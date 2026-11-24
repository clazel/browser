//! The page's JIT governor (docs/phases/jit.md item J.11): the tiering
//! counters ([`crate::tier`]), the bounds ([`crate::limits`]) and the code
//! cache ([`crate::cache`], whose budget invariant is proven) put together,
//! with the measurement counters.
//!
//! The governor is the one place that answers "this function was entered: run
//! it compiled, run it in the interpreter, or compile it first?", and, when
//! something is refused, says why ([`Fallback`]).
//!
//! # What it does and does not do
//!
//! - It is plain safe Rust over [`CodeCache`]. The bound it adds to the
//!   proven one is arithmetic on counters (`compiles_started <=
//!   max_compiles`, tracked functions `<= max_tracked_functions`), checked by
//!   the tests, not proven.
//! - **It maps nothing and enters nothing.** A region arrives from the caller
//!   (compiled, validated and mapped by someone else), and leaves in an
//!   [`Evicted`] list for the caller to unmap. Mapping and `enter` wait for
//!   `clazel-sys`'s code regions (open PR #272); the region type will be
//!   [`Mapped`](crate::cache::Mapped) around its `CodeRegion`.
//! - **It reads no clock.** Compile time is passed in by the caller.
//!
//! # Who must do what
//!
//! 1. Call [`Governor::on_entry`] at each function entry in the interpreter
//!    loop (and [`Governor::on_back_edge`] at each loop back-edge).
//! 2. On [`Dispatch::Compiled`], run the code.
//! 3. On [`Dispatch::Compile`], compile, validate, map, and then call
//!    [`Governor::submit`] (or [`Governor::compile_failed`]). Until then the
//!    function runs in the interpreter and asks for nothing more.
//! 4. Unmap everything returned in an [`Evicted`] list, and drop a refused
//!    region.

use std::collections::BTreeMap;

use crate::cache::{CodeCache, Evicted, Key, Region, Reject, Why};
use crate::limits::{Fallback, Limits, Stats};
use crate::tier::{Counters, Decision, State, Trigger, decide};

/// One function's bookkeeping.
#[derive(Clone, Copy, Debug)]
struct FnRecord {
    /// The version the counters and state are about.
    version: u32,
    counters: Counters,
    state: State,
    /// Evictions and version changes so far (the backoff exponent).
    strikes: u32,
}

/// What to do at a function entry.
#[derive(Debug)]
pub enum Dispatch<'a, R> {
    /// Run this compiled code. The borrow is of the cache's own entry, so it
    /// cannot be held across an eviction.
    Compiled(&'a R),
    /// Run the interpreter loop. `Some` says why this function is not going
    /// to be compiled; `None` means it is still warming up (or its compile is
    /// in flight).
    Interpret(Option<Fallback>),
    /// Run the interpreter loop for now, and compile this function.
    Compile(Trigger),
}

/// What to do at a back-edge (the function is not compiled).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// Keep interpreting; `Some` says why the function will not be compiled.
    Interpret(Option<Fallback>),
    /// Compile this function.
    Compile(Trigger),
}

/// A refused blob.
pub struct Refusal<R> {
    /// Why. The function stays interpreted.
    pub why: Fallback,
    /// The region that was offered, handed back to be dropped.
    pub region: R,
    /// Blobs of older versions of the same function that were dropped on the
    /// way (to be unmapped).
    pub unmap: Vec<Evicted<R>>,
}

/// What a later report reads.
#[derive(Clone, Debug)]
pub struct Report {
    /// The counters.
    pub stats: Stats,
    /// Code bytes resident now.
    pub resident_bytes: usize,
    /// Blobs resident now.
    pub resident_blobs: usize,
    /// The page's code budget.
    pub page_budget: usize,
    /// Compilations started.
    pub compiles_started: u32,
    /// Functions tracked.
    pub tracked_functions: usize,
}

/// One page's JIT policy and code cache.
pub struct Governor<R: Region> {
    cache: CodeCache<R>,
    limits: Limits,
    funcs: BTreeMap<u32, FnRecord>,
    compiles_started: u32,
    stats: Stats,
}

impl<R: Region> Governor<R> {
    /// A governor for one page with these limits.
    pub fn new(limits: Limits) -> Governor<R> {
        Governor {
            cache: CodeCache::new(limits.page_budget),
            limits,
            funcs: BTreeMap::new(),
            compiles_started: 0,
            stats: Stats::default(),
        }
    }

    /// The limits in force (the cache's budget is clamped to
    /// [`crate::cache::MAX_BUDGET`]; see [`Governor::report`]).
    pub fn limits(&self) -> &Limits {
        &self.limits
    }

    /// The counters so far.
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// The cache, read-only.
    pub fn cache(&self) -> &CodeCache<R> {
        &self.cache
    }

    /// A snapshot for the report.
    pub fn report(&self) -> Report {
        Report {
            stats: self.stats.clone(),
            resident_bytes: self.cache.used(),
            resident_blobs: self.cache.len(),
            page_budget: self.cache.budget(),
            compiles_started: self.compiles_started,
            tracked_functions: self.funcs.len(),
        }
    }

    /// The record for `func` at `version`, made if there is room. A version
    /// change starts the counters over and is a strike (inline-cache churn
    /// must not buy a page a free recompile each time).
    fn record(&mut self, func: u32, version: u32) -> Option<&mut FnRecord> {
        if !self.funcs.contains_key(&func) {
            if self.funcs.len() >= self.limits.max_tracked_functions {
                return None;
            }
            self.funcs.insert(
                func,
                FnRecord {
                    version,
                    counters: Counters::default(),
                    state: State::Interpreting,
                    strikes: 0,
                },
            );
        }
        let rec = self.funcs.get_mut(&func)?;
        if rec.version != version {
            rec.version = version;
            rec.counters = Counters::default();
            rec.state = State::Interpreting;
            rec.strikes = rec.strikes.saturating_add(1);
        }
        Some(rec)
    }

    /// Count one step of the function in the interpreter and decide.
    fn step(&mut self, func: u32, version: u32, entry: bool) -> Verdict {
        let thresholds = self.limits.thresholds;
        let quota_left = self.compiles_started < self.limits.max_compiles;
        let Some(rec) = self.record(func, version) else {
            self.stats.note_fallback(Fallback::TooManyFunctions);
            return Verdict::Interpret(Some(Fallback::TooManyFunctions));
        };
        if entry {
            rec.counters.enter();
        } else {
            rec.counters.back_edge();
        }
        // A function marked compiled that the cache no longer holds was
        // evicted without our noticing; treat it as interpreting.
        if rec.state == State::Compiled {
            rec.state = State::Interpreting;
        }
        match rec.state {
            State::Refused(why) => Verdict::Interpret(Some(why)),
            State::Compiling | State::Compiled => Verdict::Interpret(None),
            State::Interpreting => {
                match decide(&rec.counters, &thresholds, rec.strikes, rec.state) {
                    Decision::Stay => Verdict::Interpret(None),
                    Decision::Compile(trigger) => {
                        if quota_left {
                            rec.state = State::Compiling;
                            self.compiles_started = self.compiles_started.saturating_add(1);
                            Verdict::Compile(trigger)
                        } else {
                            rec.state = State::Refused(Fallback::CompileQuotaExhausted);
                            self.stats.note_fallback(Fallback::CompileQuotaExhausted);
                            Verdict::Interpret(Some(Fallback::CompileQuotaExhausted))
                        }
                    }
                }
            }
        }
    }

    /// A function was entered. See [`Dispatch`].
    pub fn on_entry(&mut self, func: u32, version: u32) -> Dispatch<'_, R> {
        let key = Key { func, version };
        if self.cache.contains(key) {
            self.stats.note_hit();
            // `lookup` borrows the cache for as long as the answer lives, so
            // the borrow is created only on the path that returns it.
            return match self.cache.lookup(key) {
                Some(region) => Dispatch::Compiled(region),
                None => Dispatch::Interpret(None),
            };
        }
        self.stats.note_miss();
        match self.step(func, version, true) {
            Verdict::Interpret(why) => Dispatch::Interpret(why),
            Verdict::Compile(t) => Dispatch::Compile(t),
        }
    }

    /// A loop back-edge was taken in the interpreter. See [`Verdict`].
    pub fn on_back_edge(&mut self, func: u32, version: u32) -> Verdict {
        self.step(func, version, false)
    }

    /// The back end refused the function: it stays interpreted at this
    /// version.
    pub fn compile_failed(&mut self, func: u32, version: u32) {
        if let Some(rec) = self.record(func, version) {
            rec.state = State::Refused(Fallback::BackEndRefused);
            self.stats.note_fallback(Fallback::BackEndRefused);
        }
    }

    /// Mark a function whose blob left the cache as interpreting again, with
    /// a strike.
    fn struck(&mut self, key: Key) {
        if let Some(rec) = self.funcs.get_mut(&key.func)
            && rec.version == key.version
            && rec.state == State::Compiled
        {
            rec.state = State::Interpreting;
            rec.counters = Counters::default();
            rec.strikes = rec.strikes.saturating_add(1);
        }
    }

    /// Account for blobs that left the cache.
    fn account(&mut self, left: &[Evicted<R>]) {
        for e in left {
            match e.why {
                Why::Capacity => {
                    self.stats.note_eviction(e.bytes);
                    self.struck(e.key);
                }
                Why::Replaced => self.stats.note_replacement(),
                Why::Invalidated => self.stats.note_invalidation(),
            }
        }
    }

    /// A compiled, validated and mapped blob for `key`, `compile_nanos` being
    /// what the caller measured for the whole compile.
    ///
    /// On `Ok` the blob is resident and the returned blobs (evicted, replaced
    /// or stale) are to be unmapped. On `Err` the function stays interpreted
    /// for the stated reason.
    pub fn submit(
        &mut self,
        key: Key,
        region: R,
        compile_nanos: u64,
    ) -> Result<Vec<Evicted<R>>, Refusal<R>> {
        let current = matches!(self.funcs.get(&key.func), Some(r) if r.version == key.version);
        if !current {
            self.stats.note_fallback(Fallback::StaleVersion);
            return Err(Refusal {
                why: Fallback::StaleVersion,
                region,
                unmap: Vec::new(),
            });
        }
        let bytes = region.byte_len();
        // Older versions of this function can never be entered again.
        let mut unmap = self.cache.invalidate_but(key.func, Some(key.version));
        match self
            .cache
            .insert(key, region, self.limits.max_function_bytes)
        {
            Ok(left) => {
                unmap.extend(left);
                self.account(&unmap);
                self.stats.note_compile(bytes, compile_nanos);
                self.stats.note_resident(self.cache.used());
                if let Some(rec) = self.funcs.get_mut(&key.func) {
                    rec.state = State::Compiled;
                }
                Ok(unmap)
            }
            Err(rej) => {
                let why = match rej.why {
                    Reject::Empty => Fallback::EmptyBlob,
                    Reject::FunctionTooLarge => Fallback::FunctionTooLarge,
                    Reject::ExceedsBudget => Fallback::ExceedsPageBudget,
                };
                self.account(&unmap);
                self.stats.note_compile(0, compile_nanos);
                self.stats.note_fallback(why);
                if let Some(rec) = self.funcs.get_mut(&key.func) {
                    rec.state = State::Refused(why);
                }
                Err(Refusal {
                    why,
                    region: rej.region,
                    unmap,
                })
            }
        }
    }

    /// The function's bytecode changed: drop all its blobs (returned, to be
    /// unmapped) and start its counters over, with a strike.
    pub fn invalidate_function(&mut self, func: u32) -> Vec<Evicted<R>> {
        let left = self.cache.invalidate(func);
        self.account(&left);
        if let Some(rec) = self.funcs.get_mut(&func) {
            rec.state = State::Interpreting;
            rec.counters = Counters::default();
            rec.strikes = rec.strikes.saturating_add(1);
        }
        left
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache::Mapped;
    use crate::tier::Thresholds;
    use std::cell::Cell;
    use std::rc::Rc;

    /// A handle that counts how many are alive.
    struct Token(Rc<Cell<usize>>);

    impl Token {
        fn new(live: &Rc<Cell<usize>>) -> Token {
            live.set(live.get().saturating_add(1));
            Token(Rc::clone(live))
        }
    }

    impl Drop for Token {
        fn drop(&mut self) {
            self.0.set(self.0.get().saturating_sub(1));
        }
    }

    type Blob = Mapped<Token>;
    type Live = Rc<Cell<usize>>;

    fn blob(live: &Live, len: usize) -> Blob {
        Mapped {
            handle: Token::new(live),
            len,
        }
    }

    /// The `Ok` of a submit.
    fn ok(r: Result<Vec<Evicted<Blob>>, Refusal<Blob>>) -> Vec<Evicted<Blob>> {
        match r {
            Ok(v) => v,
            Err(r) => unreachable!("refused: {:?}", r.why),
        }
    }

    /// The `Err` of a submit.
    fn refused(r: Result<Vec<Evicted<Blob>>, Refusal<Blob>>) -> Refusal<Blob> {
        match r {
            Ok(_) => unreachable!("expected a refusal"),
            Err(r) => r,
        }
    }

    fn key(func: u32, version: u32) -> Key {
        Key { func, version }
    }

    fn small_limits() -> Limits {
        Limits {
            max_function_bytes: 400,
            page_budget: 1000,
            max_compiles: 50,
            max_tracked_functions: 20,
            thresholds: Thresholds {
                entries: 3,
                back_edges: 10,
            },
        }
    }

    /// Drive `func` until it asks to be compiled.
    fn warm(g: &mut Governor<Blob>, func: u32, version: u32) -> Trigger {
        for _ in 0..10_000 {
            match g.on_entry(func, version) {
                Dispatch::Compile(t) => return t,
                Dispatch::Compiled(_) => unreachable!("already compiled"),
                Dispatch::Interpret(Some(why)) => unreachable!("refused: {why:?}"),
                Dispatch::Interpret(None) => {}
            }
        }
        unreachable!("never asked to compile")
    }

    fn resident_sum(g: &Governor<Blob>) -> usize {
        let mut sum = 0usize;
        let mut i = 0usize;
        while let Some((_, n)) = g.cache().entry_at(i) {
            sum = sum.saturating_add(n);
            i = i.saturating_add(1);
        }
        sum
    }

    #[test]
    fn warm_up_then_compile_then_hit() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        for _ in 0..2 {
            assert!(matches!(g.on_entry(1, 0), Dispatch::Interpret(None)));
        }
        assert!(matches!(
            g.on_entry(1, 0),
            Dispatch::Compile(Trigger::Entries)
        ));
        // The compile is in flight: no second request.
        assert!(matches!(g.on_entry(1, 0), Dispatch::Interpret(None)));
        let left = ok(g.submit(key(1, 0), blob(&live, 100), 1234));
        assert!(left.is_empty());
        assert!(matches!(g.on_entry(1, 0), Dispatch::Compiled(r) if r.len == 100));
        let s = g.stats();
        assert_eq!(
            (s.compiles, s.compile_nanos, s.code_bytes_emitted),
            (1, 1234, 100)
        );
        assert_eq!((s.hits, s.misses), (1, 4));
        assert_eq!(g.report().resident_bytes, 100);
    }

    #[test]
    fn a_loop_entered_once_compiles() {
        let mut g: Governor<Blob> = Governor::new(small_limits());
        assert!(matches!(g.on_entry(7, 0), Dispatch::Interpret(None)));
        for _ in 0..9 {
            assert_eq!(g.on_back_edge(7, 0), Verdict::Interpret(None));
        }
        assert_eq!(g.on_back_edge(7, 0), Verdict::Compile(Trigger::BackEdges));
    }

    #[test]
    fn oversize_function_falls_back_with_a_reason_and_stays_out() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        warm(&mut g, 1, 0);
        let r = refused(g.submit(key(1, 0), blob(&live, 401), 5));
        assert_eq!(r.why, Fallback::FunctionTooLarge);
        assert_eq!(r.region.len, 401);
        drop(r);
        assert_eq!(live.get(), 0, "a refused region is handed back, not kept");
        assert_eq!(g.report().resident_bytes, 0);
        // Never asked again at this version.
        for _ in 0..100 {
            assert!(matches!(
                g.on_entry(1, 0),
                Dispatch::Interpret(Some(Fallback::FunctionTooLarge))
            ));
        }
        assert_eq!(g.stats().fallback_count(Fallback::FunctionTooLarge), 1);
        // A new version is a new chance.
        assert!(matches!(g.on_entry(1, 1), Dispatch::Interpret(None)));
    }

    #[test]
    fn blob_over_the_page_budget_is_refused() {
        let live = Live::default();
        let mut g = Governor::new(Limits {
            max_function_bytes: 5000,
            ..small_limits()
        });
        warm(&mut g, 1, 0);
        let r = refused(g.submit(key(1, 0), blob(&live, 1001), 0));
        assert_eq!(r.why, Fallback::ExceedsPageBudget);
        assert!(r.why.reason().contains("budget"));
    }

    #[test]
    fn empty_blob_and_failed_compile_are_refused() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        warm(&mut g, 1, 0);
        let r = refused(g.submit(key(1, 0), blob(&live, 0), 0));
        assert_eq!(r.why, Fallback::EmptyBlob);
        warm(&mut g, 2, 0);
        g.compile_failed(2, 0);
        assert!(matches!(
            g.on_entry(2, 0),
            Dispatch::Interpret(Some(Fallback::BackEndRefused))
        ));
    }

    #[test]
    fn eviction_makes_the_function_interpret_and_earn_its_blob_again() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        for f in 1..=2u32 {
            warm(&mut g, f, 0);
            drop(ok(g.submit(key(f, 0), blob(&live, 400), 1)));
        }
        // 800 of 1000 used. Function 1 is the least recently used.
        warm(&mut g, 3, 0);
        let left = ok(g.submit(key(3, 0), blob(&live, 400), 1));
        assert_eq!(left.len(), 1);
        let first = left.first().map(|e| (e.key, e.why));
        assert_eq!(first, Some((key(1, 0), Why::Capacity)));
        drop(left);
        assert_eq!(live.get(), 2);
        assert!(g.report().resident_bytes <= 1000);
        assert_eq!(g.stats().evictions, 1);
        assert_eq!(g.stats().evicted_bytes, 400);
        // Function 1 is not entered compiled any more. It had a strike, so
        // its threshold is 6 entries, not 3.
        let mut entries = 0u32;
        loop {
            entries = entries.saturating_add(1);
            match g.on_entry(1, 0) {
                Dispatch::Compile(_) => break,
                Dispatch::Interpret(None) => {}
                _ => unreachable!("unexpected dispatch"),
            }
            assert!(entries < 100);
        }
        assert_eq!(entries, 6);
    }

    #[test]
    fn a_hit_keeps_a_blob_resident_over_an_older_one() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        for f in 1..=2u32 {
            warm(&mut g, f, 0);
            drop(ok(g.submit(key(f, 0), blob(&live, 400), 1)));
        }
        // Touch function 1: function 2 becomes the least recently used.
        assert!(matches!(g.on_entry(1, 0), Dispatch::Compiled(_)));
        warm(&mut g, 3, 0);
        let left = ok(g.submit(key(3, 0), blob(&live, 400), 1));
        assert_eq!(left.first().map(|e| e.key.func), Some(2));
        assert!(matches!(g.on_entry(1, 0), Dispatch::Compiled(_)));
        assert!(matches!(g.on_entry(2, 0), Dispatch::Interpret(_)));
    }

    #[test]
    fn a_new_version_drops_the_old_blob() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        warm(&mut g, 1, 0);
        drop(ok(g.submit(key(1, 0), blob(&live, 100), 1)));
        warm(&mut g, 1, 1);
        let left = ok(g.submit(key(1, 1), blob(&live, 120), 1));
        assert_eq!(left.len(), 1);
        assert_eq!(
            left.first().map(|e| (e.key.version, e.why)),
            Some((0, Why::Invalidated))
        );
        drop(left);
        assert_eq!(live.get(), 1);
        assert_eq!(g.report().resident_bytes, 120);
        assert_eq!(g.stats().invalidations, 1);
        assert!(matches!(g.on_entry(1, 1), Dispatch::Compiled(_)));
    }

    #[test]
    fn a_blob_for_a_version_that_moved_on_is_refused() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        warm(&mut g, 1, 0);
        // Version 1 is entered while version 0 compiles.
        let _ = g.on_entry(1, 1);
        let r = refused(g.submit(key(1, 0), blob(&live, 100), 1));
        assert_eq!(r.why, Fallback::StaleVersion);
        assert_eq!(g.report().resident_bytes, 0);
    }

    #[test]
    fn invalidate_function_drops_all_its_blobs() {
        let live = Live::default();
        let mut g = Governor::new(small_limits());
        warm(&mut g, 1, 0);
        drop(ok(g.submit(key(1, 0), blob(&live, 100), 1)));
        let left = g.invalidate_function(1);
        assert_eq!(left.len(), 1);
        drop(left);
        assert_eq!(live.get(), 0);
        assert_eq!(g.report().resident_bytes, 0);
        assert!(matches!(g.on_entry(1, 0), Dispatch::Interpret(None)));
    }

    #[test]
    fn compile_quota_stops_new_compiles() {
        let live = Live::default();
        let mut g = Governor::new(Limits {
            max_compiles: 3,
            ..small_limits()
        });
        for f in 0..3u32 {
            warm(&mut g, f, 0);
            drop(ok(g.submit(key(f, 0), blob(&live, 10), 1)));
        }
        for _ in 0..2 {
            assert!(matches!(g.on_entry(9, 0), Dispatch::Interpret(None)));
        }
        assert!(matches!(
            g.on_entry(9, 0),
            Dispatch::Interpret(Some(Fallback::CompileQuotaExhausted))
        ));
        assert_eq!(g.report().compiles_started, 3);
    }

    #[test]
    fn tracked_functions_are_bounded() {
        let mut g: Governor<Blob> = Governor::new(small_limits());
        for f in 0..1000u32 {
            let _ = g.on_entry(f, 0);
        }
        assert_eq!(g.report().tracked_functions, 20);
        assert!(matches!(
            g.on_entry(999, 0),
            Dispatch::Interpret(Some(Fallback::TooManyFunctions))
        ));
        assert_eq!(g.stats().fallback_count(Fallback::TooManyFunctions), 981);
    }

    /// A xorshift generator, so the flood is the same on every run.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0.wrapping_shl(13);
            self.0 ^= self.0.wrapping_shr(7);
            self.0 ^= self.0.wrapping_shl(17);
            self.0
        }

        /// A number below `n` (`n > 0`).
        fn below(&mut self, n: u64) -> u64 {
            self.next().checked_rem(n).unwrap_or(0)
        }
    }

    /// A flood of compile requests, with sizes from nothing to far over every
    /// cap, never lets the resident code pass the budget, and never leaks a
    /// region: what is alive is exactly what is resident.
    #[test]
    fn a_flood_of_compile_requests_stays_within_the_budget() {
        let rounds: u32 = if cfg!(miri) { 300 } else { 60_000 };
        let live = Live::default();
        let limits = Limits {
            max_function_bytes: 3000,
            page_budget: 20_000,
            max_compiles: u32::MAX,
            max_tracked_functions: 500,
            thresholds: Thresholds {
                entries: 2,
                back_edges: 5,
            },
        };
        let mut g: Governor<Blob> = Governor::new(limits);
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        let mut version = [0u32; 600];
        for round in 0..rounds {
            let func = rng.below(600) as u32;
            let churn = rng.below(17) == 0;
            let v = match version.get_mut(func as usize) {
                Some(v) => {
                    // Inline-cache churn: now and then the function changes.
                    if churn {
                        *v = v.saturating_add(1);
                    }
                    *v
                }
                None => 0,
            };
            let verdict = if rng.below(4) == 0 {
                g.on_back_edge(func, v)
            } else {
                match g.on_entry(func, v) {
                    Dispatch::Compile(t) => Verdict::Compile(t),
                    Dispatch::Compiled(_) => Verdict::Interpret(None),
                    Dispatch::Interpret(w) => Verdict::Interpret(w),
                }
            };
            if let Verdict::Compile(_) = verdict {
                let len = match rng.below(10) {
                    0 => 0,
                    1 => 1_000_000,
                    2 => 20_001,
                    3 => 3001,
                    _ => (rng.below(3000) as usize).saturating_add(1),
                };
                if rng.below(12) == 0 {
                    g.compile_failed(func, v);
                } else {
                    match g.submit(key(func, v), blob(&live, len), 10) {
                        Ok(left) => drop(left),
                        Err(r) => {
                            assert!(!r.why.reason().is_empty());
                            drop(r);
                        }
                    }
                }
            }
            if round % 97 == 0 {
                drop(g.invalidate_function(rng.below(600) as u32));
            }
            // The invariants, after every request.
            let used = g.cache().used();
            assert!(used <= 20_000, "resident code {used} passed the budget");
            assert_eq!(used, resident_sum(&g));
            assert_eq!(
                live.get(),
                g.cache().len(),
                "a region is alive but not resident"
            );
            assert!(g.report().tracked_functions <= 500);
        }
        let s = g.stats();
        assert!(s.peak_resident_bytes <= 20_000);
        assert!(
            s.evictions > 0 || rounds < 1000,
            "the flood should have forced evictions"
        );
        assert!(s.total_fallbacks() > 0);
        assert!(s.compiles > 0);
    }

    /// A page that cycles through more equally hot functions than fit does
    /// not compile for ever: the backoff makes each round cost more.
    #[test]
    fn thrashing_is_damped_by_backoff() {
        let live = Live::default();
        let limits = Limits {
            max_function_bytes: 1000,
            page_budget: 2000,
            max_compiles: u32::MAX,
            max_tracked_functions: 100,
            thresholds: Thresholds {
                entries: 2,
                back_edges: 1000,
            },
        };
        let mut g: Governor<Blob> = Governor::new(limits);
        // Three functions of 1000 bytes each, two fit.
        let steps: u32 = if cfg!(miri) { 2_000 } else { 200_000 };
        let mut compiles_early = 0u64;
        for step in 0..steps {
            let func = step % 3;
            if let Dispatch::Compile(_) = g.on_entry(func, 0) {
                drop(ok(g.submit(key(func, 0), blob(&live, 1000), 1)));
            }
            if step == steps / 10 {
                compiles_early = g.stats().compiles;
            }
        }
        let total = g.stats().compiles;
        assert!(
            total < u64::from(steps) / 20,
            "{total} compiles in {steps} steps"
        );
        // Compiles slow down: the last nine tenths add few compared with the
        // first tenth.
        let late = total.saturating_sub(compiles_early);
        assert!(late < compiles_early.saturating_mul(4).saturating_add(10));
        assert!(g.cache().used() <= 2000);
    }
}
