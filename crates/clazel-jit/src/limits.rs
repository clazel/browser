//! The hostile-page bounds and the measurement counters of the JIT's code
//! cache (docs/phases/jit.md item J.11).
//!
//! - [`Limits`]: what one page may use. Every limit has a default and a stated
//!   reason, and every way of exceeding one ends in the same place: the
//!   function stays in the interpreter loop, for a stated [`Fallback`].
//! - [`Stats`]: the counters a later report reads (compile time, code bytes,
//!   evictions, fallbacks). **No clock is read here**: the caller measures a
//!   compile with its own clock and passes the nanoseconds in, so nothing in
//!   this crate depends on wall-clock time (and nothing in a proof could).

use crate::tier::Thresholds;

/// The largest blob the A64 back end emits (`a64::cfemit::MAX_WORDS` words of
/// four bytes, 512 KiB). The x86-64 emitter's own cap is the same size
/// (`cftemplates::max_size`).
pub const BACKEND_MAX_BYTES: usize = 0x8_0000;

/// What one page's code cache may use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// The most bytes of compiled code one function may take. A blob above
    /// this is refused ([`Fallback::FunctionTooLarge`]) and its function
    /// stays interpreted. Never above [`BACKEND_MAX_BYTES`] in practice, since
    /// the back ends refuse larger bodies themselves.
    pub max_function_bytes: usize,
    /// The most bytes of compiled code the page may hold at once (J.11:
    /// "bound the code bytes per renderer"). Past it the least recently used
    /// blobs are evicted. Clamped to [`crate::cache::MAX_BUDGET`].
    pub page_budget: usize,
    /// The most compilations the page may start over its lifetime. Eviction
    /// and recompilation could otherwise burn CPU for ever on a page that
    /// cycles through more hot functions than fit. Past it nothing new
    /// compiles ([`Fallback::CompileQuotaExhausted`]).
    pub max_compiles: u32,
    /// The most functions whose counters are tracked. Past it a new function
    /// is simply interpreted ([`Fallback::TooManyFunctions`]), so the
    /// bookkeeping is bounded whatever the page defines.
    pub max_tracked_functions: usize,
    /// When to compile (jit.md J.10).
    pub thresholds: Thresholds,
}

impl Default for Limits {
    /// Starting values, to be set from J.11's measurements: 512 KiB per
    /// function (the back ends' own cap), 8 MiB per page, 4096 compilations
    /// and 65,536 tracked functions.
    fn default() -> Limits {
        Limits {
            max_function_bytes: BACKEND_MAX_BYTES,
            page_budget: 8 * 1024 * 1024,
            max_compiles: 4096,
            max_tracked_functions: 65_536,
            thresholds: Thresholds::default(),
        }
    }
}

/// Why a function runs in the interpreter loop instead of compiled. The
/// interpreter is complete, so every one of these is a slower run, never a
/// wrong one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fallback {
    /// The compiled blob is longer than [`Limits::max_function_bytes`].
    FunctionTooLarge,
    /// The compiled blob is longer than the whole page budget.
    ExceedsPageBudget,
    /// The back end produced no code.
    EmptyBlob,
    /// The page has started [`Limits::max_compiles`] compilations.
    CompileQuotaExhausted,
    /// The page already has [`Limits::max_tracked_functions`] functions.
    TooManyFunctions,
    /// The back end refused the function (a construct it has no template for,
    /// or a body over its own size cap).
    BackEndRefused,
    /// The function changed (its version moved on) while its blob was being
    /// compiled, so the blob is for code that no longer exists.
    StaleVersion,
}

impl Fallback {
    /// The number of reasons.
    pub const COUNT: usize = 7;

    /// Every reason, in [`Fallback::index`] order.
    pub const ALL: [Fallback; Fallback::COUNT] = [
        Fallback::FunctionTooLarge,
        Fallback::ExceedsPageBudget,
        Fallback::EmptyBlob,
        Fallback::CompileQuotaExhausted,
        Fallback::TooManyFunctions,
        Fallback::BackEndRefused,
        Fallback::StaleVersion,
    ];

    /// The position of this reason in [`Fallback::ALL`] and in
    /// [`Stats::fallbacks`].
    pub fn index(self) -> usize {
        match self {
            Fallback::FunctionTooLarge => 0,
            Fallback::ExceedsPageBudget => 1,
            Fallback::EmptyBlob => 2,
            Fallback::CompileQuotaExhausted => 3,
            Fallback::TooManyFunctions => 4,
            Fallback::BackEndRefused => 5,
            Fallback::StaleVersion => 6,
        }
    }

    /// The stated reason, for a report or a console line.
    pub fn reason(self) -> &'static str {
        match self {
            Fallback::FunctionTooLarge => "compiled code exceeds the per-function size cap",
            Fallback::ExceedsPageBudget => "compiled code exceeds the page's code budget",
            Fallback::EmptyBlob => "the back end produced no code",
            Fallback::CompileQuotaExhausted => "the page's compilation quota is used up",
            Fallback::TooManyFunctions => "too many functions to track",
            Fallback::BackEndRefused => "the back end has no translation for the function",
            Fallback::StaleVersion => "the function changed during compilation",
        }
    }
}

/// `*counter + by`, stopping at the maximum.
fn bump(counter: &mut u64, by: u64) {
    *counter = counter.saturating_add(by);
}

/// The measurement counters (J.11, "measurement"). All saturate, so a hostile
/// page cannot make them wrap.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Compilations whose blob reached the cache or was refused by it.
    pub compiles: u64,
    /// Nanoseconds spent compiling, as the caller measured them.
    pub compile_nanos: u64,
    /// Bytes of code emitted over the page's life (accepted blobs only).
    pub code_bytes_emitted: u64,
    /// The most code bytes resident at once.
    pub peak_resident_bytes: u64,
    /// Blobs evicted for capacity.
    pub evictions: u64,
    /// Bytes of code evicted for capacity.
    pub evicted_bytes: u64,
    /// Blobs replaced by a new blob for the same function version.
    pub replacements: u64,
    /// Blobs dropped because their function changed.
    pub invalidations: u64,
    /// Entries that found compiled code.
    pub hits: u64,
    /// Entries that did not (they ran in the interpreter).
    pub misses: u64,
    /// Refusals, by [`Fallback::index`].
    pub fallbacks: [u64; Fallback::COUNT],
}

impl Stats {
    /// How many times this reason was given.
    pub fn fallback_count(&self, why: Fallback) -> u64 {
        self.fallbacks.get(why.index()).copied().unwrap_or(0)
    }

    /// The total number of refusals.
    pub fn total_fallbacks(&self) -> u64 {
        self.fallbacks
            .iter()
            .fold(0u64, |a, b| a.saturating_add(*b))
    }

    pub(crate) fn note_fallback(&mut self, why: Fallback) {
        if let Some(c) = self.fallbacks.get_mut(why.index()) {
            bump(c, 1);
        }
    }

    pub(crate) fn note_compile(&mut self, bytes: usize, nanos: u64) {
        bump(&mut self.compiles, 1);
        bump(&mut self.compile_nanos, nanos);
        bump(&mut self.code_bytes_emitted, bytes as u64);
    }

    pub(crate) fn note_eviction(&mut self, bytes: usize) {
        bump(&mut self.evictions, 1);
        bump(&mut self.evicted_bytes, bytes as u64);
    }

    pub(crate) fn note_replacement(&mut self) {
        bump(&mut self.replacements, 1);
    }

    pub(crate) fn note_invalidation(&mut self) {
        bump(&mut self.invalidations, 1);
    }

    pub(crate) fn note_hit(&mut self) {
        bump(&mut self.hits, 1);
    }

    pub(crate) fn note_miss(&mut self) {
        bump(&mut self.misses, 1);
    }

    pub(crate) fn note_resident(&mut self, resident: usize) {
        self.peak_resident_bytes = self.peak_resident_bytes.max(resident as u64);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fallback_index_matches_all() {
        for (i, f) in Fallback::ALL.iter().enumerate() {
            assert_eq!(f.index(), i);
            assert!(!f.reason().is_empty());
        }
        assert_eq!(Fallback::ALL.len(), Fallback::COUNT);
    }

    #[test]
    fn counters_saturate() {
        let mut s = Stats {
            compile_nanos: u64::MAX - 1,
            ..Stats::default()
        };
        s.note_compile(10, 5);
        assert_eq!(s.compile_nanos, u64::MAX);
        s.note_fallback(Fallback::EmptyBlob);
        assert_eq!(s.fallback_count(Fallback::EmptyBlob), 1);
        assert_eq!(s.total_fallbacks(), 1);
    }

    #[test]
    fn default_function_cap_is_the_backend_cap() {
        assert_eq!(
            Limits::default().max_function_bytes,
            4 * crate::a64::cfemit::MAX_WORDS
        );
        assert_eq!(BACKEND_MAX_BYTES, 4 * crate::a64::cfemit::MAX_WORDS);
    }
}
