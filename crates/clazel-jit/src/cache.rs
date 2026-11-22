//! The code cache's data structure (docs/phases/jit.md item J.11, "bound the
//! code bytes per renderer").
//!
//! A [`CodeCache`] holds the compiled blobs of one page, one per
//! [`Key`] (bytecode function id and version), under a fixed byte budget.
//! When a new blob does not fit, the least recently used blobs are evicted
//! until it does.
//!
//! # The statement (written first, CLAUDE.md rule 3)
//!
//! [`CodeCache::inv`] is the invariant, and every public operation takes it
//! and returns it ([`CodeCache::insert`], [`CodeCache::lookup`],
//! [`CodeCache::invalidate`], [`CodeCache::new`]):
//!
//! 1. **The bound.** `used <= budget <= MAX_BUDGET`, and `used` is exactly
//!    the sum of the byte lengths of the resident entries (`total`). So the
//!    code bytes of the resident blobs never exceed the budget, at any
//!    point between two operations, whatever sequence of requests came.
//! 2. **The lengths are the regions'.** Each entry's `bytes` equals its
//!    region's own length ([`Region::byte_len`]), so the sum in 1 is the sum
//!    of what is mapped, not of what a caller claimed.
//! 3. **One blob per key.** No two resident entries have the same key, so a
//!    lookup finds the only blob for a function version.
//!
//! And the three consequences the J.11 text asks for:
//!
//! - **An evicted entry is never entered.** `lookup` is the only way to get
//!   at a resident region, and it returns a borrow of the cache's own entry
//!   (so the borrow cannot outlive the next `insert` or `invalidate`).
//!   Eviction moves the region out of the cache and into the returned
//!   [`Evicted`] list, for the caller to unmap, and the postcondition of
//!   `insert` says no resident key is the key of an evicted blob (other than
//!   the key just inserted). After an eviction, `lookup` answers `None` for
//!   that key, so the caller runs the interpreter ([`CodeCache::lookup`]'s
//!   postcondition: `Some` exactly when the key is resident).
//! - **A rejected insert changes nothing** and hands the region back, with
//!   the reason ([`Reject`]).
//! - **A function's blobs can all be dropped** ([`CodeCache::invalidate`]).
//!
//! # What this module is and is not
//!
//! Pure safe Rust, proven in Verus (no axiom, no assumption). It does not map
//! or enter anything. The real region type will be `clazel-sys`'s
//! `CodeRegion` (open PR #272, jit.md J.7); until it merges nothing here
//! depends on it. The cache is generic over [`Region`], whose only job is to
//! state a length; [`Mapped`] pairs any handle with its length, which is how
//! `CodeRegion` will fill it. The cache never reads or writes a region's
//! bytes, so it cannot make anything executable.
//!
//! The eviction *order* (least recently used first) is a policy, not part of
//! the proof: the vector is kept in recency order, with the front the least
//! recently used, and the proof does not depend on the order.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The largest budget a cache accepts (1 GiB). A larger request is clamped to
/// it, so that `used + bytes` cannot overflow a `usize` (at least 32 bits).
pub const MAX_BUDGET: usize = 0x4000_0000;

/// What the cache needs to know of a compiled blob's memory: its length.
pub trait Region {
    /// The blob's length in bytes.
    spec fn spec_len(&self) -> nat;

    /// The same, as a number.
    fn byte_len(&self) -> (n: usize)
        ensures
            n as nat == self.spec_len(),
    ;
}

/// Any handle (the future `clazel-sys` `CodeRegion`, a test stand-in) with the
/// length of the code in it.
pub struct Mapped<H> {
    /// The handle. Dropping it releases the memory.
    pub handle: H,
    /// The length of the code, in bytes.
    pub len: usize,
}

impl<H> Region for Mapped<H> {
    open spec fn spec_len(&self) -> nat {
        self.len as nat
    }

    fn byte_len(&self) -> (n: usize) {
        self.len
    }
}

/// A function version: the bytecode function's id and the version of its
/// bytecode (bumped when the function's code or its inline-cache shape
/// assumptions change).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Key {
    /// The bytecode function id.
    pub func: u32,
    /// The version of that function's code.
    pub version: u32,
}

/// One resident blob.
pub struct Entry<R> {
    /// The function version it was compiled from.
    pub key: Key,
    /// The memory holding it.
    pub region: R,
    /// Its length, equal to the region's own (invariant 2).
    pub bytes: usize,
}

/// Why a blob left the cache.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// Evicted to make room for another blob.
    Capacity,
    /// Replaced by a new blob for the same key.
    Replaced,
    /// Dropped by [`CodeCache::invalidate`].
    Invalidated,
}

/// A blob that left the cache, handed back to be unmapped.
pub struct Evicted<R> {
    /// The function version it was compiled from.
    pub key: Key,
    /// The memory. The cache no longer refers to it.
    pub region: R,
    /// Its length.
    pub bytes: usize,
    /// Why it left.
    pub why: Why,
}

/// Why an insert was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reject {
    /// The blob is empty.
    Empty,
    /// The blob is longer than the per-function cap given to `insert`.
    FunctionTooLarge,
    /// The blob is longer than the whole budget.
    ExceedsBudget,
}

/// A refused insert: the reason, and the region handed back.
pub struct Rejected<R> {
    /// Why.
    pub why: Reject,
    /// The region that was offered.
    pub region: R,
}

/// The sum of the byte lengths of the entries.
pub open spec fn total<R>(s: Seq<Entry<R>>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0].bytes as nat + total(s.subrange(1, s.len() as int))
    }
}

/// Appending an entry adds its length.
pub proof fn lemma_total_push<R>(s: Seq<Entry<R>>, e: Entry<R>)
    ensures
        total(s.push(e)) == total(s) + e.bytes as nat,
    decreases s.len(),
{
    reveal_with_fuel(total, 2);
    if s.len() == 0 {
        assert(s.push(e).subrange(1, 1) =~= Seq::<Entry<R>>::empty());
    } else {
        let t = s.subrange(1, s.len() as int);
        lemma_total_push(t, e);
        assert(s.push(e).subrange(1, s.len() as int + 1) =~= t.push(e));
        assert(s.push(e)[0] == s[0]);
    }
}

/// Removing an entry subtracts its length.
pub proof fn lemma_total_remove<R>(s: Seq<Entry<R>>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        total(s) == total(s.remove(i)) + s[i].bytes as nat,
    decreases s.len(),
{
    reveal_with_fuel(total, 2);
    s.remove_ensures(i);
    if i == 0 {
        assert(s.remove(0) =~= s.subrange(1, s.len() as int));
    } else {
        let t = s.subrange(1, s.len() as int);
        lemma_total_remove(t, i - 1);
        t.remove_ensures(i - 1);
        assert(s.remove(i).subrange(1, s.len() as int - 1) =~= t.remove(i - 1));
        assert(s.remove(i)[0] == s[0]);
        assert(t[i - 1] == s[i]);
    }
}

/// Whether [`CodeCache::invalidate_but`] drops a blob with this key.
pub open spec fn drops(k: Key, func: u32, keep: Option<u32>) -> bool {
    k.func == func && match keep {
        None => true,
        Some(v) => k.version != v,
    }
}

/// `a + b`, when it does not overflow.
fn add_u(a: usize, b: usize) -> (r: usize)
    requires
        a + b <= usize::MAX,
    ensures
        r == a + b,
{
    a.saturating_add(b)
}

/// `a - b`, when it does not underflow.
fn sub_u(a: usize, b: usize) -> (r: usize)
    requires
        b <= a,
    ensures
        r == a - b,
{
    a.saturating_sub(b)
}

/// The code cache of one page. See the module header for the invariant.
pub struct CodeCache<R: Region> {
    /// Resident entries, least recently used first.
    entries: Vec<Entry<R>>,
    /// The sum of the entries' lengths.
    used: usize,
    /// The byte budget.
    budget: usize,
}

impl<R: Region> CodeCache<R> {
    /// The invariant (module header, 1 to 3).
    pub closed spec fn inv(&self) -> bool {
        &&& self.budget <= MAX_BUDGET
        &&& self.used <= self.budget
        &&& self.used as nat == total(self.entries@)
        &&& forall|i: int|
            0 <= i < self.entries@.len() ==> (#[trigger] self.entries@[i]).bytes as nat
                == self.entries@[i].region.spec_len()
        &&& forall|i: int, j: int|
            0 <= i < j < self.entries@.len() ==> (#[trigger] self.entries@[i]).key
                != (#[trigger] self.entries@[j]).key
    }

    /// The budget, as a spec.
    pub closed spec fn spec_budget(&self) -> nat {
        self.budget as nat
    }

    /// The bytes in use, as a spec.
    pub closed spec fn spec_used(&self) -> nat {
        self.used as nat
    }

    /// The resident entries, least recently used first.
    pub closed spec fn spec_entries(&self) -> Seq<Entry<R>> {
        self.entries@
    }

    /// Some resident entry has this key.
    pub closed spec fn has(&self, k: Key) -> bool {
        exists|i: int| 0 <= i < self.entries@.len() && (#[trigger] self.entries@[i]).key == k
    }

    /// **The budget invariant, as a theorem**: under `inv`, the bytes in use
    /// never exceed the budget, which never exceeds [`MAX_BUDGET`].
    pub proof fn lemma_within_budget(&self)
        requires
            self.inv(),
        ensures
            self.spec_used() <= self.spec_budget(),
            self.spec_budget() <= MAX_BUDGET as nat,
            self.spec_used() == total(self.spec_entries()),
    {
    }

    /// An empty cache. A budget above [`MAX_BUDGET`] is clamped to it.
    pub fn new(budget: usize) -> (c: Self)
        ensures
            c.inv(),
            c.spec_used() == 0,
            c.spec_budget() == if budget <= MAX_BUDGET {
                budget as nat
            } else {
                MAX_BUDGET as nat
            },
            forall|k: Key| !c.has(k),
    {
        let b = if budget < MAX_BUDGET {
            budget
        } else {
            MAX_BUDGET
        };
        let c = CodeCache { entries: Vec::new(), used: 0, budget: b };
        proof {
            assert(c.entries@ =~= Seq::<Entry<R>>::empty());
        }
        c
    }

    /// The bytes in use.
    pub fn used(&self) -> (n: usize)
        ensures
            n as nat == self.spec_used(),
    {
        self.used
    }

    /// The budget.
    pub fn budget(&self) -> (n: usize)
        ensures
            n as nat == self.spec_budget(),
    {
        self.budget
    }

    /// The number of resident entries.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self.spec_entries().len(),
    {
        self.entries.len()
    }

    /// Whether the cache holds nothing.
    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self.spec_entries().len() == 0),
    {
        self.entries.len() == 0
    }

    /// Whether a blob for this key is resident. Does not change the order.
    pub fn contains(&self, key: Key) -> (b: bool)
        ensures
            b == self.has(key),
    {
        self.find(key).is_some()
    }

    /// The index of the entry with this key.
    fn find(&self, key: Key) -> (r: Option<usize>)
        ensures
            match r {
                Some(i) => i < self.entries@.len() && self.entries@[i as int].key == key,
                None => !self.has(key),
            },
    {
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries@.len(),
                forall|j: int| 0 <= j < i ==> (#[trigger] self.entries@[j]).key != key,
            decreases self.entries@.len() - i,
        {
            let hit = match self.entries.as_slice().get(i) {
                Some(e) => e.key.func == key.func && e.key.version == key.version,
                None => {
                    proof {
                        assert(false);
                    }
                    false
                },
            };
            if hit {
                return Some(i);
            }
            i = add_u(i, 1);
        }
        None
    }

    /// Remove entry `i`, returning it. The bytes in use drop by its length.
    fn remove_at(&mut self, i: usize) -> (e: Entry<R>)
        requires
            old(self).inv(),
            i < old(self).entries@.len(),
        ensures
            final(self).inv(),
            e == old(self).entries@[i as int],
            final(self).entries@ == old(self).entries@.remove(i as int),
            final(self).budget == old(self).budget,
            final(self).used as int == old(self).used as int - e.bytes as int,
            e.bytes <= old(self).used,
    {
        proof {
            lemma_total_remove(self.entries@, i as int);
        }
        let ghost before = self.entries@;
        let e = self.entries.remove(i);
        proof {
            before.remove_ensures(i as int);
        }
        self.used = sub_u(self.used, e.bytes);
        proof {
            assert forall|k: int| 0 <= k < self.entries@.len() implies (
            #[trigger] self.entries@[k]).bytes as nat == self.entries@[k].region.spec_len() by {
                if k < i as int {
                    assert(self.entries@[k] == before[k]);
                } else {
                    assert(self.entries@[k] == before[k + 1]);
                }
            }
            assert forall|a: int, b: int| 0 <= a < b < self.entries@.len() implies (
            #[trigger] self.entries@[a]).key != (#[trigger] self.entries@[b]).key by {
                let ia = if a < i as int {
                    a
                } else {
                    a + 1
                };
                let ib = if b < i as int {
                    b
                } else {
                    b + 1
                };
                assert(self.entries@[a] == before[ia]);
                assert(self.entries@[b] == before[ib]);
                assert(ia < ib);
            }
        }
        e
    }

    /// Append `e`. The caller shows the bytes fit and the key is new.
    fn push_back(&mut self, e: Entry<R>)
        requires
            old(self).inv(),
            e.bytes as nat == e.region.spec_len(),
            old(self).used + e.bytes <= old(self).budget,
            !old(self).has(e.key),
        ensures
            final(self).inv(),
            final(self).entries@ == old(self).entries@.push(e),
            final(self).budget == old(self).budget,
            final(self).used == old(self).used + e.bytes,
    {
        proof {
            lemma_total_push(self.entries@, e);
        }
        let ghost before = self.entries@;
        let b = e.bytes;
        let ghost key = e.key;
        self.entries.push(e);
        self.used = add_u(self.used, b);
        proof {
            assert forall|k: int| 0 <= k < self.entries@.len() implies (
            #[trigger] self.entries@[k]).bytes as nat == self.entries@[k].region.spec_len() by {
                if k < before.len() {
                    assert(self.entries@[k] == before[k]);
                }
            }
            assert forall|a: int, c: int| 0 <= a < c < self.entries@.len() implies (
            #[trigger] self.entries@[a]).key != (#[trigger] self.entries@[c]).key by {
                if c < before.len() {
                    assert(self.entries@[a] == before[a]);
                    assert(self.entries@[c] == before[c]);
                } else {
                    assert(self.entries@[a] == before[a]);
                    assert(self.entries@[c].key == key);
                    assert(before[a].key != key);
                }
            }
        }
    }

    /// Look a function version up for entry. A hit makes the entry the most
    /// recently used and returns the cache's own borrow of its region, so
    /// there is no way to hold a region the cache has given up.
    ///
    /// `Some` exactly when the key is resident; after an eviction it is
    /// `None`, and the caller runs the interpreter.
    pub fn lookup(&mut self, key: Key) -> (r: Option<&R>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).spec_budget() == old(self).spec_budget(),
            final(self).spec_used() == old(self).spec_used(),
            r is Some <==> old(self).has(key),
            match r {
                Some(reg) => exists|i: int|
                    0 <= i < final(self).spec_entries().len() && (#[trigger] final(self).spec_entries()[i]).key
                        == key && final(self).spec_entries()[i].region == *reg,
                None => true,
            },
            forall|k: Key| final(self).has(k) <==> old(self).has(k),
    {
        match self.find(key) {
            None => None,
            Some(i) => {
                let e = self.remove_at(i);
                proof {
                    assert(!self.has(e.key)) by {
                        let s = old(self).entries@;
                        s.remove_ensures(i as int);
                        assert forall|k: int| 0 <= k < self.entries@.len() implies (
                        #[trigger] self.entries@[k]).key != e.key by {
                            let ik = if k < i as int {
                                k
                            } else {
                                k + 1
                            };
                            assert(self.entries@[k] == s[ik]);
                        }
                    }
                }
                let ghost removed = self.entries@;
                self.push_back(e);
                let n = self.entries.len();
                proof {
                    assert(self.entries@.last() == e);
                    assert forall|k: Key| self.has(k) <==> old(self).has(k) by {
                        if self.has(k) {
                            let j = choose|j: int|
                                0 <= j < self.entries@.len() && (#[trigger] self.entries@[j]).key
                                    == k;
                            if j == self.entries@.len() - 1 {
                                assert(old(self).entries@[i as int].key == k);
                            } else {
                                assert(removed[j] == old(self).entries@.remove(i as int)[j]);
                                let ij = if j < i as int {
                                    j
                                } else {
                                    j + 1
                                };
                                assert(old(self).entries@[ij].key == k);
                            }
                        }
                        if old(self).has(k) {
                            let j = choose|j: int|
                                0 <= j < old(self).entries@.len() && (
                                #[trigger] old(self).entries@[j]).key == k;
                            if j == i as int {
                                assert(self.entries@[self.entries@.len() - 1].key == k);
                            } else {
                                let nj = if j < i as int {
                                    j
                                } else {
                                    j - 1
                                };
                                assert(removed[nj] == old(self).entries@[j]);
                                assert(self.entries@[nj] == removed[nj]);
                            }
                        }
                    }
                }
                match self.entries.as_slice().get(sub_u(n, 1)) {
                    Some(en) => {
                        proof {
                            let last = self.entries@.len() - 1;
                            assert(*en == self.entries@[last]);
                            assert(self.entries@[last].key == key);
                            assert(self.entries@[last].region == en.region);
                            assert(0 <= last < self.spec_entries().len());
                            assert(self.spec_entries()[last].key == key
                                && self.spec_entries()[last].region == en.region);
                        }
                        Some(&en.region)
                    },
                    None => {
                        proof {
                            assert(false);
                        }
                        None
                    },
                }
            },
        }
    }

    /// Insert a compiled blob under `key`, evicting least recently used blobs
    /// until it fits the budget. `max_fn` is the per-function size cap.
    ///
    /// - On `Ok`, the blob is resident (the most recently used), the bytes in
    ///   use are within the budget, and the returned list holds every blob
    ///   that left: the old blob for the same key (`Replaced`), and the
    ///   evicted ones (`Capacity`). The caller unmaps them.
    /// - On `Err`, **the cache is unchanged** and the region comes back.
    pub fn insert(&mut self, key: Key, region: R, max_fn: usize) -> (res: Result<
        Vec<Evicted<R>>,
        Rejected<R>,
    >)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).spec_budget() == old(self).spec_budget(),
            match res {
                Ok(ev) => {
                    &&& final(self).spec_entries().len() > 0
                    &&& final(self).spec_entries().last().key == key
                    &&& final(self).spec_entries().last().region == region
                    &&& forall|j: int, i: int|
                        0 <= j < ev@.len() && 0 <= i < final(self).spec_entries().len() && (
                        #[trigger] final(self).spec_entries()[i]).key == (#[trigger] ev@[j]).key
                            ==> ev@[j].key == key
                },
                Err(rej) => {
                    &&& final(self).spec_entries() == old(self).spec_entries()
                    &&& final(self).spec_used() == old(self).spec_used()
                    &&& rej.region == region
                },
            },
    {
        let bytes = region.byte_len();
        if bytes == 0 {
            return Err(Rejected { why: Reject::Empty, region });
        }
        if bytes > max_fn {
            return Err(Rejected { why: Reject::FunctionTooLarge, region });
        }
        if bytes > self.budget {
            return Err(Rejected { why: Reject::ExceedsBudget, region });
        }
        let mut ev: Vec<Evicted<R>> = Vec::new();
        if let Some(i) = self.find(key) {
            let old_e = self.remove_at(i);
            proof {
                let s = old(self).entries@;
                s.remove_ensures(i as int);
                assert forall|k: int| 0 <= k < self.entries@.len() implies (
                #[trigger] self.entries@[k]).key != key by {
                    let ik = if k < i as int {
                        k
                    } else {
                        k + 1
                    };
                    assert(self.entries@[k] == s[ik]);
                }
            }
            ev.push(
                Evicted { key: old_e.key, region: old_e.region, bytes: old_e.bytes, why: Why::Replaced },
            );
        }
        while add_u(self.used, bytes) > self.budget
            invariant
                self.inv(),
                self.budget == old(self).budget,
                0 < bytes <= self.budget,
                bytes as nat == region.spec_len(),
                !self.has(key),
                forall|j: int, i: int|
                    0 <= j < ev@.len() && 0 <= i < self.entries@.len() ==> (
                    #[trigger] self.entries@[i]).key != (#[trigger] ev@[j]).key,
            decreases self.entries@.len(),
        {
            if self.entries.is_empty() {
                proof {
                    // `used + bytes > budget >= bytes` forces `used > 0`, and
                    // `used == total(entries)`.
                    assert(self.entries@ =~= Seq::<Entry<R>>::empty());
                    assert(self.used == 0);
                    assert(false);
                }
                return Err(Rejected { why: Reject::ExceedsBudget, region });
            }
            let ghost before = self.entries@;
            let victim = self.remove_at(0);
            proof {
                before.remove_ensures(0);
                assert forall|k: int| 0 <= k < self.entries@.len() implies (
                #[trigger] self.entries@[k]).key != victim.key by {
                    assert(self.entries@[k] == before[k + 1]);
                }
                assert forall|j: int, i: int|
                    0 <= j < ev@.len() && 0 <= i < self.entries@.len() implies (
                #[trigger] self.entries@[i]).key != (#[trigger] ev@[j]).key by {
                    assert(self.entries@[i] == before[i + 1]);
                }
                assert(!self.has(key)) by {
                    assert forall|k: int| 0 <= k < self.entries@.len() implies (
                    #[trigger] self.entries@[k]).key != key by {
                        assert(self.entries@[k] == before[k + 1]);
                    }
                }
            }
            let ghost ev_before = ev@;
            ev.push(
                Evicted { key: victim.key, region: victim.region, bytes: victim.bytes, why: Why::Capacity },
            );
            proof {
                assert forall|j: int, i: int|
                    0 <= j < ev@.len() && 0 <= i < self.entries@.len() implies (
                #[trigger] self.entries@[i]).key != (#[trigger] ev@[j]).key by {
                    if j < ev_before.len() {
                        assert(ev@[j] == ev_before[j]);
                    } else {
                        assert(ev@[j].key == victim.key);
                    }
                }
            }
        }
        let ghost before = self.entries@;
        self.push_back(Entry { key, region, bytes });
        proof {
            assert(self.entries@.last().key == key);
            assert forall|j: int, i: int|
                0 <= j < ev@.len() && 0 <= i < self.entries@.len() && (
                #[trigger] self.entries@[i]).key == (#[trigger] ev@[j]).key implies ev@[j].key
                == key by {
                if i < before.len() {
                    assert(self.entries@[i] == before[i]);
                }
            }
        }
        Ok(ev)
    }

    /// Drop every blob of function `func` (all versions), returning them to
    /// be unmapped. Afterwards no resident entry belongs to `func`.
    pub fn invalidate(&mut self, func: u32) -> (ev: Vec<Evicted<R>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).spec_budget() == old(self).spec_budget(),
            forall|i: int|
                0 <= i < final(self).spec_entries().len() ==> (
                #[trigger] final(self).spec_entries()[i]).key.func != func,
    {
        self.invalidate_but(func, None)
    }

    /// Drop the blobs of function `func` whose version is not `keep` (all of
    /// them if `keep` is `None`), returning them to be unmapped. Afterwards
    /// every resident blob of `func` is of the version `keep`.
    pub fn invalidate_but(&mut self, func: u32, keep: Option<u32>) -> (ev: Vec<Evicted<R>>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).spec_budget() == old(self).spec_budget(),
            forall|i: int|
                0 <= i < final(self).spec_entries().len() ==> !drops(
                    (#[trigger] final(self).spec_entries()[i]).key,
                    func,
                    keep,
                ),
    {
        let mut ev: Vec<Evicted<R>> = Vec::new();
        let mut i: usize = self.entries.len();
        while i > 0
            invariant
                self.inv(),
                self.budget == old(self).budget,
                i <= self.entries@.len(),
                forall|j: int|
                    i <= j < self.entries@.len() ==> !drops(
                        (#[trigger] self.entries@[j]).key,
                        func,
                        keep,
                    ),
            decreases i,
        {
            i = sub_u(i, 1);
            let hit = match self.entries.as_slice().get(i) {
                Some(e) => {
                    e.key.func == func && match keep {
                        None => true,
                        Some(v) => e.key.version != v,
                    }
                },
                None => {
                    proof {
                        assert(false);
                    }
                    false
                },
            };
            if hit {
                let ghost before = self.entries@;
                let e = self.remove_at(i);
                proof {
                    before.remove_ensures(i as int);
                    assert forall|j: int| i <= j < self.entries@.len() implies !drops(
                        (#[trigger] self.entries@[j]).key,
                        func,
                        keep,
                    ) by {
                        assert(self.entries@[j] == before[j + 1]);
                    }
                }
                ev.push(
                    Evicted { key: e.key, region: e.region, bytes: e.bytes, why: Why::Invalidated },
                );
            }
        }
        ev
    }

    /// The `i`th resident entry's key and length, least recently used first.
    pub fn entry_at(&self, i: usize) -> (r: Option<(Key, usize)>)
        ensures
            match r {
                Some((k, n)) => i < self.spec_entries().len() && self.spec_entries()[i as int].key
                    == k && self.spec_entries()[i as int].bytes == n,
                None => i >= self.spec_entries().len(),
            },
    {
        if i >= self.entries.len() {
            return None;
        }
        match self.entries.as_slice().get(i) {
            Some(e) => Some((e.key, e.bytes)),
            None => {
                proof {
                    assert(false);
                }
                None
            },
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    type C = CodeCache<Mapped<u32>>;
    type Gone = Vec<Evicted<Mapped<u32>>>;

    fn m(id: u32, len: usize) -> Mapped<u32> {
        Mapped { handle: id, len }
    }

    fn k(func: u32, version: u32) -> Key {
        Key { func, version }
    }

    fn inserted(r: Result<Gone, Rejected<Mapped<u32>>>) -> Gone {
        match r {
            Ok(v) => v,
            Err(r) => unreachable!("rejected: {:?}", r.why),
        }
    }

    #[test]
    fn budget_is_clamped() {
        assert_eq!(C::new(usize::MAX).budget(), MAX_BUDGET);
        assert_eq!(C::new(7).budget(), 7);
    }

    #[test]
    fn evicts_least_recently_used_and_never_enters_it() {
        let mut c = C::new(100);
        assert!(inserted(c.insert(k(1, 0), m(1, 40), 100)).is_empty());
        assert!(inserted(c.insert(k(2, 0), m(2, 40), 100)).is_empty());
        // Touch 1, so 2 is the oldest.
        assert!(matches!(c.lookup(k(1, 0)), Some(r) if r.handle == 1));
        let gone = inserted(c.insert(k(3, 0), m(3, 40), 100));
        assert_eq!(gone.len(), 1);
        let first = gone.first().map(|e| (e.key, e.why, e.bytes));
        assert_eq!(first, Some((k(2, 0), Why::Capacity, 40)));
        assert!(c.lookup(k(2, 0)).is_none());
        assert!(!c.contains(k(2, 0)));
        assert_eq!(c.used(), 80);
        assert_eq!(c.len(), 2);
    }

    #[test]
    fn a_big_blob_evicts_several() {
        let mut c = C::new(100);
        for i in 0..4u32 {
            let _ = inserted(c.insert(k(i, 0), m(i, 25), 100));
        }
        assert_eq!(c.used(), 100);
        let gone = inserted(c.insert(k(9, 0), m(9, 60), 100));
        assert_eq!(gone.len(), 3);
        assert_eq!(c.used(), 85);
    }

    #[test]
    fn the_same_key_replaces() {
        let mut c = C::new(100);
        let _ = inserted(c.insert(k(1, 0), m(1, 30), 100));
        let gone = inserted(c.insert(k(1, 0), m(2, 50), 100));
        assert_eq!(
            gone.first().map(|e| (e.why, e.region.handle)),
            Some((Why::Replaced, 1))
        );
        assert_eq!((c.len(), c.used()), (1, 50));
        assert!(matches!(c.lookup(k(1, 0)), Some(r) if r.handle == 2));
    }

    #[test]
    fn rejections_change_nothing_and_give_the_region_back() {
        let mut c = C::new(100);
        let _ = inserted(c.insert(k(1, 0), m(1, 60), 80));
        for (len, why) in [
            (0, Reject::Empty),
            (81, Reject::FunctionTooLarge),
            (101, Reject::FunctionTooLarge),
        ] {
            match c.insert(k(2, 0), m(2, len), 80) {
                Err(r) => assert_eq!((r.why, r.region.len), (why, len)),
                Ok(_) => unreachable!("accepted"),
            }
            assert_eq!((c.len(), c.used()), (1, 60));
        }
        match c.insert(k(2, 0), m(2, 101), 1000) {
            Err(r) => assert_eq!(r.why, Reject::ExceedsBudget),
            Ok(_) => unreachable!("accepted"),
        }
        assert_eq!((c.len(), c.used()), (1, 60));
    }

    #[test]
    fn invalidate_but_keeps_one_version() {
        let mut c = C::new(1000);
        for (f, v) in [(1, 0), (1, 1), (1, 2), (2, 0)] {
            let _ = inserted(c.insert(k(f, v), m(f.saturating_mul(10).saturating_add(v), 10), 100));
        }
        assert_eq!(c.invalidate_but(1, Some(1)).len(), 2);
        assert!(c.contains(k(1, 1)) && c.contains(k(2, 0)) && !c.contains(k(1, 0)));
        assert_eq!(c.invalidate(1).len(), 1);
        assert_eq!((c.len(), c.used()), (1, 10));
    }
}
