//! A divide-and-conquer form of [`super::spec::longest_match`], proven
//! equal to it ([`lemma_best_in_full`]). It exists so that Verus can
//! evaluate the matching rule on a concrete input (`by (compute_only)`, in
//! [`super::examples`] and kill certificates): the spec scans 2231 rows
//! one recursive call at a time, deeper than Verus's evaluator goes, while
//! this splits the rows in halves (depth 12).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Row `i` if its name is a prefix of the input from `pos` on.
pub open spec fn candidate(input: Seq<u32>, pos: int, i: nat) -> Option<nat> {
    if is_prefix_at(entity_name(i as int), input, pos) {
        Some(i)
    } else {
        None
    }
}

/// The longer of two candidates, the first on a tie.
pub open spec fn pick(a: Option<nat>, b: Option<nat>) -> Option<nat> {
    match (a, b) {
        (_, None) => a,
        (None, Some(_)) => b,
        (Some(x), Some(y)) => if entity_name(x as int).len() < entity_name(y as int).len() {
            b
        } else {
            a
        },
    }
}

/// The candidates of rows `lo .. hi`, picked from left to right.
pub open spec fn fold(input: Seq<u32>, pos: int, lo: nat, hi: nat) -> Option<nat>
    decreases hi,
{
    if hi <= lo {
        None
    } else {
        pick(fold(input, pos, lo, (hi - 1) as nat), candidate(input, pos, (hi - 1) as nat))
    }
}

/// The candidates of rows `lo .. hi`, picked by halves.
pub open spec fn best_in(input: Seq<u32>, pos: int, lo: nat, hi: nat) -> Option<nat>
    decreases hi - lo,
{
    if hi <= lo {
        None
    } else if hi == lo + 1 {
        candidate(input, pos, lo)
    } else {
        let mid = lo + (hi - lo) / 2;
        pick(best_in(input, pos, lo, mid as nat), best_in(input, pos, mid as nat, hi))
    }
}

proof fn lemma_pick_assoc(a: Option<nat>, b: Option<nat>, c: Option<nat>)
    ensures
        pick(pick(a, b), c) == pick(a, pick(b, c)),
{
}

/// Folding `lo .. hi` is picking between folding `lo .. mid` and `mid ..
/// hi`.
proof fn lemma_fold_split(input: Seq<u32>, pos: int, lo: nat, mid: nat, hi: nat)
    requires
        lo <= mid <= hi,
    ensures
        fold(input, pos, lo, hi) == pick(fold(input, pos, lo, mid), fold(input, pos, mid, hi)),
    decreases hi,
{
    if hi == mid {
    } else {
        lemma_fold_split(input, pos, lo, mid, (hi - 1) as nat);
        lemma_pick_assoc(
            fold(input, pos, lo, mid),
            fold(input, pos, mid, (hi - 1) as nat),
            candidate(input, pos, (hi - 1) as nat),
        );
    }
}

proof fn lemma_best_in_fold(input: Seq<u32>, pos: int, lo: nat, hi: nat)
    ensures
        best_in(input, pos, lo, hi) == fold(input, pos, lo, hi),
    decreases hi - lo,
{
    if hi <= lo {
    } else if hi == lo + 1 {
        assert(fold(input, pos, lo, lo) is None);
    } else {
        let mid = (lo + (hi - lo) / 2) as nat;
        lemma_best_in_fold(input, pos, lo, mid);
        lemma_best_in_fold(input, pos, mid, hi);
        lemma_fold_split(input, pos, lo, mid, hi);
    }
}

proof fn lemma_fold_upto(input: Seq<u32>, pos: int, k: nat)
    ensures
        fold(input, pos, 0, k) == longest_match_upto(input, pos, k),
    decreases k,
{
    if k > 0 {
        lemma_fold_upto(input, pos, (k - 1) as nat);
    }
}

/// See [`lemma_fold_split`].
pub proof fn lemma_fold_split_pub(input: Seq<u32>, pos: int, lo: nat, mid: nat, hi: nat)
    requires
        lo <= mid <= hi,
    ensures
        fold(input, pos, lo, hi) == pick(fold(input, pos, lo, mid), fold(input, pos, mid, hi)),
{
    lemma_fold_split(input, pos, lo, mid, hi);
}

/// See [`lemma_best_in_fold`].
pub proof fn lemma_best_in_fold_pub(input: Seq<u32>, pos: int, lo: nat, hi: nat)
    ensures
        best_in(input, pos, lo, hi) == fold(input, pos, lo, hi),
{
    lemma_best_in_fold(input, pos, lo, hi);
}

/// The halves form is the spec's matching rule.
pub proof fn lemma_best_in_full(input: Seq<u32>, pos: int)
    ensures
        best_in(input, pos, 0, entity_count()) == longest_match(input, pos),
{
    lemma_best_in_fold(input, pos, 0, entity_count());
    lemma_fold_upto(input, pos, entity_count());
}

} // verus!
