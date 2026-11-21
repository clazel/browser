//! Facts about the A64 spec's scan and policy that the completeness of the
//! validator needs: an accepted blob's targets all lie inside it on word
//! boundaries, and the list functions `seq_has` and `subset_of` behave as
//! membership and inclusion. The counterpart of [`crate::acc_lemmas`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `seq_has` of a concatenation.
pub proof fn lemma_seq_has_concat(a: Seq<int>, b: Seq<int>, x: int)
    ensures
        seq_has(a + b, x) == (seq_has(a, x) || seq_has(b, x)),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let d = b.drop_last();
        lemma_seq_has_concat(a, d, x);
        assert((a + b).drop_last() =~= a + d);
        assert((a + b).last() == b.last());
    }
}

/// A one-element list has just that element.
pub proof fn lemma_seq_has_single(y: int, x: int)
    ensures
        seq_has(seq![y], x) == (y == x),
{
    reveal_with_fuel(seq_has, 2);
    assert(seq![y].drop_last() =~= Seq::<int>::empty());
}

/// `seq_has(s, s[i])`.
pub proof fn lemma_seq_has_at(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        seq_has(s, s[i]),
    decreases s.len(),
{
    if i < s.len() - 1 {
        lemma_seq_has_at(s.drop_last(), i);
        assert(s.drop_last()[i] == s[i]);
    }
}

/// Membership in a subset implies membership in the superset.
pub proof fn lemma_subset_elim(a: Seq<int>, b: Seq<int>, x: int)
    requires
        subset_of(a, b),
        seq_has(a, x),
    ensures
        seq_has(b, x),
    decreases a.len(),
{
    if a.len() > 0 {
        if a.last() != x {
            lemma_subset_elim(a.drop_last(), b, x);
        }
    }
}

/// If every element of `a` is in `b`, `a` is a subset of `b`.
pub proof fn lemma_subset_intro(a: Seq<int>, b: Seq<int>)
    requires
        forall|i: int| 0 <= i < a.len() ==> seq_has(b, #[trigger] a[i]),
    ensures
        subset_of(a, b),
    decreases a.len(),
{
    if a.len() > 0 {
        let d = a.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies seq_has(b, #[trigger] d[i]) by {
            assert(d[i] == a[i]);
        }
        lemma_subset_intro(d, b);
        assert(a[a.len() - 1] == a.last());
    }
}

/// Every unit start the scan finds is the start of an instruction at or after
/// `j`: `4k` for some `k` with `j <= k < len`.
pub proof fn lemma_scan_starts(ins: Seq<Instr>, tg: Seq<int>, j: int, fs: Facts, x: int)
    requires
        0 <= j,
        scan(ins, tg, j, fs) is Some,
        seq_has(scan(ins, tg, j, fs)->Some_0, x),
    ensures
        exists|k: int| j <= k < ins.len() && x == start_of(ins, k),
    decreases ins.len() - j,
{
    reveal_with_fuel(scan, 2);
    if j < ins.len() {
        let here = start_of(ins, j);
        let fs0 = if seq_has(tg, here) {
            no_facts()
        } else {
            fs
        };
        let u = unit_at(ins, j, fs0)->Some_0;
        let rest = scan(ins, tg, j + u.len, u.facts)->Some_0;
        lemma_seq_has_concat(seq![here], rest, x);
        lemma_seq_has_single(here, x);
        if x != here {
            lemma_scan_starts(ins, tg, j + u.len, u.facts, x);
        } else {
            assert(j <= j < ins.len() && x == start_of(ins, j));
        }
    }
}

/// **An accepted blob's targets lie inside it, on word boundaries**: every
/// entry and every branch target of an instruction list that passes the
/// policy is the offset of one of its instructions, so a multiple of 4 in
/// `[0, 4 * len)`.
pub proof fn lemma_policy_in_range(ins: Seq<Instr>, entries: Seq<int>, x: int)
    requires
        policy(ins, entries),
        seq_has(all_targets(ins, entries), x),
    ensures
        0 <= x < 4 * ins.len(),
        x % 4 == 0,
{
    let tg = all_targets(ins, entries);
    let starts = scan(ins, tg, 0, no_facts())->Some_0;
    lemma_subset_elim(tg, starts, x);
    lemma_scan_starts(ins, tg, 0, no_facts(), x);
    let k = choose|k: int| 0 <= k < ins.len() && x == start_of(ins, k);
    assert(x == 4 * k);
}

} // verus!
