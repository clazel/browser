//! Facts about the spec's scan and policy that the completeness of the
//! validator needs: an accepted blob's targets all lie inside it, and the
//! list `seq_has` and `subset_of` behave as membership and inclusion.

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

/// Every unit start the scan finds is the start of an instruction at or after
/// `j`.
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

/// **An accepted blob's targets lie inside it**: every entry and every jump
/// target of an instruction list that passes the policy is the offset of one
/// of its instructions, so in `[0, start_of(ins, len))`.
pub proof fn lemma_policy_in_range(ins: Seq<Instr>, entries: Seq<int>, x: int)
    requires
        policy(ins, entries),
        seq_has(all_targets(ins, entries), x),
    ensures
        0 <= x < start_of(ins, ins.len() as int),
{
    let tg = all_targets(ins, entries);
    let starts = scan(ins, tg, 0, no_facts())->Some_0;
    lemma_subset_elim(tg, starts, x);
    lemma_scan_starts(ins, tg, 0, no_facts(), x);
    let k = choose|k: int| 0 <= k < ins.len() && x == start_of(ins, k);
    super::scan_exec::lemma_start_of_lt(ins, k, ins.len() as int);
    super::validate::lemma_start_of_ge(ins, k);
}

} // verus!
