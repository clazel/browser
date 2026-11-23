//! Which byte offsets are entered or jumped to: [`mark_targets`] fills one
//! flag per byte of the blob, for every entry and every `jcc`/`jmp` target,
//! and refuses (`None`) a target outside the blob. This is the dataflow
//! validator's edge set: the places where control arrives other than by
//! falling through from the unit before.
//!
//! Only one direction is proven, which is all soundness needs: every element
//! of the spec's `all_targets` is inside the blob and flagged. A flag may be
//! set where the spec has no target (it never is, but nothing relies on it),
//! because an extra flag only makes the analysis forget more.
//!
//! The proof is by quantified invariants over the entries and the
//! instructions, not by an accumulated list as in `crate::validate`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Offset `p` is inside the blob (as long as `mark`) and flagged.
pub open spec fn covered(mark: Seq<bool>, p: int) -> bool {
    0 <= p < mark.len() && mark[p]
}

/// A member of a list is one of its elements.
pub proof fn lemma_has_index(s: Seq<int>, x: int)
    requires
        seq_has(s, x),
    ensures
        exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == x,
    decreases s.len(),
{
    if s.len() > 0 {
        if s.last() != x {
            lemma_has_index(s.drop_last(), x);
            let i = choose|i: int| 0 <= i < s.drop_last().len() && #[trigger] s.drop_last()[i] == x;
            assert(s[i] == x);
        } else {
            assert(s[s.len() - 1] == x);
        }
    }
}

/// A jump target of `ins[j..]` is that of one of those instructions: the
/// offset after it plus its displacement.
pub proof fn lemma_jt_has(ins: Seq<Instr>, j: int, p: int)
    requires
        0 <= j,
        seq_has(jump_targets(ins, j), p),
    ensures
        exists|q: int|
            j <= q < ins.len() && jump_rel(#[trigger] ins[q]) is Some && p == start_of(ins, q + 1)
                + jump_rel(ins[q])->Some_0,
    decreases ins.len() - j,
{
    if j < ins.len() {
        crate::validate::lemma_jump_targets_step(ins, j);
        let here: Seq<int> = match jump_rel(ins[j]) {
            Some(r) => seq![start_of(ins, j + 1) + r],
            None => Seq::empty(),
        };
        crate::acc_lemmas::lemma_seq_has_concat(here, jump_targets(ins, j + 1), p);
        if seq_has(here, p) {
            match jump_rel(ins[j]) {
                Some(r) => {
                    crate::acc_lemmas::lemma_seq_has_single(start_of(ins, j + 1) + r, p);
                    assert(j <= j < ins.len() && p == start_of(ins, j + 1) + r);
                },
                None => {
                    assert(here =~= Seq::<int>::empty());
                },
            }
        } else {
            lemma_jt_has(ins, j + 1, p);
        }
    } else {
        assert(jump_targets(ins, j) =~= Seq::<int>::empty());
    }
}

/// Flags every entry and every direct jump target of `ins`, or refuses one
/// outside the blob. `st[j]` is the start offset of instruction `j` and
/// `total` the length of the blob.
#[verifier::spinoff_prover]
#[verifier::rlimit(4000)]
pub fn mark_targets(
    ins: &[Instr],
    st: &[usize],
    entries: &[usize],
    total: usize,
    Ghost(ent): Ghost<Seq<int>>,
) -> (r: Option<Vec<bool>>)
    requires
        ins@.len() == st@.len(),
        ins@.len() < 0x8000_0000,
        total <= 0x7FFF_FFFF,
        total as int == start_of(ins@, ins@.len() as int),
        forall|j: int| 0 <= j < ins@.len() ==> st@[j] as int == start_of(ins@, j),
        ent == crate::contract::entry_offsets(entries@),
    ensures
        match r {
            Some(mark) => {
                &&& mark@.len() == total
                &&& forall|p: int| seq_has(all_targets(ins@, ent), p) ==> covered(mark@, p)
            },
            None => true,
        },
{
    let mut mark: Vec<bool> = vec![false; total];
    let mut k: usize = 0;
    while k < entries.len()
        invariant
            k <= entries.len(),
            mark@.len() == total,
            total <= 0x7FFF_FFFF,
            forall|q: int| 0 <= q < k ==> covered(mark@, (#[trigger] entries@[q]) as int),
        decreases entries.len() - k,
    {
        let e = match entries.get(k) {
            Some(e) => *e,
            None => {
                return None;
            },
        };
        if e >= total {
            return None;
        }
        let ghost old = mark@;
        mark.set(e, true);
        proof {
            assert forall|q: int| 0 <= q < k + 1 implies covered(
                mark@,
                (#[trigger] entries@[q]) as int,
            ) by {
                if q < k {
                    assert(covered(old, entries@[q] as int));
                } else {
                    assert(entries@[q] as int == e as int);
                }
            }
        }
        k = k.saturating_add(1);
    }
    let n = ins.len();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            n == ins@.len(),
            ins@.len() == st@.len(),
            ins@.len() < 0x8000_0000,
            total <= 0x7FFF_FFFF,
            total as int == start_of(ins@, ins@.len() as int),
            forall|q: int| 0 <= q < ins@.len() ==> st@[q] as int == start_of(ins@, q),
            mark@.len() == total,
            forall|q: int|
                0 <= q < entries@.len() ==> covered(mark@, (#[trigger] entries@[q]) as int),
            forall|q: int|
                0 <= q < j && jump_rel(#[trigger] ins@[q]) is Some ==> covered(
                    mark@,
                    start_of(ins@, q + 1) + jump_rel(ins@[q])->Some_0,
                ),
        decreases n - j,
    {
        let j1 = j.saturating_add(1);
        let next: usize = if j1 < n {
            match st.get(j1) {
                Some(s) => *s,
                None => {
                    return None;
                },
            }
        } else {
            total
        };
        proof {
            if j + 1 < n {
                crate::scan_exec::lemma_start_of_lt(ins@, j as int + 1, n as int);
            }
        }
        assert(next as int == start_of(ins@, j as int + 1));
        assert(next <= total);
        let rel = match ins.get(j) {
            Some(i) => crate::validate::jump_rel_e(i),
            None => {
                return None;
            },
        };
        match rel {
            None => {
                proof {
                    assert forall|q: int|
                        0 <= q < j + 1 && jump_rel(#[trigger] ins@[q]) is Some implies covered(
                        mark@,
                        start_of(ins@, q + 1) + jump_rel(ins@[q])->Some_0,
                    ) by {
                        if q == j {
                            assert(jump_rel(ins@[j as int]) is None);
                        }
                    }
                }
            },
            Some(d) => {
                let t: i64 = match (next as i64).checked_add(d as i64) {
                    Some(t) => t,
                    None => {
                        return None;
                    },
                };
                proof {
                    let a64 = next as i64;
                    let b64 = d as i64;
                    assert(a64 as int == next as int);
                    assert(b64 as int == d as int);
                    assert(a64.checked_add(b64) == Some(t));
                    assert(t as int == a64 as int + b64 as int);
                    assert(t as int == next as int + d as int);
                }
                if t < 0 || t >= total as i64 {
                    return None;
                }
                let ghost old = mark@;
                mark.set(t as usize, true);
                proof {
                    assert forall|q: int|
                        0 <= q < entries@.len() implies covered(
                        mark@,
                        (#[trigger] entries@[q]) as int,
                    ) by {
                        assert(covered(old, entries@[q] as int));
                    }
                    assert forall|q: int|
                        0 <= q < j + 1 && jump_rel(#[trigger] ins@[q]) is Some implies covered(
                        mark@,
                        start_of(ins@, q + 1) + jump_rel(ins@[q])->Some_0,
                    ) by {
                        if q < j {
                            let x = start_of(ins@, q + 1) + jump_rel(ins@[q])->Some_0;
                            assert(covered(old, x));
                        } else {
                            assert(jump_rel(ins@[j as int]) == Some(d as int));
                            assert(start_of(ins@, q + 1) + jump_rel(ins@[q])->Some_0 == t as int);
                        }
                    }
                }
            },
        }
        j = j.saturating_add(1);
    }
    proof {
        assert forall|p: int| seq_has(all_targets(ins@, ent), p) implies covered(mark@, p) by {
            crate::acc_lemmas::lemma_seq_has_concat(ent, jump_targets(ins@, 0), p);
            assert(all_targets(ins@, ent) =~= ent + jump_targets(ins@, 0));
            if seq_has(ent, p) {
                lemma_has_index(ent, p);
                let i = choose|i: int| 0 <= i < ent.len() && #[trigger] ent[i] == p;
                assert(ent[i] == entries@[i] as int);
            } else {
                lemma_jt_has(ins@, 0, p);
            }
        }
    }
    Some(mark)
}

} // verus!
