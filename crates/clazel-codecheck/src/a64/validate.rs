//! The executable A64 validator, proven **sound and complete**: [`validate`]
//! returns `true` if and only if the blob is [`super::spec::accepted`] for the
//! entries, so it meets `contract::validate_ensures`. It decodes once
//! ([`super::decode::decode_all_a64`]), marks the entries and the branch
//! targets, runs the unit scan ([`super::scan_exec::scan_exec`]) and checks
//! that every target is a unit start, in time and space linear in the blob.
//! Being Verus code it has no panic and no overflow. The counterpart of
//! [`crate::validate`]; completeness needs no assumption (see
//! [`super::contract`]).
use super::decode::decode_all_a64;
use super::scan_exec::scan_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The offsets of the direct branches of `ins[j..]` unfold one instruction at
/// a time.
pub proof fn lemma_jump_targets_step(ins: Seq<Instr>, j: int)
    requires
        0 <= j < ins.len(),
    ensures
        jump_targets(ins, j) == (match jump_rel(ins[j]) {
            Some(r) => seq![start_of(ins, j) + r],
            None => Seq::<int>::empty(),
        } + jump_targets(ins, j + 1)),
{
}

/// The branch immediate of an instruction (the spec's `jump_rel` is four times
/// it, in bytes).
pub fn jump_rel_e(i: &Instr) -> (r: Option<i32>)
    ensures
        match r {
            Some(d) => jump_rel(*i) == Some(d as int * 4),
            None => jump_rel(*i) is None,
        },
{
    match i {
        Instr::B { imm26 } => Some(*imm26),
        Instr::BCond { imm19, .. } => Some(*imm19),
        Instr::CompareBranch { imm19, .. } => Some(*imm19),
        _ => None,
    }
}

/// If the decomposition `ins` of the blob is the only one, an accepted blob
/// passes the policy as `ins`.
pub proof fn lemma_acc_policy(blob: Seq<u8>, ent: Seq<int>, ins: Seq<Instr>)
    requires
        decodes_to(blob, ins),
        forall|w: Seq<Instr>| #[trigger] decodes_to(blob, w) ==> ins =~= w,
    ensures
        accepted(blob, ent) ==> policy(ins, ent),
{
    if accepted(blob, ent) {
        let w = choose|w: Seq<Instr>| decodes_to(blob, w) && policy(w, ent);
        assert(decodes_to(blob, w));
        assert(ins =~= w);
    }
}

/// Whether `blob`, entered at `entries`, is accepted: `true` if and only if it
/// is, so the contract's soundness and completeness both hold.
#[verifier::spinoff_prover]
#[verifier::rlimit(4000)]
pub fn validate(blob: &[u8], entries: &[usize]) -> (ok: bool)
    requires
        blob@.len() <= 0x7FFF_FFFF,
    ensures
        crate::a64::contract::validate_ensures(blob@, entries@, ok),
{
    let ghost ent = crate::a64::contract::entry_offsets(entries@);
    let ins = match decode_all_a64(blob) {
        Some(x) => x,
        None => {
            proof {
                assert(!accepted(blob@, ent)) by {
                    if accepted(blob@, ent) {
                        let w = choose|w: Seq<Instr>| decodes_to(blob@, w) && policy(w, ent);
                        assert(decodes_to(blob@, w));
                    }
                }
            }
            return false;
        },
    };
    let n = ins.len();
    proof {
        assert(blob@.len() == 4 * n);
        assert(forall|w: Seq<Instr>| #[trigger] decodes_to(blob@, w) ==> ins@ =~= w);
        lemma_acc_policy(blob@, ent, ins@);
    }
    if n == 0 {
        proof {
            assert(!accepted(blob@, ent));
        }
        return false;
    }
    // The last instruction is ret or b.
    let last_ok = matches!(ins.get(n.saturating_sub(1)), Some(Instr::Ret | Instr::B { .. }));
    if !last_ok {
        proof {
            assert(!accepted(blob@, ent)) by {
                if accepted(blob@, ent) {
                    super::lemmas::lemma_policy_ends(ins@, ent);
                }
            }
        }
        return false;
    }
    // Targets: the entries, then the branch targets. `target[p]` marks the
    // offset `4p`.
    let mut target: Vec<bool> = vec![false; n];
    let ghost mut tgacc: Seq<int> = Seq::empty();
    let mut k: usize = 0;
    while k < entries.len()
        invariant
            k <= entries.len(),
            target@.len() == n,
            n == ins@.len(),
            n < 0x2000_0000,
            accepted(blob@, ent) ==> policy(ins@, ent),
            ent == crate::a64::contract::entry_offsets(entries@),
            tgacc.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] tgacc[q] == entries@[q] as int,
            forall|q: int|
                0 <= q < tgacc.len() ==> 0 <= #[trigger] tgacc[q] < 4 * n && tgacc[q] % 4 == 0,
            forall|p: int| 0 <= p < n ==> target@[p] == seq_has(tgacc, 4 * p),
        decreases entries.len() - k,
    {
        let e = match entries.get(k) {
            Some(e) => *e,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        let q4 = e / 4;
        let e4 = q4.saturating_add(q4).saturating_add(q4).saturating_add(q4);
        if e4 != e || q4 >= n {
            proof {
                assert(!accepted(blob@, ent)) by {
                    if accepted(blob@, ent) {
                        assert(ent.len() == entries@.len());
                        assert(e == entries@[k as int]);
                        assert(ent[k as int] == entries@[k as int] as int);
                        assert(ent[k as int] == e as int);
                        super::acc_lemmas::lemma_seq_has_at(ent, k as int);
                        super::acc_lemmas::lemma_seq_has_concat(
                            ent,
                            jump_targets(ins@, 0),
                            e as int,
                        );
                        assert(all_targets(ins@, ent) =~= ent + jump_targets(ins@, 0));
                        super::acc_lemmas::lemma_policy_in_range(ins@, ent, e as int);
                    }
                }
            }
            return false;
        }
        target.set(e / 4, true);
        let ghost old = tgacc;
        proof {
            tgacc = old.push(e as int);
            assert(tgacc.drop_last() =~= old);
            reveal_with_fuel(seq_has, 2);
            assert forall|p: int| 0 <= p < n implies target@[p] == seq_has(tgacc, 4 * p) by {
                assert(seq_has(tgacc, 4 * p) == (4 * p == e as int || seq_has(old, 4 * p)));
            }
            assert forall|q: int| 0 <= q < tgacc.len() implies 0 <= #[trigger] tgacc[q] < 4 * n
                && tgacc[q] % 4 == 0 by {
                if q < old.len() {
                    assert(tgacc[q] == old[q]);
                }
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(tgacc =~= ent);
    }
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            n == ins@.len(),
            n < 0x2000_0000,
            target@.len() == n,
            accepted(blob@, ent) ==> policy(ins@, ent),
            ent == crate::a64::contract::entry_offsets(entries@),
            forall|q: int|
                0 <= q < tgacc.len() ==> 0 <= #[trigger] tgacc[q] < 4 * n && tgacc[q] % 4 == 0,
            forall|p: int| 0 <= p < n ==> target@[p] == seq_has(tgacc, 4 * p),
            tgacc + jump_targets(ins@, j as int) =~= all_targets(ins@, ent),
        decreases n - j,
    {
        proof {
            lemma_jump_targets_step(ins@, j as int);
        }
        let rel = match ins.get(j) {
            Some(i) => jump_rel_e(i),
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        match rel {
            None => {
                proof {
                    assert(jump_rel(ins@[j as int]) is None);
                    assert(tgacc + jump_targets(ins@, j as int + 1) =~= all_targets(ins@, ent));
                }
            },
            Some(d) => {
                proof {
                    // The target `4j + 4d` is among the targets, so inside the
                    // blob if the blob is accepted.
                    let x = 4 * j as int + 4 * d as int;
                    assert(jump_rel(ins@[j as int]) == Some(d as int * 4));
                    assert(jump_targets(ins@, j as int) =~= seq![x] + jump_targets(
                        ins@,
                        j as int + 1,
                    ));
                    super::acc_lemmas::lemma_seq_has_concat(
                        seq![x],
                        jump_targets(ins@, j as int + 1),
                        x,
                    );
                    super::acc_lemmas::lemma_seq_has_single(x, x);
                    super::acc_lemmas::lemma_seq_has_concat(tgacc, jump_targets(ins@, j as int), x);
                    assert(seq_has(all_targets(ins@, ent), x));
                    assert(accepted(blob@, ent) ==> (0 <= j as int + d as int && (j as int + d as int)
                        < (n as int))) by {
                        if accepted(blob@, ent) {
                            super::acc_lemmas::lemma_policy_in_range(ins@, ent, x);
                        }
                    }
                }
                let t: i64 = match (j as i64).checked_add(d as i64) {
                    Some(t) => t,
                    None => {
                        proof {
                            assert(!accepted(blob@, ent));
                        }
                        return false;
                    },
                };
                proof {
                    assert(t as int == j as int + d as int);
                }
                if t < 0 || t >= n as i64 {
                    proof {
                        assert(!accepted(blob@, ent));
                    }
                    return false;
                }
                target.set(t as usize, true);
                let ghost old = tgacc;
                proof {
                    tgacc = old.push(4 * t as int);
                    assert(tgacc.drop_last() =~= old);
                    reveal_with_fuel(seq_has, 2);
                    assert forall|p: int| 0 <= p < n implies target@[p] == seq_has(
                        tgacc,
                        4 * p,
                    ) by {
                        assert(seq_has(tgacc, 4 * p) == (4 * p == 4 * t as int || seq_has(
                            old,
                            4 * p,
                        )));
                    }
                    assert forall|q: int| 0 <= q < tgacc.len() implies 0 <= #[trigger] tgacc[q] < 4
                        * n && tgacc[q] % 4 == 0 by {
                        if q < old.len() {
                            assert(tgacc[q] == old[q]);
                        }
                    }
                    assert(jump_targets(ins@, j as int) =~= seq![4 * t as int] + jump_targets(
                        ins@,
                        j as int + 1,
                    ));
                    assert(tgacc + jump_targets(ins@, j as int + 1) =~= old + jump_targets(
                        ins@,
                        j as int,
                    ));
                }
            },
        }
        j = j.saturating_add(1);
    }
    proof {
        assert(jump_targets(ins@, n as int) =~= Seq::<int>::empty());
        assert(tgacc =~= all_targets(ins@, ent));
    }
    let tg = Ghost(tgacc);
    let us = match scan_exec(ins.as_slice(), target.as_slice(), tg) {
        Some(us) => us,
        None => {
            proof {
                assert(!accepted(blob@, ent)) by {
                    if accepted(blob@, ent) {
                        assert(tgacc =~= all_targets(ins@, ent));
                    }
                }
            }
            return false;
        },
    };
    // Every target is a unit start.
    let mut p: usize = 0;
    while p < n
        invariant
            p <= n,
            n == ins@.len(),
            target@.len() == n,
            n < 0x2000_0000,
            ent == crate::a64::contract::entry_offsets(entries@),
            us@.len() == n,
            forall|q: int|
                0 <= q < tgacc.len() ==> 0 <= #[trigger] tgacc[q] < 4 * n && tgacc[q] % 4 == 0,
            forall|q: int| 0 <= q < p ==> (target@[q] ==> us@[q]),
            tgacc =~= all_targets(ins@, ent),
            scan(ins@, tgacc, 0, no_facts()) is Some,
            forall|q: int| 0 <= q < n ==> target@[q] == seq_has(tgacc, 4 * q),
            forall|q: int|
                0 <= q < n ==> us@[q] == seq_has(
                    scan(ins@, tgacc, 0, no_facts())->Some_0,
                    4 * q,
                ),
            accepted(blob@, ent) ==> policy(ins@, ent),
        decreases n - p,
    {
        let t = match target.get(p) {
            Some(t) => *t,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        let u = match us.get(p) {
            Some(u) => *u,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        if t && !u {
            proof {
                assert(!accepted(blob@, ent)) by {
                    if accepted(blob@, ent) {
                        let starts = scan(ins@, tgacc, 0, no_facts())->Some_0;
                        super::acc_lemmas::lemma_subset_elim(tgacc, starts, 4 * p as int);
                    }
                }
            }
            return false;
        }
        p = p.saturating_add(1);
    }
    proof {
        let starts = scan(ins@, tgacc, 0, no_facts())->Some_0;
        assert forall|i: int| 0 <= i < tgacc.len() implies seq_has(starts, #[trigger] tgacc[i]) by {
            let x = tgacc[i];
            let q = x / 4;
            assert(0 <= q < n && 4 * q == x);
            super::acc_lemmas::lemma_seq_has_at(tgacc, i);
            assert(target@[q] == seq_has(tgacc, 4 * q));
        }
        super::acc_lemmas::lemma_subset_intro(tgacc, starts);
        assert(policy(ins@, ent));
        assert(decodes_to(blob@, ins@));
    }
    true
}

} // verus!
