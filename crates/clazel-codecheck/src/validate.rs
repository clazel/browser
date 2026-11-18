//! The executable validator, proven **sound**: [`validate`] returns `true`
//! only if the blob is [`crate::spec::accepted`] for the entries. It decodes
//! once ([`crate::decode_all::decode_all`]), marks the entries and the jump
//! targets, runs the unit scan ([`crate::scan_exec::scan_exec`]) and checks
//! that every target is a unit start, in time and space linear in the blob.
//!
//! Completeness (`accepted ==> true`) is not proven here.

use super::decode_all::decode_all;
use super::scan_exec::scan_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

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

/// Every instruction takes a byte: the start offset of instruction `k` is at
/// least `k`.
pub proof fn lemma_start_of_ge(ins: Seq<Instr>, k: int)
    requires
        0 <= k <= ins.len(),
    ensures
        start_of(ins, k) >= k,
    decreases k,
{
    if k > 0 {
        lemma_start_of_ge(ins, k - 1);
        super::decode_all::lemma_encode_nonempty(ins[k - 1]);
    }
}

/// The bytes of the instructions have as many bytes as the last start offset.
pub proof fn lemma_enc_all_len(ins: Seq<Instr>)
    ensures
        enc_all(ins).len() == start_of(ins, ins.len() as int),
    decreases ins.len(),
{
    if ins.len() > 0 {
        let d = ins.drop_last();
        lemma_enc_all_len(d);
        assert(ins =~= d.push(ins.last()));
        super::decode_all::lemma_start_of_push(d, ins.last(), d.len() as int);
    }
}

/// The offsets of the direct jumps of `ins[j..]` unfold one instruction at a
/// time.
pub proof fn lemma_jump_targets_step(ins: Seq<Instr>, j: int)
    requires
        0 <= j < ins.len(),
    ensures
        jump_targets(ins, j) == (match jump_rel(ins[j]) {
            Some(r) => seq![start_of(ins, j + 1) + r],
            None => Seq::<int>::empty(),
        } + jump_targets(ins, j + 1)),
{
}

/// The jump displacement of an instruction (the spec's `jump_rel`).
pub fn jump_rel_e(i: &Instr) -> (r: Option<i32>)
    ensures
        match r {
            Some(d) => jump_rel(*i) == Some(d as int),
            None => jump_rel(*i) is None,
        },
{
    match i {
        Instr::Jcc { rel, .. } => Some(*rel),
        Instr::Jmp { rel } => Some(*rel),
        _ => None,
    }
}

/// Whether `blob`, entered at `entries`, is accepted. Sound: a `true`
/// answer means [`accepted`].
#[verifier::spinoff_prover]
#[verifier::rlimit(4000)]
pub fn validate(blob: &[u8], entries: &[usize]) -> (ok: bool)
    requires
        blob@.len() <= 0x7FFF_FFFF,
    ensures
        ok ==> accepted(blob@, entries@.map_values(|e: usize| e as int)),
{
    let total = blob.len();
    let (ins, st) = match decode_all(blob) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let n = ins.len();
    proof {
        lemma_enc_all_len(ins@);
        assert(total as int == start_of(ins@, n as int));
        lemma_start_of_ge(ins@, n as int);
    }
    if n == 0 {
        return false;
    }
    // The last instruction is ret or jmp.
    let last_ok = matches!(ins.get(n.saturating_sub(1)), Some(Instr::Ret | Instr::Jmp { .. }));
    if !last_ok {
        return false;
    }
    let ghost ent = entries@.map_values(|e: usize| e as int);
    // Targets: the entries, then the jump targets.
    let mut target: Vec<bool> = vec![false; total];
    let ghost mut tgacc: Seq<int> = Seq::empty();
    let mut k: usize = 0;
    while k < entries.len()
        invariant
            k <= entries.len(),
            target@.len() == total,
            total <= 0x7FFF_FFFF,
            tgacc.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] tgacc[q] == entries@[q] as int,
            forall|q: int| 0 <= q < tgacc.len() ==> 0 <= #[trigger] tgacc[q] < total,
            forall|p: int| 0 <= p < total ==> target@[p] == seq_has(tgacc, p),
        decreases entries.len() - k,
    {
        let e = match entries.get(k) {
            Some(e) => *e,
            None => {
                return false;
            },
        };
        if e >= total {
            return false;
        }
        target.set(e, true);
        let ghost old = tgacc;
        proof {
            tgacc = old.push(e as int);
            assert(tgacc.drop_last() =~= old);
            reveal_with_fuel(seq_has, 2);
            assert forall|p: int| 0 <= p < total implies target@[p] == seq_has(tgacc, p) by {
                assert(seq_has(tgacc, p) == (p == e as int || seq_has(old, p)));
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
            ins@.len() == st@.len(),
            ins@.len() < 0x8000_0000,
            total as int == start_of(ins@, n as int),
            forall|q: int| 0 <= q < ins@.len() ==> st@[q] as int == start_of(ins@, q),
            all_valid(ins@),
            target@.len() == total,
            total <= 0x7FFF_FFFF,
            forall|q: int| 0 <= q < tgacc.len() ==> 0 <= #[trigger] tgacc[q] < total,
            forall|p: int| 0 <= p < total ==> target@[p] == seq_has(tgacc, p),
            tgacc + jump_targets(ins@, j as int) =~= all_targets(ins@, ent),
        decreases n - j,
    {
        proof {
            lemma_jump_targets_step(ins@, j as int);
        }
        let j1 = j.saturating_add(1);
        let next: usize = if j1 < n {
            match st.get(j1) {
                Some(s) => *s,
                None => {
                    return false;
                },
            }
        } else {
            total
        };
        proof {
            if j + 1 < n {
                super::scan_exec::lemma_start_of_lt(ins@, j as int + 1, n as int);
            }
        }
        assert(next as int == start_of(ins@, j as int + 1));
        assert(next <= total);
        let rel = match ins.get(j) {
            Some(i) => jump_rel_e(i),
            None => {
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
                let t: i64 = match (next as i64).checked_add(d as i64) {
                    Some(t) => t,
                    None => {
                        return false;
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
                    return false;
                }
                target.set(t as usize, true);
                let ghost old = tgacc;
                proof {
                    tgacc = old.push(t as int);
                    assert(tgacc.drop_last() =~= old);
                    reveal_with_fuel(seq_has, 2);
                    assert forall|p: int| 0 <= p < total implies target@[p] == seq_has(
                        tgacc,
                        p,
                    ) by {
                        assert(seq_has(tgacc, p) == (p == t as int || seq_has(old, p)));
                    }
                    assert(jump_targets(ins@, j as int) =~= seq![t as int] + jump_targets(
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
    let us = match scan_exec(ins.as_slice(), st.as_slice(), target.as_slice(), tg, total) {
        Some(us) => us,
        None => {
            return false;
        },
    };
    // Every target is a unit start.
    let mut p: usize = 0;
    while p < total
        invariant
            p <= total,
            target@.len() == total,
            total <= 0x7FFF_FFFF,
            us@.len() == total,
            forall|q: int| 0 <= q < p ==> (target@[q] ==> us@[q]),
        decreases total - p,
    {
        let t = match target.get(p) {
            Some(t) => *t,
            None => {
                return false;
            },
        };
        let u = match us.get(p) {
            Some(u) => *u,
            None => {
                return false;
            },
        };
        if t && !u {
            return false;
        }
        p = p.saturating_add(1);
    }
    proof {
        let starts = scan(ins@, tgacc, 0, no_facts())->Some_0;
        assert forall|i: int| 0 <= i < tgacc.len() implies seq_has(starts, #[trigger] tgacc[i]) by {
            lemma_seq_has_at(tgacc, i);
        }
        lemma_subset_intro(tgacc, starts);
        assert(policy(ins@, ent));
        assert(decodes_to(blob@, ins@));
    }
    true
}

} // verus!
