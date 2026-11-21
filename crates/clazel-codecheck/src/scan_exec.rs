//! The executable unit scan, proven to refine the spec's recursive
//! [`crate::spec::scan`]: [`scan_exec`] walks the instructions with an exec
//! array of register facts, and either finds that the spec scan refuses a
//! unit (`None`) or returns, for every byte offset, whether a unit starts
//! there (`Some`), which is membership in the spec's list of unit starts.

#[allow(unused_imports)]
use super::spec::*;
pub use super::unit_exec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Instruction start offsets increase: `start_of(ins, j) < start_of(ins, k)`
/// for `j < k <= len`.
pub proof fn lemma_start_of_lt(ins: Seq<Instr>, j: int, k: int)
    requires
        0 <= j < k <= ins.len(),
    ensures
        start_of(ins, j) < start_of(ins, k),
    decreases k,
{
    super::decode_all::lemma_encode_nonempty(ins[k - 1]);
    if j < k - 1 {
        lemma_start_of_lt(ins, j, k - 1);
    }
}

/// One step of the scan: after taking the unit at `j`, the whole scan is
/// the accumulated starts followed by the scan from the next unit.
pub proof fn lemma_scan_step(
    ins: Seq<Instr>,
    tg: Seq<int>,
    j: int,
    fs: Facts,
    fs0: Facts,
    acc: Seq<int>,
    ulen: int,
    ufacts: Facts,
)
    requires
        0 <= j < ins.len(),
        scan(ins, tg, 0, no_facts()) == (match scan(ins, tg, j, fs) {
            None => None::<Seq<int>>,
            Some(rest) => Some(acc + rest),
        }),
        fs0 == (if seq_has(tg, start_of(ins, j)) {
            no_facts()
        } else {
            fs
        }),
        unit_at(ins, j, fs0) == Some(Unit { len: ulen, facts: ufacts }),
        ulen >= 1,
        j + ulen <= ins.len(),
    ensures
        scan(ins, tg, 0, no_facts()) == (match scan(ins, tg, j + ulen, ufacts) {
            None => None::<Seq<int>>,
            Some(rest) => Some(acc.push(start_of(ins, j)) + rest),
        }),
{
    reveal_with_fuel(scan, 2);
    match scan(ins, tg, j + ulen, ufacts) {
        None => {},
        Some(rest) => {
            assert(acc + (seq![start_of(ins, j)] + rest) =~= acc.push(start_of(ins, j)) + rest);
        },
    }
}

/// A unit that the spec refuses makes the whole scan refuse.
pub proof fn lemma_scan_refuses(
    ins: Seq<Instr>,
    tg: Seq<int>,
    j: int,
    fs: Facts,
    fs0: Facts,
    acc: Seq<int>,
)
    requires
        0 <= j < ins.len(),
        scan(ins, tg, 0, no_facts()) == (match scan(ins, tg, j, fs) {
            None => None::<Seq<int>>,
            Some(rest) => Some(acc + rest),
        }),
        fs0 == (if seq_has(tg, start_of(ins, j)) {
            no_facts()
        } else {
            fs
        }),
        unit_at(ins, j, fs0) is None,
    ensures
        scan(ins, tg, 0, no_facts()) is None,
{
    reveal_with_fuel(scan, 2);
}

/// Resets what is known about every register.
pub fn reset_facts(fa: &mut Vec<FactE>)
    requires
        old(fa)@.len() == 16,
    ensures
        rel(final(fa)@, no_facts()),
{
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            fa@.len() == 16,
            forall|r: int| 0 <= r < k ==> fa@[r] == FactE::Unknown,
        decreases 16 - k,
    {
        fa.set(k, FactE::Unknown);
        k = k.saturating_add(1);
    }
    assert forall|r: int| 0 <= r < 16 implies fact_view(#[trigger] fa@[r]) == fact_of(
        no_facts(),
        r as u8,
    ) by {}
}

/// The scan of the spec, executed. `target[p]` says whether offset `p` is a
/// jump target or an entry (`seq_has(tg, p)`); the result says which offsets
/// start a unit.
#[verifier::spinoff_prover]
#[verifier::rlimit(4000)]
pub fn scan_exec(
    ins: &[Instr],
    st: &[usize],
    target: &[bool],
    Ghost(tg): Ghost<Seq<int>>,
    total: usize,
) -> (r: Option<Vec<bool>>)
    requires
        ins@.len() == st@.len(),
        ins@.len() < 0x8000_0000,
        total < 0x8000_0000,
        total as int == start_of(ins@, ins@.len() as int),
        forall|j: int| 0 <= j < ins@.len() ==> st@[j] as int == start_of(ins@, j),
        all_valid(ins@),
        target@.len() == total,
        forall|p: int| 0 <= p < total ==> target@[p] == seq_has(tg, p),
    ensures
        match r {
            Some(us) => {
                &&& scan(ins@, tg, 0, no_facts()) is Some
                &&& us@.len() == total
                &&& forall|p: int|
                    0 <= p < total ==> us@[p] == seq_has(scan(ins@, tg, 0, no_facts())->Some_0, p)
            },
            None => scan(ins@, tg, 0, no_facts()) is None,
        },
{
    let n = ins.len();
    let mut fa: Vec<FactE> = vec![FactE::Unknown; 16];
    let mut us: Vec<bool> = vec![false; total];
    let mut j: usize = 0;
    let ghost mut fs: Facts = no_facts();
    let ghost mut acc: Seq<int> = Seq::empty();
    proof {
        assert forall|r: int| 0 <= r < 16 implies fact_view(#[trigger] fa@[r]) == fact_of(
            no_facts(),
            r as u8,
        ) by {}
    }
    while j < n
        invariant
            n == ins@.len(),
            j <= n,
            ins@.len() == st@.len(),
            ins@.len() < 0x8000_0000,
            total < 0x8000_0000,
            total as int == start_of(ins@, ins@.len() as int),
            forall|q: int| 0 <= q < ins@.len() ==> st@[q] as int == start_of(ins@, q),
            all_valid(ins@),
            target@.len() == total,
            forall|p: int| 0 <= p < total ==> target@[p] == seq_has(tg, p),
            rel(fa@, fs),
            us@.len() == total,
            forall|p: int| 0 <= p < total ==> us@[p] == seq_has(acc, p),
            scan(ins@, tg, 0, no_facts()) == (match scan(ins@, tg, j as int, fs) {
                None => None::<Seq<int>>,
                Some(rest) => Some(acc + rest),
            }),
        decreases n - j,
    {
        let here: usize = match st.get(j) {
            Some(h) => *h,
            None => {
                return None;
            },
        };
        proof {
            lemma_start_of_lt(ins@, j as int, n as int);
        }
        let is_target = match target.get(here) {
            Some(t) => *t,
            None => false,
        };
        let ghost fs0 = if seq_has(tg, here as int) {
            no_facts()
        } else {
            fs
        };
        if is_target {
            reset_facts(&mut fa);
        }
        proof {
            assert(rel(fa@, fs0));
        }
        us.set(here, true);
        let ghost acc2 = acc.push(here as int);
        proof {
            assert forall|p: int| 0 <= p < total implies us@[p] == seq_has(acc2, p) by {
                assert(acc2.drop_last() =~= acc);
                assert(acc2.last() == here as int);
                reveal_with_fuel(seq_has, 2);
                assert(seq_has(acc2, p) == (p == here as int || seq_has(acc, p)));
                if p == here as int {
                    assert(us@[p] == true);
                } else {
                    assert(us@[p] == seq_has(acc, p));
                }
            }
            assert(here as int == start_of(ins@, j as int));
        }
        if exit_at_e(ins, j) {
            reset_facts(&mut fa);
            proof {
                assert(unit_at(ins@, j as int, fs0) == Some(Unit { len: 3, facts: no_facts() }));
                lemma_scan_step(ins@, tg, j as int, fs, fs0, acc, 3, no_facts());
                fs = no_facts();
                acc = acc2;
            }
            j = j.saturating_add(3);
        } else {
            match check_at_e(ins, j) {
                Some(c) => {
                    proof {
                        assert(valid_instr(ins@[j as int]));
                        assert(valid_instr(ins@[j as int + 1]));
                    }
                    fa.set(c.t as usize, FactE::Unknown);
                    fa.set(c.z as usize, FactE::Unknown);
                    fa.set(c.i as usize, FactE::Idx(c.k, c.n));
                    proof {
                        let p = check_params(ins@, j as int)->Some_0;
                        let f1 = set_fact(fs0, c.t, Fact::Unknown);
                        let f2 = set_fact(f1, c.z, Fact::Unknown);
                        let f3 = set_fact(f2, c.i, Fact::Idx(c.k as int, c.n as int));
                        assert(check_facts(fs0, ins@, j as int) == f3);
                        assert(unit_at(ins@, j as int, fs0) == Some(Unit { len: 8, facts: f3 }));
                        assert forall|r: int| 0 <= r < 16 implies fact_view(#[trigger] fa@[r])
                            == fact_of(f3, r as u8) by {
                            lemma_fact_of_set(fs0, c.t, Fact::Unknown, r as u8);
                            lemma_fact_of_set(f1, c.z, Fact::Unknown, r as u8);
                            lemma_fact_of_set(f2, c.i, Fact::Idx(c.k as int, c.n as int), r as u8);
                        }
                        lemma_scan_step(ins@, tg, j as int, fs, fs0, acc, 8, f3);
                        fs = f3;
                        acc = acc2;
                    }
                    j = j.saturating_add(8);
                },
                None => {
                    let i = match ins.get(j) {
                        Some(i) => i,
                        None => {
                            return None;
                        },
                    };
                    proof {
                        assert(valid_instr(*i));
                    }
                    let ok = plain_ok_e(&mut fa, Ghost(fs0), i);
                    if !ok {
                        proof {
                            assert(unit_at(ins@, j as int, fs0) is None);
                            lemma_scan_refuses(ins@, tg, j as int, fs, fs0, acc);
                        }
                        return None;
                    }
                    proof {
                        let f = plain_ok(fs0, ins@[j as int])->Some_0;
                        assert(unit_at(ins@, j as int, fs0) == Some(Unit { len: 1, facts: f }));
                        lemma_scan_step(ins@, tg, j as int, fs, fs0, acc, 1, f);
                        fs = f;
                        acc = acc2;
                    }
                    j = j.saturating_add(1);
                },
            }
        }
    }
    proof {
        assert(scan(ins@, tg, j as int, fs) == Some(Seq::<int>::empty()));
        assert(acc + Seq::<int>::empty() =~= acc);
    }
    Some(us)
}

} // verus!
