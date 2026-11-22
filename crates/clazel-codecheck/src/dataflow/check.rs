//! The checker of the dataflow solution, and the whole of the proof.
//!
//! The solver ([`super::solve`]) computes, for the start of every unit, what
//! it believes is known of each register. **It is not trusted and nothing is
//! proven about it**: this module takes its answer `inn` as a *certificate*
//! and verifies it against the spec, so a wrong solver can only make the
//! validator refuse.
//!
//! [`check_units`] walks the units once and, at each, checks three things
//! about the certificate's state `cur` for that unit:
//!
//! 1. **It is a post-fixpoint.** At an entry or jump target the state must be
//!    empty (all [`FactE::Unknown`]): the spec forgets everything where
//!    control may arrive other than by falling through. Anywhere else it must
//!    be no stronger than what the unit before computes, [`weaker_all`]: each
//!    register is unknown or has exactly the fact the transfer of the unit
//!    before gave it.
//! 2. **The unit is permitted in it.** An access must pass [`permit_e`]
//!    against `cur`; a write to `r15` or `rsp`, and a lone `ret`, refuse.
//! 3. **Its transfer** (what it does to the facts) is computed, for the next
//!    unit's check 1.
//!
//! The invariant that carries the proof is [`sound_for`]: the exec state is no
//! stronger than the spec's [`Facts`] (a register is `Unknown`, or its fact is
//! what `fact_of` says). A permission granted against a weaker state is
//! granted against the spec's ([`permit_e`]), and the transfer of a weaker
//! state is weaker than the spec's transfer. That `sound_for` is not
//! equality is why the solver may be imprecise. It is also why no completeness
//! is claimed.
//!
//! What this module shares with `crate::unit_exec`: only the syntactic
//! recognizers, each proven equal to its spec function ([`exit_at_e`],
//! [`check_at_e`], [`written_gpr_e`], [`mem_access_e`], [`base_load_region_e`]
//! and [`fact_at`]). The policy (what is permitted, what a unit does to the
//! facts) is written again here. The facts *after* a unit are the spec's
//! (`plain_ok`, `check_facts`), reached by `crate::scan_exec::lemma_scan_step`,
//! which is about the spec's `scan` only.

#[allow(unused_imports)]
use super::spec::*;
use crate::unit_exec::{
    FactE, base_load_region_e, check_at_e, exit_at_e, fact_at, mem_access_e, written_gpr_e,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exec state `fa` is **no stronger than** the spec facts `fs`: every
/// register is unknown, or has the fact `fs` gives it.
pub open spec fn sound_for(fa: Seq<FactE>, fs: Facts) -> bool {
    fa.len() == 16 && forall|r: int|
        0 <= r < 16 ==> (#[trigger] fa[r] == FactE::Unknown || crate::unit_exec::fact_view(fa[r])
            == fact_of(fs, r as u8))
}

/// `a` is no stronger than `b`, register by register.
pub open spec fn weaker(a: Seq<FactE>, b: Seq<FactE>) -> bool {
    a.len() == 16 && b.len() == 16 && forall|r: int|
        0 <= r < 16 ==> (#[trigger] a[r] == FactE::Unknown || a[r] == b[r])
}

/// An empty state is no stronger than anything.
pub proof fn lemma_unknown_sound(fa: Seq<FactE>, fs: Facts)
    requires
        fa.len() == 16,
        forall|r: int| 0 <= r < 16 ==> #[trigger] fa[r] == FactE::Unknown,
    ensures
        sound_for(fa, fs),
{
}

/// A state no stronger than a sound one is sound.
pub proof fn lemma_weaker_sound(a: Seq<FactE>, b: Seq<FactE>, fs: Facts)
    requires
        weaker(a, b),
        sound_for(b, fs),
    ensures
        sound_for(a, fs),
{
    assert forall|r: int| 0 <= r < 16 implies (#[trigger] a[r] == FactE::Unknown
        || crate::unit_exec::fact_view(a[r]) == fact_of(fs, r as u8)) by {
        if a[r] != FactE::Unknown {
            assert(a[r] == b[r]);
        }
    }
}

/// Setting a register to `f` in both keeps soundness.
pub proof fn lemma_set_sound(fa: Seq<FactE>, fs: Facts, d: u8, f: FactE)
    requires
        sound_for(fa, fs),
        d < 16,
    ensures
        sound_for(fa.update(d as int, f), set_fact(fs, d, crate::unit_exec::fact_view(f))),
{
    let ns = set_fact(fs, d, crate::unit_exec::fact_view(f));
    let na = fa.update(d as int, f);
    assert forall|r: int| 0 <= r < 16 implies (#[trigger] na[r] == FactE::Unknown
        || crate::unit_exec::fact_view(na[r]) == fact_of(ns, r as u8)) by {
        crate::unit_exec::lemma_fact_of_set(fs, d, crate::unit_exec::fact_view(f), r as u8);
    }
}

/// `a` is no stronger than `b` for one register.
pub fn weaker_e(a: FactE, b: FactE) -> (r: bool)
    ensures
        r ==> (a == FactE::Unknown || a == b),
{
    match (a, b) {
        (FactE::Unknown, _) => true,
        (FactE::Base(x), FactE::Base(y)) => x == y,
        (FactE::Idx(k, n), FactE::Idx(k2, n2)) => k == k2 && n == n2,
        _ => false,
    }
}

/// `a` is no stronger than `b`, in all 16 registers.
pub fn weaker_all(a: &[FactE], b: &[FactE]) -> (r: bool)
    requires
        a@.len() == 16,
        b@.len() == 16,
    ensures
        r ==> weaker(a@, b@),
{
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            a@.len() == 16,
            b@.len() == 16,
            forall|r: int| 0 <= r < k ==> (#[trigger] a@[r] == FactE::Unknown || a@[r] == b@[r]),
        decreases 16 - k,
    {
        let x = match a.get(k) {
            Some(x) => *x,
            None => {
                return false;
            },
        };
        let y = match b.get(k) {
            Some(y) => *y,
            None => {
                return false;
            },
        };
        if !weaker_e(x, y) {
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

/// Every register of `a` is unknown.
pub fn all_unknown_e(a: &[FactE]) -> (r: bool)
    requires
        a@.len() == 16,
    ensures
        r ==> forall|q: int| 0 <= q < 16 ==> #[trigger] a@[q] == FactE::Unknown,
{
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            a@.len() == 16,
            forall|q: int| 0 <= q < k ==> #[trigger] a@[q] == FactE::Unknown,
        decreases 16 - k,
    {
        match a.get(k) {
            Some(FactE::Unknown) => {},
            _ => {
                return false;
            },
        }
        k = k.saturating_add(1);
    }
    true
}

/// Makes every register unknown.
pub fn reset_e(fa: &mut Vec<FactE>)
    requires
        old(fa)@.len() == 16,
    ensures
        final(fa)@.len() == 16,
        forall|q: int| 0 <= q < 16 ==> #[trigger] final(fa)@[q] == FactE::Unknown,
{
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            fa@.len() == 16,
            forall|q: int| 0 <= q < k ==> #[trigger] fa@[q] == FactE::Unknown,
        decreases 16 - k,
    {
        fa.set(k, FactE::Unknown);
        k = k.saturating_add(1);
    }
}

/// Copies the 16 registers of `src` to `dst`.
pub fn copy_state(src: &[FactE], dst: &mut Vec<FactE>)
    requires
        src@.len() == 16,
        old(dst)@.len() == 16,
    ensures
        final(dst)@ == src@,
{
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            src@.len() == 16,
            dst@.len() == 16,
            forall|q: int| 0 <= q < k ==> #[trigger] dst@[q] == src@[q],
        decreases 16 - k,
    {
        let x = match src.get(k) {
            Some(x) => *x,
            None => FactE::Unknown,
        };
        dst.set(k, x);
        k = k.saturating_add(1);
    }
    assert(dst@ =~= src@);
}

/// Sets register `d` to `f`.
pub fn set_e(fa: &mut Vec<FactE>, d: u8, f: FactE)
    requires
        old(fa)@.len() == 16,
        d < 16,
    ensures
        final(fa)@ == old(fa)@.update(d as int, f),
{
    fa.set(d as usize, f);
}

/// Loads the certificate's state for the unit at instruction `j` (16 slots
/// from `16 * j`); a missing slot is unknown. Nothing is promised about the
/// values: they are checked by the caller.
pub fn load_state(inn: &[FactE], j: usize, cur: &mut Vec<FactE>)
    requires
        old(cur)@.len() == 16,
    ensures
        final(cur)@.len() == 16,
{
    let base = j.saturating_mul(16);
    let mut k: usize = 0;
    while k < 16
        invariant
            k <= 16,
            cur@.len() == 16,
        decreases 16 - k,
    {
        let f = match inn.get(base.saturating_add(k)) {
            Some(f) => *f,
            None => FactE::Unknown,
        };
        cur.set(k, f);
        k = k.saturating_add(1);
    }
}

/// An access is permitted in the state `cur`, which is no stronger than the
/// spec facts `fs`: so it is permitted by the spec's `access_ok` in `fs`.
/// The same two cases as the spec (`J.6/every load and store ...`): the
/// context, or a region through a base and an index known in `cur`.
pub fn permit_e(cur: &[FactE], Ghost(fs): Ghost<Facts>, m: &Mem, size: u8, store: bool) -> (r: bool)
    requires
        sound_for(cur@, fs),
        mem_ok(*m),
    ensures
        r ==> access_ok(fs, Access { mem: *m, size: size as int, store: store }),
{
    if m.base == 15 {
        let none = m.index.is_none();
        none && m.disp >= 0 && (m.disp as i64).wrapping_add(size as i64) <= 512 && (!store
            || 256 <= m.disp)
    } else {
        match &m.index {
            None => false,
            Some(ix) => {
                if !(ix.scale == 0 && m.disp == 0) {
                    return false;
                }
                let b = fact_at(cur, m.base);
                let x = fact_at(cur, ix.reg);
                match (b, x) {
                    (FactE::Base(k), FactE::Idx(k2, n)) => k == k2 && size <= n,
                    _ => false,
                }
            },
        }
    }
}

/// The units, checked against the certificate `inn`.
///
/// `mark[p]` says offset `p` is an entry or jump target (given: every spec
/// target is marked). Returns `None` if any check fails; otherwise, for every
/// byte offset, whether a unit starts there, which is membership in the
/// spec's list of unit starts, with the spec's scan known to succeed.
#[verifier::spinoff_prover]
#[verifier::rlimit(8000)]
pub fn check_units(
    ins: &[Instr],
    st: &[usize],
    mark: &[bool],
    inn: &[FactE],
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
        mark@.len() == total,
        forall|p: int| seq_has(tg, p) ==> super::targets::covered(mark@, p),
    ensures
        match r {
            Some(us) => {
                &&& scan(ins@, tg, 0, no_facts()) is Some
                &&& us@.len() == total
                &&& forall|p: int|
                    0 <= p < total ==> us@[p] == seq_has(scan(ins@, tg, 0, no_facts())->Some_0, p)
            },
            None => true,
        },
{
    let n = ins.len();
    let mut cur: Vec<FactE> = vec![FactE::Unknown; 16];
    let mut prev: Vec<FactE> = vec![FactE::Unknown; 16];
    let mut us: Vec<bool> = vec![false; total];
    let mut j: usize = 0;
    let ghost mut fs: Facts = no_facts();
    let ghost mut acc: Seq<int> = Seq::empty();
    proof {
        lemma_unknown_sound(prev@, fs);
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
            mark@.len() == total,
            forall|p: int| seq_has(tg, p) ==> super::targets::covered(mark@, p),
            cur@.len() == 16,
            sound_for(prev@, fs),
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
            crate::scan_exec::lemma_start_of_lt(ins@, j as int, n as int);
        }
        // Check 1: the certificate's state at this unit is a post-fixpoint.
        let is_target = match mark.get(here) {
            Some(t) => *t,
            None => {
                return None;
            },
        };
        load_state(inn, j, &mut cur);
        let in_ok = if is_target {
            all_unknown_e(cur.as_slice())
        } else {
            weaker_all(cur.as_slice(), prev.as_slice())
        };
        if !in_ok {
            return None;
        }
        let ghost fs0 = if seq_has(tg, here as int) {
            no_facts()
        } else {
            fs
        };
        proof {
            if seq_has(tg, here as int) {
                assert(super::targets::covered(mark@, here as int));
                assert(is_target);
            }
            if is_target {
                lemma_unknown_sound(cur@, fs0);
            } else {
                assert(fs0 == fs);
                lemma_weaker_sound(cur@, prev@, fs);
            }
            assert(sound_for(cur@, fs0));
        }
        us.set(here, true);
        let ghost acc2 = acc.push(here as int);
        proof {
            assert forall|p: int| 0 <= p < total implies us@[p] == seq_has(acc2, p) by {
                assert(acc2.drop_last() =~= acc);
                assert(acc2.last() == here as int);
                reveal_with_fuel(seq_has, 2);
                assert(seq_has(acc2, p) == (p == here as int || seq_has(acc, p)));
            }
            assert(here as int == start_of(ins@, j as int));
        }
        if exit_at_e(ins, j) {
            // The exit sequence: nothing is known after it.
            reset_e(&mut prev);
            proof {
                assert(unit_at(ins@, j as int, fs0) == Some(Unit { len: 3, facts: no_facts() }));
                crate::scan_exec::lemma_scan_step(ins@, tg, j as int, fs, fs0, acc, 3, no_facts());
                lemma_unknown_sound(prev@, no_facts());
                fs = no_facts();
                acc = acc2;
            }
            j = j.saturating_add(3);
        } else {
            match check_at_e(ins, j) {
                Some(c) => {
                    // The bounds-check sequence: its scratch registers are
                    // unknown after it, and its index is checked.
                    proof {
                        assert(valid_instr(ins@[j as int]));
                        assert(valid_instr(ins@[j as int + 1]));
                        assert(valid_instr(ins@[j as int + 5]));
                    }
                    copy_state(cur.as_slice(), &mut prev);
                    set_e(&mut prev, c.t, FactE::Unknown);
                    set_e(&mut prev, c.z, FactE::Unknown);
                    set_e(&mut prev, c.i, FactE::Idx(c.k, c.n));
                    proof {
                        let f1 = set_fact(fs0, c.t, Fact::Unknown);
                        let f2 = set_fact(f1, c.z, Fact::Unknown);
                        let f3 = set_fact(f2, c.i, Fact::Idx(c.k as int, c.n as int));
                        assert(check_facts(fs0, ins@, j as int) == f3);
                        assert(unit_at(ins@, j as int, fs0) == Some(Unit { len: 8, facts: f3 }));
                        lemma_set_sound(cur@, fs0, c.t, FactE::Unknown);
                        lemma_set_sound(cur@.update(c.t as int, FactE::Unknown), f1, c.z, FactE::Unknown);
                        lemma_set_sound(
                            cur@.update(c.t as int, FactE::Unknown).update(c.z as int, FactE::Unknown),
                            f2,
                            c.i,
                            FactE::Idx(c.k, c.n),
                        );
                        assert(prev@ =~= cur@.update(c.t as int, FactE::Unknown).update(
                            c.z as int,
                            FactE::Unknown,
                        ).update(c.i as int, FactE::Idx(c.k, c.n)));
                        crate::scan_exec::lemma_scan_step(ins@, tg, j as int, fs, fs0, acc, 8, f3);
                        fs = f3;
                        acc = acc2;
                    }
                    j = j.saturating_add(8);
                },
                None => {
                    // One instruction, alone.
                    let i = match ins.get(j) {
                        Some(i) => i,
                        None => {
                            return None;
                        },
                    };
                    proof {
                        assert(valid_instr(*i));
                    }
                    // Check 2: it is permitted in the certificate's state.
                    if let Instr::Ret = i {
                        return None;
                    }
                    let wg = written_gpr_e(i);
                    let reserved = match wg {
                        Some(d) => d == 15 || d == 4,
                        None => false,
                    };
                    if reserved {
                        return None;
                    }
                    if let Some((m, size, store)) = mem_access_e(i) {
                        proof {
                            assert(mem_ok(*m));
                        }
                        if !permit_e(cur.as_slice(), Ghost(fs0), m, size, store) {
                            return None;
                        }
                    }
                    // Check 3: its transfer.
                    copy_state(cur.as_slice(), &mut prev);
                    if let Instr::Jmp { .. } = i {
                        reset_e(&mut prev);
                        proof {
                            lemma_unknown_sound(prev@, no_facts());
                            assert(plain_ok(fs0, ins@[j as int]) == Some(no_facts()));
                        }
                    } else {
                        match wg {
                            None => {
                                proof {
                                    assert(plain_ok(fs0, ins@[j as int]) == Some(fs0));
                                }
                            },
                            Some(d) => {
                                let f = match base_load_region_e(i) {
                                    Some(k) => FactE::Base(k),
                                    None => FactE::Unknown,
                                };
                                proof {
                                    assert(valid_instr(*i));
                                    assert(d < 16);
                                }
                                set_e(&mut prev, d, f);
                                proof {
                                    lemma_set_sound(cur@, fs0, d, f);
                                    assert(plain_ok(fs0, ins@[j as int]) == Some(
                                        set_fact(fs0, d, crate::unit_exec::fact_view(f)),
                                    ));
                                }
                            },
                        }
                    }
                    proof {
                        let f = plain_ok(fs0, ins@[j as int])->Some_0;
                        assert(unit_at(ins@, j as int, fs0) == Some(Unit { len: 1, facts: f }));
                        crate::scan_exec::lemma_scan_step(ins@, tg, j as int, fs, fs0, acc, 1, f);
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
