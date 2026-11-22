//! The executable unit checks of the validator, each proven equal to its
//! spec function: [`plain_ok_e`] to [`crate::spec::plain_ok`], [`exit_at_e`]
//! to [`crate::spec::exit_unit_at`], and [`check_at_e`] to
//! [`crate::spec::check_unit_at`] with its parameters.
//!
//! What is known about the 16 registers is an exec array of [`FactE`]
//! ([`rel`] relates it to the spec's list of bindings, [`crate::spec::Facts`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What is known about one register (the exec form of [`Fact`]).
#[derive(Clone, Copy)]
pub enum FactE {
    /// Nothing.
    Unknown,
    /// The base of region `k`.
    Base(u8),
    /// Checked for `n` bytes of region `k`.
    Idx(u8, u8),
}

/// The spec fact an exec fact stands for.
pub open spec fn fact_view(f: FactE) -> Fact {
    match f {
        FactE::Unknown => Fact::Unknown,
        FactE::Base(k) => Fact::Base(k as int),
        FactE::Idx(k, n) => Fact::Idx(k as int, n as int),
    }
}

/// The array `fa` of 16 exec facts is what the spec list `fs` says.
pub open spec fn rel(fa: Seq<FactE>, fs: Facts) -> bool {
    fa.len() == 16 && forall|r: int|
        0 <= r < 16 ==> fact_view(#[trigger] fa[r]) == fact_of(fs, r as u8)
}

/// Binding a register changes that register's fact only.
pub proof fn lemma_fact_of_set(fs: Facts, d: u8, f: Fact, r: u8)
    ensures
        fact_of(set_fact(fs, d, f), r) == if r == d {
            f
        } else {
            fact_of(fs, r)
        },
{
    let s = set_fact(fs, d, f);
    assert(s.drop_last() =~= fs);
    assert(s.last() == (Binding { reg: d, fact: f }));
}

/// The exec fact of register `r`.
pub fn fact_at(fa: &[FactE], r: u8) -> (f: FactE)
    requires
        fa@.len() == 16,
        r < 16,
    ensures
        f == fa@[r as int],
{
    match fa.get(r as usize) {
        Some(x) => *x,
        None => FactE::Unknown,
    }
}

/// The spec's `access_ok`.
pub fn access_ok_e(fa: &[FactE], Ghost(fs): Ghost<Facts>, m: &Mem, size: u8, store: bool) -> (r: bool)
    requires
        rel(fa@, fs),
        mem_ok(*m),
    ensures
        r == access_ok(fs, Access { mem: *m, size: size as int, store: store }),
{
    if m.base == 15 {
        let none = m.index.is_none();
        none && m.disp >= 0 && (m.disp as i64).wrapping_add(size as i64) <= 512 && (!store
            || 256 <= m.disp)
    } else {
        match &m.index {
            None => false,
            Some(ix) => ix.scale == 0 && m.disp == 0 && match (
                fact_at(fa, m.base),
                fact_at(fa, ix.reg),
            ) {
                (FactE::Base(k), FactE::Idx(k2, n)) => k == k2 && size <= n,
                _ => false,
            },
        }
    }
}

/// The spec's `written_gpr`.
pub fn written_gpr_e(i: &Instr) -> (r: Option<u8>)
    ensures
        r == written_gpr(*i),
{
    match i {
        Instr::MovRR { dst, .. } => Some(*dst),
        Instr::MovLoad { dst, .. } => Some(*dst),
        Instr::MovStore { .. } => None,
        Instr::MovImm32 { dst, .. } => Some(*dst),
        Instr::MovImm32S { dst, .. } => Some(*dst),
        Instr::MovImm64 { dst, .. } => Some(*dst),
        Instr::AluRR { alu, dst, .. } => match alu {
            AluOp::Cmp => None,
            _ => Some(*dst),
        },
        Instr::AluRM { alu, dst, .. } => match alu {
            AluOp::Cmp => None,
            _ => Some(*dst),
        },
        Instr::AluRI { alu, dst, .. } => match alu {
            AluOp::Cmp => None,
            _ => Some(*dst),
        },
        Instr::TestRR { .. } => None,
        Instr::TestRI { .. } => None,
        Instr::Neg { r, .. } => Some(*r),
        Instr::Not { r, .. } => Some(*r),
        Instr::ShiftImm { r, .. } => Some(*r),
        Instr::ShiftCl { r, .. } => Some(*r),
        Instr::ImulRR { dst, .. } => Some(*dst),
        Instr::ImulRRI { dst, .. } => Some(*dst),
        Instr::Jcc { .. } => None,
        Instr::Jmp { .. } => None,
        Instr::Ret => None,
        Instr::Cmovcc { dst, .. } => Some(*dst),
        Instr::Setcc { dst, .. } => Some(*dst),
        Instr::FpArith { .. } => None,
        Instr::Sqrtsd { .. } => None,
        Instr::Ucomisd { .. } => None,
        Instr::Cvtsi2sd { .. } => None,
        Instr::Cvttsd2si { dst, .. } => Some(*dst),
        Instr::Cvtsd2si { dst, .. } => Some(*dst),
        Instr::MovqToXmm { .. } => None,
        Instr::MovqFromXmm { dst, .. } => Some(*dst),
        Instr::MovsdLoad { .. } => None,
        Instr::MovsdStore { .. } => None,
    }
}

/// The spec's `mem_access`: the operand, its size, whether it is a store.
pub fn mem_access_e(i: &Instr) -> (r: Option<(&Mem, u8, bool)>)
    ensures
        match r {
            Some((m, s, st)) => mem_access(*i) == Some(
                Access { mem: *m, size: s as int, store: st },
            ),
            None => mem_access(*i) is None,
        },
{
    match i {
        Instr::MovLoad { sz, mem, .. } => Some(
            (
                mem,
                match sz {
                    Size::W64 => 8u8,
                    Size::W32 => 4u8,
                },
                false,
            ),
        ),
        Instr::MovStore { sz, mem, .. } => Some(
            (
                mem,
                match sz {
                    Size::W64 => 8u8,
                    Size::W32 => 4u8,
                },
                true,
            ),
        ),
        Instr::AluRM { sz, mem, .. } => Some(
            (
                mem,
                match sz {
                    Size::W64 => 8u8,
                    Size::W32 => 4u8,
                },
                false,
            ),
        ),
        Instr::FpArith { xsrc, .. } => match xsrc {
            XmmSrc::Mem(m) => Some((m, 8u8, false)),
            XmmSrc::Reg(_) => None,
        },
        Instr::Sqrtsd { xsrc, .. } => match xsrc {
            XmmSrc::Mem(m) => Some((m, 8u8, false)),
            XmmSrc::Reg(_) => None,
        },
        Instr::Ucomisd { xsrc, .. } => match xsrc {
            XmmSrc::Mem(m) => Some((m, 8u8, false)),
            XmmSrc::Reg(_) => None,
        },
        Instr::MovsdLoad { mem, .. } => Some((mem, 8u8, false)),
        Instr::MovsdStore { mem, .. } => Some((mem, 8u8, true)),
        _ => None,
    }
}

/// The spec's `base_load_region`: the region a table-base load names.
pub fn base_load_region_e(i: &Instr) -> (r: Option<u8>)
    ensures
        match r {
            Some(k) => base_load_region(*i) == Some(k as int),
            None => base_load_region(*i) is None,
        },
{
    match i {
        Instr::MovLoad { sz, mem, .. } => {
            let w64 = match sz {
                Size::W64 => true,
                Size::W32 => false,
            };
            let noidx = mem.index.is_none();
            if w64 && mem.base == 15 && noidx && 0 <= mem.disp && mem.disp < 256 && mem.disp % 16
                == 0 {
                Some((mem.disp / 16) as u8)
            } else {
                None
            }
        },
        _ => None,
    }
}

/// The spec's `plain_ok`: `true` and the new facts if one instruction is
/// permitted, else `false`.
#[verifier::spinoff_prover]
#[verifier::rlimit(1000)]
pub fn plain_ok_e(fa: &mut Vec<FactE>, Ghost(fs): Ghost<Facts>, i: &Instr) -> (r: bool)
    requires
        rel(old(fa)@, fs),
        valid_instr(*i),
    ensures
        r == (plain_ok(fs, *i) is Some),
        r ==> rel(final(fa)@, plain_ok(fs, *i)->Some_0),
{
    if let Instr::Ret = i {
        return false;
    }
    let wg = written_gpr_e(i);
    let wres = match wg {
        Some(d) => d == 15 || d == 4,
        None => false,
    };
    if wres {
        return false;
    }
    let bad = match mem_access_e(i) {
        Some((m, size, store)) => !access_ok_e(fa.as_slice(), Ghost(fs), m, size, store),
        None => false,
    };
    if bad {
        return false;
    }
    if let Instr::Jmp { .. } = i {
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
        proof {
            assert(rel(fa@, no_facts())) by {
                assert forall|r: int| 0 <= r < 16 implies fact_view(#[trigger] fa@[r]) == fact_of(
                    no_facts(),
                    r as u8,
                ) by {}
            }
        }
        return true;
    }
    match wg {
        None => true,
        Some(d) => {
            let f = match base_load_region_e(i) {
                Some(k) => FactE::Base(k),
                None => FactE::Unknown,
            };
            fa.set(d as usize, f);
            proof {
                let ns = set_fact(fs, d, fact_view(f));
                assert forall|r: int| 0 <= r < 16 implies fact_view(#[trigger] fa@[r])
                    == fact_of(ns, r as u8) by {
                    lemma_fact_of_set(fs, d, fact_view(f), r as u8);
                }
            }
            true
        },
    }
}

/// The spec's `exit_unit_at`.
pub fn exit_at_e(ins: &[Instr], j: usize) -> (r: bool)
    requires
        j < 0x8000_0000,
    ensures
        r == exit_unit_at(ins@, j as int),
{
    match (ins.get(j), ins.get(j.saturating_add(1)), ins.get(j.saturating_add(2))) {
        (
            Some(Instr::MovImm32 { dst: t, .. }),
            Some(Instr::MovStore { sz, mem, src }),
            Some(Instr::Ret),
        ) => {
            let w64 = match sz {
                Size::W64 => true,
                Size::W32 => false,
            };
            let noidx = mem.index.is_none();
            !(*t == 15 || *t == 4) && w64 && mem.base == 15 && noidx && mem.disp == 256 && *src
                == *t
        },
        _ => false,
    }
}

/// The parameters of a bounds-check sequence (the spec's `Chk`, without the
/// jump displacements).
pub struct ChkE {
    /// The region.
    pub k: u8,
    /// The size.
    pub n: u8,
    /// The index register.
    pub i: u8,
    /// The first scratch register.
    pub t: u8,
    /// The zero register.
    pub z: u8,
}

/// The spec's `check_unit_at` with the parameters `check_params` reads.
#[verifier::spinoff_prover]
#[verifier::rlimit(2000)]
pub fn check_at_e(ins: &[Instr], j: usize) -> (r: Option<ChkE>)
    requires
        j < 0x8000_0000,
    ensures
        match r {
            Some(c) => {
                &&& check_unit_at(ins@, j as int)
                &&& check_params(ins@, j as int) is Some
                &&& check_params(ins@, j as int)->Some_0.k == c.k as int
                &&& check_params(ins@, j as int)->Some_0.n == c.n as int
                &&& check_params(ins@, j as int)->Some_0.i == c.i
                &&& check_params(ins@, j as int)->Some_0.t == c.t
                &&& check_params(ins@, j as int)->Some_0.z == c.z
            },
            None => !check_unit_at(ins@, j as int),
        },
{
    let (t, i) = match ins.get(j) {
        Some(Instr::MovRR { sz: Size::W64, dst, src }) => (*dst, *src),
        _ => {
            return None;
        },
    };
    let n = match ins.get(j.saturating_add(1)) {
        Some(Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst, imm }) if *dst == t => *imm,
        _ => {
            return None;
        },
    };
    match ins.get(j.saturating_add(2)) {
        Some(Instr::Jcc { cc: 2, .. }) => {},
        _ => {
            return None;
        },
    }
    let disp = match ins.get(j.saturating_add(3)) {
        Some(
            Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst, mem: Mem { base: 15, index: None, disp } },
        ) if *dst == t => *disp,
        _ => {
            return None;
        },
    };
    match ins.get(j.saturating_add(4)) {
        Some(Instr::Jcc { cc: 7, .. }) => {},
        _ => {
            return None;
        },
    }
    let z = match ins.get(j.saturating_add(5)) {
        Some(Instr::MovImm32 { dst, imm_u32: 0 }) => *dst,
        _ => {
            return None;
        },
    };
    match ins.get(j.saturating_add(6)) {
        Some(
            Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst, mem: Mem { base: 15, index: None, disp: d6 } },
        ) if *dst == i && *d6 == disp => {},
        _ => {
            return None;
        },
    }
    match ins.get(j.saturating_add(7)) {
        Some(Instr::Cmovcc { cc: 3, sz: Size::W64, dst, src }) if *dst == i && *src == z => {},
        _ => {
            return None;
        },
    }
    if disp < 8 {
        return None;
    }
    let off = disp.wrapping_sub(8);
    if off % 16 != 0 || off / 16 >= 16 {
        return None;
    }
    if n < 1 {
        return None;
    }
    if n > 8 {
        return None;
    }
    if i == t || i == z || t == z {
        return None;
    }
    if i == 15 || i == 4 || t == 15 || t == 4 || z == 15 || z == 4 {
        return None;
    }
    Some(ChkE { k: (off / 16) as u8, n: n as u8, i, t, z })
}

} // verus!
