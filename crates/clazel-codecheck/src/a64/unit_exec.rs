//! The executable unit checks of the A64 validator, each proven equal to its
//! spec function: [`plain_ok_e`] to [`crate::a64::spec::plain_ok`],
//! [`exit_at_e`] to [`crate::a64::spec::exit_unit_at`], and [`check_at_e`] to
//! [`crate::a64::spec::check_unit_at`] with its parameters. The counterpart of
//! [`crate::unit_exec`].
//!
//! What is known about the 32 register numbers is an exec array of [`FactE`]
//! ([`rel`] relates it to the spec's list of bindings,
//! [`crate::a64::spec::Facts`]).

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

/// The array `fa` of 32 exec facts is what the spec list `fs` says.
pub open spec fn rel(fa: Seq<FactE>, fs: Facts) -> bool {
    fa.len() == 32 && forall|r: int|
        0 <= r < 32 ==> fact_view(#[trigger] fa[r]) == fact_of(fs, r as u8)
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
        fa@.len() == 32,
        r < 32,
    ensures
        f == fa@[r as int],
{
    match fa.get(r as usize) {
        Some(x) => *x,
        None => FactE::Unknown,
    }
}

/// Resets what is known about every register.
pub fn reset_facts(fa: &mut Vec<FactE>)
    requires
        old(fa)@.len() == 32,
    ensures
        rel(final(fa)@, no_facts()),
{
    let mut k: usize = 0;
    while k < 32
        invariant
            k <= 32,
            fa@.len() == 32,
            forall|r: int| 0 <= r < k ==> fa@[r] == FactE::Unknown,
        decreases 32 - k,
    {
        fa.set(k, FactE::Unknown);
        k = k.saturating_add(1);
    }
    assert forall|r: int| 0 <= r < 32 implies fact_view(#[trigger] fa@[r]) == fact_of(
        no_facts(),
        r as u8,
    ) by {}
}

/// A memory access (the exec form of [`Access`]).
pub struct AccE {
    /// The base register.
    pub base: u8,
    /// The offset register, if any.
    pub index: Option<u8>,
    /// The `S` bit.
    pub scaled: bool,
    /// The immediate byte offset.
    pub off: u32,
    /// The bytes touched.
    pub size: u8,
    /// A store.
    pub store: bool,
}

/// The spec access an exec access stands for.
pub open spec fn acc_view(a: AccE) -> Access {
    Access {
        base: a.base,
        index: a.index,
        scaled: a.scaled,
        off: a.off as int,
        size: a.size as int,
        store: a.store,
    }
}

/// The registers of the access are register numbers (below 32).
pub open spec fn acc_regs_ok(a: AccE) -> bool {
    a.base < 32 && (match a.index {
        Some(m) => m < 32,
        None => true,
    })
}

/// The spec's `mem_access`.
pub fn mem_access_e(i: &Instr) -> (r: Option<AccE>)
    requires
        valid_instr(*i),
    ensures
        match r {
            Some(a) => mem_access(*i) == Some(acc_view(a)) && acc_regs_ok(a),
            None => mem_access(*i) is None,
        },
{
    match i {
        Instr::LoadStoreImm { sf, load, n, imm12, .. } => {
            let sz: u8 = match sf {
                Width::W32 => 4,
                Width::W64 => 8,
            };
            Some(
                AccE {
                    base: *n,
                    index: None,
                    scaled: false,
                    off: (*imm12 as u32).wrapping_mul(sz as u32),
                    size: sz,
                    store: !*load,
                },
            )
        },
        Instr::LoadStoreReg { sf, load, n, m, s, .. } => {
            let sz: u8 = match sf {
                Width::W32 => 4,
                Width::W64 => 8,
            };
            Some(
                AccE {
                    base: *n,
                    index: Some(*m),
                    scaled: *s,
                    off: 0,
                    size: sz,
                    store: !*load,
                },
            )
        },
        Instr::FpLoadStoreImm { load, n, imm12, .. } => Some(
            AccE {
                base: *n,
                index: None,
                scaled: false,
                off: (*imm12 as u32) * 8,
                size: 8,
                store: !*load,
            },
        ),
        Instr::FpLoadStoreReg { load, n, m, s, .. } => Some(
            AccE { base: *n, index: Some(*m), scaled: *s, off: 0, size: 8, store: !*load },
        ),
        _ => None,
    }
}

/// The spec's `access_ok`.
pub fn access_ok_e(fa: &[FactE], Ghost(fs): Ghost<Facts>, a: &AccE) -> (r: bool)
    requires
        rel(fa@, fs),
        acc_regs_ok(*a),
    ensures
        r == access_ok(fs, acc_view(*a)),
{
    if a.base == 28 {
        a.index.is_none() && (a.off as u64).wrapping_add(a.size as u64) <= 512 && (!a.store || 256 <= a.off)
    } else {
        match a.index {
            None => false,
            Some(m) => !a.scaled && a.off == 0 && match (
                fact_at(fa, a.base),
                fact_at(fa, m),
            ) {
                (FactE::Base(k), FactE::Idx(k2, n)) => k == k2 && a.size <= n,
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
        Instr::AddSubShiftedReg { d, .. } => Some(*d),
        Instr::AddSubImm { d, .. } => Some(*d),
        Instr::MulAddSub { d, .. } => Some(*d),
        Instr::Div { d, .. } => Some(*d),
        Instr::LogicalShiftedReg { d, .. } => Some(*d),
        Instr::ShiftVariable { d, .. } => Some(*d),
        Instr::Bitfield { d, .. } => Some(*d),
        Instr::MoveWide { d, .. } => Some(*d),
        Instr::CondSelect { d, .. } => Some(*d),
        Instr::LoadStoreImm { load, t, .. } => if *load {
            Some(*t)
        } else {
            None
        },
        Instr::LoadStoreReg { load, t, .. } => if *load {
            Some(*t)
        } else {
            None
        },
        Instr::FpLoadStoreImm { .. } => None,
        Instr::FpLoadStoreReg { .. } => None,
        Instr::B { .. } => None,
        Instr::BCond { .. } => None,
        Instr::CompareBranch { .. } => None,
        Instr::Ret => None,
        Instr::FAddSub { .. } => None,
        Instr::FMul { .. } => None,
        Instr::FDiv { .. } => None,
        Instr::FUnary { .. } => None,
        Instr::FCmp { .. } => None,
        Instr::FMovGen { to_fp, d, .. } => if *to_fp {
            None
        } else {
            Some(*d)
        },
        Instr::Scvtf { .. } => None,
        Instr::Fcvtzs { d, .. } => Some(*d),
    }
}

/// The spec's `writes_reserved`.
pub fn writes_reserved_e(i: &Instr) -> (r: bool)
    ensures
        r == writes_reserved(*i),
{
    let sp = match i {
        Instr::AddSubImm { setflags, d, .. } => !*setflags && *d == 31,
        _ => false,
    };
    if sp {
        return true;
    }
    match written_gpr_e(i) {
        Some(d) => d == 28 || d == 30,
        None => false,
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
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => {
            let w64 = match sf {
                Width::W64 => true,
                Width::W32 => false,
            };
            let off: u32 = (*imm12 as u32) * 8;
            if w64 && *load && *n == 28 && *t != 31 && off < 256 && (off / 16).wrapping_mul(16) == off {
                Some((off / 16) as u8)
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
    if writes_reserved_e(i) {
        return false;
    }
    let bad = match mem_access_e(i) {
        Some(a) => !access_ok_e(fa.as_slice(), Ghost(fs), &a),
        None => false,
    };
    if bad {
        return false;
    }
    if let Instr::B { .. } = i {
        reset_facts(fa);
        return true;
    }
    match written_gpr_e(i) {
        None => true,
        Some(d) => {
            let f = match base_load_region_e(i) {
                Some(k) => FactE::Base(k),
                None => FactE::Unknown,
            };
            fa.set(d as usize, f);
            proof {
                let ns = set_fact(fs, d, fact_view(f));
                assert forall|r: int| 0 <= r < 32 implies fact_view(#[trigger] fa@[r])
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
            Some(Instr::MoveWide { sf: Width::W32, opcode: MoveWideOp::Z, d: t, hw: 0, .. }),
            Some(Instr::LoadStoreImm { sf: Width::W64, load: false, t: src, n, imm12 }),
            Some(Instr::Ret),
        ) => {
            *t < 31 && !(*t == 28 || *t == 30) && *src == *t && *n == 28 && (*imm12 as u32) * 8
                == 256
        },
        _ => false,
    }
}

/// The parameters of a bounds-check sequence (the spec's `Chk`, without the
/// branch offsets).
pub struct ChkE {
    /// The region.
    pub k: u8,
    /// The size.
    pub n: u8,
    /// The index register.
    pub i: u8,
    /// The scratch register for `i + n`.
    pub t: u8,
    /// The scratch register for the bound.
    pub bnd: u8,
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
                &&& check_params(ins@, j as int)->Some_0.bnd == c.bnd
            },
            None => !check_unit_at(ins@, j as int),
        },
{
    let (bnd, o) = match ins.get(j) {
        Some(Instr::LoadStoreImm { sf: Width::W64, load: true, t, n: 28, imm12 }) => (*t, *imm12),
        _ => {
            return None;
        },
    };
    let (t, i, n) = match ins.get(j.saturating_add(1)) {
        Some(
            Instr::AddSubImm { sf: Width::W64, sub_op: false, setflags: true, d, n, imm12, sh: false },
        ) => (*d, *n, *imm12),
        _ => {
            return None;
        },
    };
    match ins.get(j.saturating_add(2)) {
        Some(Instr::BCond { cond: 2, .. }) => {},
        _ => {
            return None;
        },
    }
    match ins.get(j.saturating_add(3)) {
        Some(
            Instr::AddSubShiftedReg {
                sf: Width::W64,
                sub_op: true,
                setflags: true,
                d: 31,
                n: n3,
                m: m3,
                shift_type: ShiftType::Lsl,
                shift_amount: 0,
            },
        ) if *n3 == t && *m3 == bnd => {},
        _ => {
            return None;
        },
    }
    match ins.get(j.saturating_add(4)) {
        Some(Instr::BCond { cond: 8, .. }) => {},
        _ => {
            return None;
        },
    }
    match ins.get(j.saturating_add(5)) {
        Some(
            Instr::AddSubShiftedReg {
                sf: Width::W64,
                sub_op: true,
                setflags: true,
                d: 31,
                n: n5,
                m: m5,
                shift_type: ShiftType::Lsl,
                shift_amount: 0,
            },
        ) if *n5 == i && *m5 == bnd => {},
        _ => {
            return None;
        },
    }
    match ins.get(j.saturating_add(6)) {
        Some(
            Instr::CondSelect {
                sf: Width::W64,
                else_inv: false,
                else_inc: false,
                d,
                n: n6,
                m: 31,
                cond: 3,
            },
        ) if *d == i && *n6 == i => {},
        _ => {
            return None;
        },
    }
    if o % 2 != 1 || o >= 32 {
        return None;
    }
    if n < 1 {
        return None;
    }
    if n > 8 {
        return None;
    }
    if i == t || i == bnd || t == bnd {
        return None;
    }
    if i >= 31 || t >= 31 || bnd >= 31 {
        return None;
    }
    if i == 28 || i == 30 || t == 28 || t == 30 || bnd == 28 || bnd == 30 {
        return None;
    }
    Some(ChkE { k: (o.wrapping_sub(1) / 2) as u8, n: n as u8, i, t, bnd })
}

} // verus!
