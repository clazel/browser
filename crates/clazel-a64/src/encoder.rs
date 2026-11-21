//! The **executable encoder**: [`encode_instr`] computes the canonical
//! encoding of an instruction of the subset and is proven to meet
//! [`crate::contract::encode_ensures`] (jit.md J.4, J.6): its result is the
//! word [`encode`] defines.
//!
//! One arm per [`Instr`] variant, each the sum of the fixed bits of the
//! variant and its fields at their positions, in the same order as the spec's
//! `encode`. The sums are written with `wrapping_add` and `wrapping_mul` (the
//! workspace's `arithmetic_side_effects` lint forbids `+` and `*`); Verus
//! proves that no step wraps, because every field is in range
//! ([`valid_instr`]), so each arm is the spec's integer sum.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `-2^25 <= v < 2^25` is `signed_fits(v, 26)`, and `-2^18 <= v < 2^18` is
/// `signed_fits(v, 19)`: the two signed fields of the subset.
pub proof fn lemma_signed_fits()
    ensures
        forall|v: int| #[trigger] signed_fits(v, 26) == (-0x200_0000 <= v && v < 0x200_0000),
        forall|v: int| #[trigger] signed_fits(v, 19) == (-0x4_0000 <= v && v < 0x4_0000),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(p2(25) == 0x200_0000);
    assert(p2(18) == 0x4_0000);
    assert forall|v: int| #[trigger] signed_fits(v, 26) == (-0x200_0000 <= v && v < 0x200_0000) by {
        assert(p2((26nat - 1) as nat) == 0x200_0000);
    }
    assert forall|v: int| #[trigger] signed_fits(v, 19) == (-0x4_0000 <= v && v < 0x4_0000) by {
        assert(p2((19nat - 1) as nat) == 0x4_0000);
    }
}

/// The `sf` bit.
pub fn width_u32(sf: &Width) -> (r: u32)
    ensures
        r as int == sf_bit(*sf),
{
    match sf {
        Width::W32 => 0,
        Width::W64 => 1,
    }
}

/// A flag as a 0/1 field.
pub fn bool_u32(x: bool) -> (r: u32)
    ensures
        r as int == b(x),
{
    if x {
        1
    } else {
        0
    }
}

/// The `shift` field.
pub fn shift_u32(s: &ShiftType) -> (r: u32)
    ensures
        r as int == shift_field(*s),
{
    match s {
        ShiftType::Lsl => 0,
        ShiftType::Lsr => 1,
        ShiftType::Asr => 2,
        ShiftType::Ror => 3,
    }
}

/// The `opc` field of the logical shifted-register forms.
pub fn logical_opc_u32(o: &LogicalOpc) -> (r: u32)
    ensures
        r as int == logical_opc_field(*o),
{
    match o {
        LogicalOpc::And => 0,
        LogicalOpc::Orr => 1,
        LogicalOpc::Eor => 2,
        LogicalOpc::Ands => 3,
    }
}

/// The `opc` field of the one-source floating-point forms.
pub fn fp_unary_opc_u32(o: &FPUnaryOp) -> (r: u32)
    ensures
        r as int == fp_unary_opc_field(*o),
{
    match o {
        FPUnaryOp::Mov => 0,
        FPUnaryOp::Abs => 1,
        FPUnaryOp::Neg => 2,
        FPUnaryOp::Sqrt => 3,
    }
}

/// The `K` bit of `MOVZ` (0) and `MOVK` (1).
pub fn move_wide_u32(o: &MoveWideOp) -> (r: u32)
    ensures
        r as int == b(*o is K),
{
    match o {
        MoveWideOp::Z => 0,
        MoveWideOp::K => 1,
    }
}

/// The 26-bit field of a signed offset: two's complement.
pub fn simm26_u32(v: i32) -> (r: u32)
    requires
        -0x200_0000 <= v < 0x200_0000,
    ensures
        r as int == (v as int) % 0x400_0000,
{
    if v >= 0 {
        v as u32
    } else {
        v.wrapping_add(0x400_0000) as u32
    }
}

/// The 19-bit field of a signed offset: two's complement.
pub fn simm19_u32(v: i32) -> (r: u32)
    requires
        -0x4_0000 <= v < 0x4_0000,
    ensures
        r as int == (v as int) % 0x8_0000,
{
    if v >= 0 {
        v as u32
    } else {
        v.wrapping_add(0x8_0000) as u32
    }
}

/// `acc + t * m`, when that fits.
pub fn add_field(acc: u32, t: u32, m: u32) -> (r: u32)
    requires
        acc as int + (t as int) * (m as int) < 0x1_0000_0000,
    ensures
        r as int == acc as int + (t as int) * (m as int),
{
    acc.wrapping_add(t.wrapping_mul(m))
}

/// The canonical encoding of a valid `AddSubShiftedReg`.
pub fn enc_add_sub_shifted_reg(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is AddSubShiftedReg,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } => {
            let w: u32 = 0xb00_0000u32;
            let tv = bool_u32(*sub_op);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x4000_0000);
            let tv = bool_u32(*setflags);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x2000_0000);
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = shift_u32(shift_type);
            proof {
                assert(tv < 0x4);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *shift_amount as u32;
            proof {
                assert(tv < 0x40);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `AddSubImm`.
pub fn enc_add_sub_imm(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is AddSubImm,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } => {
            let w: u32 = 0x1100_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = bool_u32(*sub_op);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x4000_0000);
            let tv = bool_u32(*setflags);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x2000_0000);
            let tv = bool_u32(*sh);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *imm12 as u32;
            proof {
                assert(tv < 0x1000);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `MulAddSub`.
pub fn enc_mul_add_sub(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is MulAddSub,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::MulAddSub { sf, sub_op, d, n, m, a } => {
            let w: u32 = 0x1b00_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = bool_u32(*sub_op);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000);
            let tv = *a as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `Div`.
pub fn enc_div(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is Div,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::Div { sf, is_unsigned, d, n, m } => {
            let w: u32 = 0x1ac0_0800u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = bool_u32(!*is_unsigned);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `LogicalShiftedReg`.
pub fn enc_logical_shifted_reg(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is LogicalShiftedReg,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } => {
            let w: u32 = 0xa00_0000u32;
            let tv = logical_opc_u32(opc);
            proof {
                assert(tv < 0x4);
            }
            let w = add_field(w, tv, 0x2000_0000);
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = shift_u32(shift_type);
            proof {
                assert(tv < 0x4);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *shift_amount as u32;
            proof {
                assert(tv < 0x40);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `ShiftVariable`.
pub fn enc_shift_variable(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is ShiftVariable,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::ShiftVariable { sf, shift_type, d, n, m } => {
            let w: u32 = 0x1ac0_2000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = shift_u32(shift_type);
            proof {
                assert(tv < 0x4);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `Bitfield`.
pub fn enc_bitfield(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is Bitfield,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::Bitfield { sf, signed, d, n, immr, imms } => {
            let w: u32 = 0x1300_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = bool_u32(!*signed);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x4000_0000);
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *immr as u32;
            proof {
                assert(tv < 0x40);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *imms as u32;
            proof {
                assert(tv < 0x40);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `MoveWide`.
pub fn enc_move_wide(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is MoveWide,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::MoveWide { sf, opcode, d, imm16, hw } => {
            let w: u32 = 0x5280_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = move_wide_u32(opcode);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x2000_0000);
            let tv = *hw as u32;
            proof {
                assert(tv < 0x4);
            }
            let w = add_field(w, tv, 0x20_0000);
            let tv = *imm16 as u32;
            proof {
                assert(tv < 0x1_0000);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `CondSelect`.
pub fn enc_cond_select(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is CondSelect,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } => {
            let w: u32 = 0x1a80_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = bool_u32(*else_inv);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x4000_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *cond as u32;
            proof {
                assert(tv < 0x10);
            }
            let w = add_field(w, tv, 0x1000);
            let tv = bool_u32(*else_inc);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `LoadStoreImm`.
pub fn enc_load_store_imm(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is LoadStoreImm,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => {
            let w: u32 = 0xb900_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x4000_0000);
            let tv = bool_u32(*load);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *imm12 as u32;
            proof {
                assert(tv < 0x1000);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *t as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `LoadStoreReg`.
pub fn enc_load_store_reg(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is LoadStoreReg,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::LoadStoreReg { sf, load, t, n, m, s } => {
            let w: u32 = 0xb820_6800u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x4000_0000);
            let tv = bool_u32(*load);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = bool_u32(*s);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x1000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *t as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FpLoadStoreImm`.
pub fn enc_fp_load_store_imm(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FpLoadStoreImm,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FpLoadStoreImm { load, t, n, imm12 } => {
            let w: u32 = 0xfd00_0000u32;
            let tv = bool_u32(*load);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *imm12 as u32;
            proof {
                assert(tv < 0x1000);
            }
            let w = add_field(w, tv, 0x400);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *t as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FpLoadStoreReg`.
pub fn enc_fp_load_store_reg(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FpLoadStoreReg,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FpLoadStoreReg { load, t, n, m, s } => {
            let w: u32 = 0xfc20_6800u32;
            let tv = bool_u32(*load);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x40_0000);
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = bool_u32(*s);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x1000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *t as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `B`.
pub fn enc_b(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is B,
    ensures
        is_canonical_encoding(out, *i),
{
    proof {
        lemma_signed_fits();
    }
    match i {
        Instr::B { imm26 } => {
            let w: u32 = 0x1400_0000u32;
            let tv = simm26_u32(*imm26);
            proof {
                assert(tv < 0x400_0000);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `BCond`.
pub fn enc_b_cond(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is BCond,
    ensures
        is_canonical_encoding(out, *i),
{
    proof {
        lemma_signed_fits();
    }
    match i {
        Instr::BCond { cond, imm19 } => {
            let w: u32 = 0x5400_0000u32;
            let tv = simm19_u32(*imm19);
            proof {
                assert(tv < 0x8_0000);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *cond as u32;
            proof {
                assert(tv < 0x10);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `CompareBranch`.
pub fn enc_compare_branch(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is CompareBranch,
    ensures
        is_canonical_encoding(out, *i),
{
    proof {
        lemma_signed_fits();
    }
    match i {
        Instr::CompareBranch { sf, iszero, t, imm19 } => {
            let w: u32 = 0x3400_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = bool_u32(!*iszero);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x100_0000);
            let tv = simm19_u32(*imm19);
            proof {
                assert(tv < 0x8_0000);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *t as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `Ret`.
pub fn enc_ret(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is Ret,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::Ret => {
            0xd65f_03c0u32
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FAddSub`.
pub fn enc_f_add_sub(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FAddSub,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FAddSub { sub_op, d, n, m } => {
            let w: u32 = 0x1e60_2800u32;
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = bool_u32(*sub_op);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x1000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FMul`.
pub fn enc_f_mul(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FMul,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FMul { d, n, m } => {
            let w: u32 = 0x1e60_0800u32;
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FDiv`.
pub fn enc_f_div(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FDiv,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FDiv { d, n, m } => {
            let w: u32 = 0x1e60_1800u32;
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FUnary`.
pub fn enc_f_unary(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FUnary,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FUnary { fpop, d, n } => {
            let w: u32 = 0x1e60_4000u32;
            let tv = fp_unary_opc_u32(fpop);
            proof {
                assert(tv < 0x4);
            }
            let w = add_field(w, tv, 0x8000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FCmp`.
pub fn enc_f_cmp(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FCmp,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FCmp { n, m } => {
            let w: u32 = 0x1e60_2000u32;
            let tv = *m as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x20)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `FMovGen`.
pub fn enc_f_mov_gen(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is FMovGen,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::FMovGen { to_fp, d, n } => {
            let w: u32 = 0x9e66_0000u32;
            let tv = bool_u32(*to_fp);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x1_0000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `Scvtf`.
pub fn enc_scvtf(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is Scvtf,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::Scvtf { sf, d, n } => {
            let w: u32 = 0x1e62_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of a valid `Fcvtzs`.
pub fn enc_fcvtzs(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
        i is Fcvtzs,
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::Fcvtzs { sf, d, n } => {
            let w: u32 = 0x1e78_0000u32;
            let tv = width_u32(sf);
            proof {
                assert(tv < 0x2);
            }
            let w = add_field(w, tv, 0x8000_0000);
            let tv = *n as u32;
            proof {
                assert(tv < 0x20);
            }
            let w = add_field(w, tv, 0x20);
            let tv = *d as u32;
            proof {
                assert(tv < 0x20);
            }
            add_field(w, tv, 0x1)
        }
        _ => {
            proof {
                assert(false);
            }
            0
        }
    }
}

/// The canonical encoding of `i`: [`encode`], as a word. Its bytes in memory are
/// `w.to_le_bytes()` ([`word_bytes`]).
pub fn encode_instr(i: &Instr) -> (out: u32)
    requires
        valid_instr(*i),
    ensures
        is_canonical_encoding(out, *i),
{
    match i {
        Instr::AddSubShiftedReg { .. } => enc_add_sub_shifted_reg(i),
        Instr::AddSubImm { .. } => enc_add_sub_imm(i),
        Instr::MulAddSub { .. } => enc_mul_add_sub(i),
        Instr::Div { .. } => enc_div(i),
        Instr::LogicalShiftedReg { .. } => enc_logical_shifted_reg(i),
        Instr::ShiftVariable { .. } => enc_shift_variable(i),
        Instr::Bitfield { .. } => enc_bitfield(i),
        Instr::MoveWide { .. } => enc_move_wide(i),
        Instr::CondSelect { .. } => enc_cond_select(i),
        Instr::LoadStoreImm { .. } => enc_load_store_imm(i),
        Instr::LoadStoreReg { .. } => enc_load_store_reg(i),
        Instr::FpLoadStoreImm { .. } => enc_fp_load_store_imm(i),
        Instr::FpLoadStoreReg { .. } => enc_fp_load_store_reg(i),
        Instr::B { .. } => enc_b(i),
        Instr::BCond { .. } => enc_b_cond(i),
        Instr::CompareBranch { .. } => enc_compare_branch(i),
        Instr::Ret => enc_ret(i),
        Instr::FAddSub { .. } => enc_f_add_sub(i),
        Instr::FMul { .. } => enc_f_mul(i),
        Instr::FDiv { .. } => enc_f_div(i),
        Instr::FUnary { .. } => enc_f_unary(i),
        Instr::FCmp { .. } => enc_f_cmp(i),
        Instr::FMovGen { .. } => enc_f_mov_gen(i),
        Instr::Scvtf { .. } => enc_scvtf(i),
        Instr::Fcvtzs { .. } => enc_fcvtzs(i),
    }
}
} // verus!
