//! Which variant a word belongs to, by its fixed bits.
//!
//! Each variant of [`Instr`] has a mask and a value: the bits of its
//! encoding that no field covers (the opcode bits) must equal the value.
//! [`chain_class`] is the first variant whose bits match. For the encoding
//! of a valid instruction it is the instruction's own variant
//! ([`lemma_class_exact`]), because no two variants' masks and values agree
//! on the bits both fix. That is what lets the decoder ([`super::decoder`])
//! look at one variant only, and what makes the canonical encoding
//! injective ([`super::inverse`]).
//!
//! Each fact about a word built from fields is a bit-vector statement, which
//! the SAT-backed `by(bit_vector)` mode of Verus proves for all values of the
//! fields at once.

#[cfg(verus_only)]
use super::encoder::lemma_signed_fits;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The class of an instruction: its variant's position in [`Instr`].
pub open spec fn class_of(i: Instr) -> int {
    match i {
        Instr::AddSubShiftedReg { .. } => 0,
        Instr::AddSubImm { .. } => 1,
        Instr::MulAddSub { .. } => 2,
        Instr::Div { .. } => 3,
        Instr::LogicalShiftedReg { .. } => 4,
        Instr::ShiftVariable { .. } => 5,
        Instr::Bitfield { .. } => 6,
        Instr::MoveWide { .. } => 7,
        Instr::CondSelect { .. } => 8,
        Instr::LoadStoreImm { .. } => 9,
        Instr::LoadStoreReg { .. } => 10,
        Instr::FpLoadStoreImm { .. } => 11,
        Instr::FpLoadStoreReg { .. } => 12,
        Instr::B { .. } => 13,
        Instr::BCond { .. } => 14,
        Instr::CompareBranch { .. } => 15,
        Instr::Ret => 16,
        Instr::FAddSub { .. } => 17,
        Instr::FMul { .. } => 18,
        Instr::FDiv { .. } => 19,
        Instr::FUnary { .. } => 20,
        Instr::FCmp { .. } => 21,
        Instr::FMovGen { .. } => 22,
        Instr::Scvtf { .. } => 23,
        Instr::Fcvtzs { .. } => 24,
    }
}

/// The number of classes.
pub open spec fn class_count() -> int {
    25
}

/// The class of a word by its fixed bits: the first class whose mask and value match,
/// or the number of classes if none does.
pub open spec fn chain_class(w: u32) -> int {
    if w & 0x1f20_0000 == 0xb00_0000 {
        0
    } else     if w & 0x1f80_0000 == 0x1100_0000 {
        1
    } else     if w & 0x7fe0_0000 == 0x1b00_0000 {
        2
    } else     if w & 0x7fe0_f800 == 0x1ac0_0800 {
        3
    } else     if w & 0x1f20_0000 == 0xa00_0000 {
        4
    } else     if w & 0x7fe0_f000 == 0x1ac0_2000 {
        5
    } else     if w & 0x3f80_0000 == 0x1300_0000 {
        6
    } else     if w & 0x5f80_0000 == 0x5280_0000 {
        7
    } else     if w & 0x3fe0_0800 == 0x1a80_0000 {
        8
    } else     if w & 0xbf80_0000 == 0xb900_0000 {
        9
    } else     if w & 0xbfa0_ec00 == 0xb820_6800 {
        10
    } else     if w & 0xff80_0000 == 0xfd00_0000 {
        11
    } else     if w & 0xffa0_ec00 == 0xfc20_6800 {
        12
    } else     if w & 0xfc00_0000 == 0x1400_0000 {
        13
    } else     if w & 0xff00_0010 == 0x5400_0000 {
        14
    } else     if w & 0x7e00_0000 == 0x3400_0000 {
        15
    } else     if w == 0xd65f_03c0 {
        16
    } else     if w & 0xffe0_ec00 == 0x1e60_2800 {
        17
    } else     if w & 0xffe0_fc00 == 0x1e60_0800 {
        18
    } else     if w & 0xffe0_fc00 == 0x1e60_1800 {
        19
    } else     if w & 0xfffe_7c00 == 0x1e60_4000 {
        20
    } else     if w & 0xffe0_fc1f == 0x1e60_2000 {
        21
    } else     if w & 0xfffe_fc00 == 0x9e66_0000 {
        22
    } else     if w & 0x7fff_fc00 == 0x1e62_0000 {
        23
    } else     if w & 0x7fff_fc00 == 0x1e78_0000 {
        24
    } else {
        25
    }
}

/// Bit-vector fact: a word built from the fields of a `AddSubShiftedReg` has the fixed bits of
/// class 0 and of no other class.
proof fn bv_add_sub_shifted_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32, t7: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x2,
        t3 < 0x4,
        t4 < 0x20,
        t5 < 0x40,
        t6 < 0x20,
        t7 < 0x20,
        w == 0xb00_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x8000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x1_0000u32 + t5 * 0x400u32 + t6 * 0x20u32 + t7,
    ensures
        w & 0x1f20_0000 == 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `AddSubShiftedReg` has class 0.
proof fn class_add_sub_shifted_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is AddSubShiftedReg,
        w as int == encode(i),
    ensures
        chain_class(w) == 0,
{
    if let Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } = i {
        lemma_signed_fits();
        let t0 = b(sub_op) as u32;
        let t1 = b(setflags) as u32;
        let t2 = sf_bit(sf) as u32;
        let t3 = shift_field(shift_type) as u32;
        let t4 = (m as int) as u32;
        let t5 = (shift_amount as int) as u32;
        let t6 = (n as int) as u32;
        let t7 = (d as int) as u32;
        assert(b(sub_op) < 0x2);
        assert(b(setflags) < 0x2);
        assert(sf_bit(sf) < 0x2);
        assert(shift_field(shift_type) < 0x4);
        assert((m as int) < 0x20);
        assert((shift_amount as int) < 0x40);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0xb00_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x8000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x1_0000u32 + t5 * 0x400u32 + t6 * 0x20u32 + t7);
        bv_add_sub_shifted_reg(w, t0, t1, t2, t3, t4, t5, t6, t7);
    }
}

/// Bit-vector fact: a word built from the fields of a `AddSubImm` has the fixed bits of
/// class 1 and of no other class.
proof fn bv_add_sub_imm(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x2,
        t3 < 0x2,
        t4 < 0x1000,
        t5 < 0x20,
        t6 < 0x20,
        w == 0x1100_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x2000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 == 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `AddSubImm` has class 1.
proof fn class_add_sub_imm(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is AddSubImm,
        w as int == encode(i),
    ensures
        chain_class(w) == 1,
{
    if let Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(sub_op) as u32;
        let t2 = b(setflags) as u32;
        let t3 = b(sh) as u32;
        let t4 = (imm12 as int) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(sub_op) < 0x2);
        assert(b(setflags) < 0x2);
        assert(b(sh) < 0x2);
        assert((imm12 as int) < 0x1000);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1100_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x2000_0000u32 + t3 * 0x40_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bv_add_sub_imm(w, t0, t1, t2, t3, t4, t5, t6);
    }
}

/// Bit-vector fact: a word built from the fields of a `MulAddSub` has the fixed bits of
/// class 2 and of no other class.
proof fn bv_mul_add_sub(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x2,
        t3 < 0x20,
        t4 < 0x20,
        t5 < 0x20,
        w == 0x1b00_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x8000u32 + t3 * 0x400u32 + t4 * 0x20u32 + t5,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 == 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `MulAddSub` has class 2.
proof fn class_mul_add_sub(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is MulAddSub,
        w as int == encode(i),
    ensures
        chain_class(w) == 2,
{
    if let Instr::MulAddSub { sf, sub_op, d, n, m, a } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = (m as int) as u32;
        let t2 = b(sub_op) as u32;
        let t3 = (a as int) as u32;
        let t4 = (n as int) as u32;
        let t5 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((m as int) < 0x20);
        assert(b(sub_op) < 0x2);
        assert((a as int) < 0x20);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1b00_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x8000u32 + t3 * 0x400u32 + t4 * 0x20u32 + t5);
        bv_mul_add_sub(w, t0, t1, t2, t3, t4, t5);
    }
}

/// Bit-vector fact: a word built from the fields of a `Div` has the fixed bits of
/// class 3 and of no other class.
proof fn bv_div(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x2,
        t3 < 0x20,
        t4 < 0x20,
        w == 0x1ac0_0800u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 == 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `Div` has class 3.
proof fn class_div(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Div,
        w as int == encode(i),
    ensures
        chain_class(w) == 3,
{
    if let Instr::Div { sf, is_unsigned, d, n, m } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = (m as int) as u32;
        let t2 = b(!is_unsigned) as u32;
        let t3 = (n as int) as u32;
        let t4 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((m as int) < 0x20);
        assert(b(!is_unsigned) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1ac0_0800u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4);
        bv_div(w, t0, t1, t2, t3, t4);
    }
}

/// Bit-vector fact: a word built from the fields of a `LogicalShiftedReg` has the fixed bits of
/// class 4 and of no other class.
proof fn bv_logical_shifted_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x4,
        t1 < 0x2,
        t2 < 0x4,
        t3 < 0x20,
        t4 < 0x40,
        t5 < 0x20,
        t6 < 0x20,
        w == 0xa00_0000u32 + t0 * 0x2000_0000u32 + t1 * 0x8000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 == 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `LogicalShiftedReg` has class 4.
proof fn class_logical_shifted_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is LogicalShiftedReg,
        w as int == encode(i),
    ensures
        chain_class(w) == 4,
{
    if let Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } = i {
        lemma_signed_fits();
        let t0 = logical_opc_field(opc) as u32;
        let t1 = sf_bit(sf) as u32;
        let t2 = shift_field(shift_type) as u32;
        let t3 = (m as int) as u32;
        let t4 = (shift_amount as int) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(logical_opc_field(opc) < 0x4);
        assert(sf_bit(sf) < 0x2);
        assert(shift_field(shift_type) < 0x4);
        assert((m as int) < 0x20);
        assert((shift_amount as int) < 0x40);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0xa00_0000u32 + t0 * 0x2000_0000u32 + t1 * 0x8000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bv_logical_shifted_reg(w, t0, t1, t2, t3, t4, t5, t6);
    }
}

/// Bit-vector fact: a word built from the fields of a `ShiftVariable` has the fixed bits of
/// class 5 and of no other class.
proof fn bv_shift_variable(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x4,
        t3 < 0x20,
        t4 < 0x20,
        w == 0x1ac0_2000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 == 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `ShiftVariable` has class 5.
proof fn class_shift_variable(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is ShiftVariable,
        w as int == encode(i),
    ensures
        chain_class(w) == 5,
{
    if let Instr::ShiftVariable { sf, shift_type, d, n, m } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = (m as int) as u32;
        let t2 = shift_field(shift_type) as u32;
        let t3 = (n as int) as u32;
        let t4 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((m as int) < 0x20);
        assert(shift_field(shift_type) < 0x4);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1ac0_2000u32 + t0 * 0x8000_0000u32 + t1 * 0x1_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4);
        bv_shift_variable(w, t0, t1, t2, t3, t4);
    }
}

/// Bit-vector fact: a word built from the fields of a `Bitfield` has the fixed bits of
/// class 6 and of no other class.
proof fn bv_bitfield(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x2,
        t3 < 0x40,
        t4 < 0x40,
        t5 < 0x20,
        t6 < 0x20,
        w == 0x1300_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 == 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `Bitfield` has class 6.
proof fn class_bitfield(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Bitfield,
        w as int == encode(i),
    ensures
        chain_class(w) == 6,
{
    if let Instr::Bitfield { sf, signed, d, n, immr, imms } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(!signed) as u32;
        let t2 = sf_bit(sf) as u32;
        let t3 = (immr as int) as u32;
        let t4 = (imms as int) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(!signed) < 0x2);
        assert(sf_bit(sf) < 0x2);
        assert((immr as int) < 0x40);
        assert((imms as int) < 0x40);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1300_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x40_0000u32 + t3 * 0x1_0000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bv_bitfield(w, t0, t1, t2, t3, t4, t5, t6);
    }
}

/// Bit-vector fact: a word built from the fields of a `MoveWide` has the fixed bits of
/// class 7 and of no other class.
proof fn bv_move_wide(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x4,
        t3 < 0x1_0000,
        t4 < 0x20,
        w == 0x5280_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x20_0000u32 + t3 * 0x20u32 + t4,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 == 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `MoveWide` has class 7.
proof fn class_move_wide(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is MoveWide,
        w as int == encode(i),
    ensures
        chain_class(w) == 7,
{
    if let Instr::MoveWide { sf, opcode, d, imm16, hw } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(opcode is K) as u32;
        let t2 = (hw as int) as u32;
        let t3 = (imm16 as int) as u32;
        let t4 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(opcode is K) < 0x2);
        assert((hw as int) < 0x4);
        assert((imm16 as int) < 0x1_0000);
        assert((d as int) < 0x20);
        assert(w == 0x5280_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x2000_0000u32 + t2 * 0x20_0000u32 + t3 * 0x20u32 + t4);
        bv_move_wide(w, t0, t1, t2, t3, t4);
    }
}

/// Bit-vector fact: a word built from the fields of a `CondSelect` has the fixed bits of
/// class 8 and of no other class.
proof fn bv_cond_select(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32, t6: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x20,
        t3 < 0x10,
        t4 < 0x2,
        t5 < 0x20,
        t6 < 0x20,
        w == 0x1a80_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 == 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `CondSelect` has class 8.
proof fn class_cond_select(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is CondSelect,
        w as int == encode(i),
    ensures
        chain_class(w) == 8,
{
    if let Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(else_inv) as u32;
        let t2 = (m as int) as u32;
        let t3 = (cond as int) as u32;
        let t4 = b(else_inc) as u32;
        let t5 = (n as int) as u32;
        let t6 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(else_inv) < 0x2);
        assert((m as int) < 0x20);
        assert((cond as int) < 0x10);
        assert(b(else_inc) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1a80_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x4000_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x400u32 + t5 * 0x20u32 + t6);
        bv_cond_select(w, t0, t1, t2, t3, t4, t5, t6);
    }
}

/// Bit-vector fact: a word built from the fields of a `LoadStoreImm` has the fixed bits of
/// class 9 and of no other class.
proof fn bv_load_store_imm(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x1000,
        t3 < 0x20,
        t4 < 0x20,
        w == 0xb900_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 == 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `LoadStoreImm` has class 9.
proof fn class_load_store_imm(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is LoadStoreImm,
        w as int == encode(i),
    ensures
        chain_class(w) == 9,
{
    if let Instr::LoadStoreImm { sf, load, t, n, imm12 } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(load) as u32;
        let t2 = (imm12 as int) as u32;
        let t3 = (n as int) as u32;
        let t4 = (t as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(load) < 0x2);
        assert((imm12 as int) < 0x1000);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xb900_0000u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x400u32 + t3 * 0x20u32 + t4);
        bv_load_store_imm(w, t0, t1, t2, t3, t4);
    }
}

/// Bit-vector fact: a word built from the fields of a `LoadStoreReg` has the fixed bits of
/// class 10 and of no other class.
proof fn bv_load_store_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32, t5: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x20,
        t3 < 0x2,
        t4 < 0x20,
        t5 < 0x20,
        w == 0xb820_6800u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x20u32 + t5,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 == 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `LoadStoreReg` has class 10.
proof fn class_load_store_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is LoadStoreReg,
        w as int == encode(i),
    ensures
        chain_class(w) == 10,
{
    if let Instr::LoadStoreReg { sf, load, t, n, m, s } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(load) as u32;
        let t2 = (m as int) as u32;
        let t3 = b(s) as u32;
        let t4 = (n as int) as u32;
        let t5 = (t as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(load) < 0x2);
        assert((m as int) < 0x20);
        assert(b(s) < 0x2);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xb820_6800u32 + t0 * 0x4000_0000u32 + t1 * 0x40_0000u32 + t2 * 0x1_0000u32 + t3 * 0x1000u32 + t4 * 0x20u32 + t5);
        bv_load_store_reg(w, t0, t1, t2, t3, t4, t5);
    }
}

/// Bit-vector fact: a word built from the fields of a `FpLoadStoreImm` has the fixed bits of
/// class 11 and of no other class.
proof fn bv_fp_load_store_imm(w: u32, t0: u32, t1: u32, t2: u32, t3: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x1000,
        t2 < 0x20,
        t3 < 0x20,
        w == 0xfd00_0000u32 + t0 * 0x40_0000u32 + t1 * 0x400u32 + t2 * 0x20u32 + t3,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 == 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FpLoadStoreImm` has class 11.
proof fn class_fp_load_store_imm(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FpLoadStoreImm,
        w as int == encode(i),
    ensures
        chain_class(w) == 11,
{
    if let Instr::FpLoadStoreImm { load, t, n, imm12 } = i {
        lemma_signed_fits();
        let t0 = b(load) as u32;
        let t1 = (imm12 as int) as u32;
        let t2 = (n as int) as u32;
        let t3 = (t as int) as u32;
        assert(b(load) < 0x2);
        assert((imm12 as int) < 0x1000);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xfd00_0000u32 + t0 * 0x40_0000u32 + t1 * 0x400u32 + t2 * 0x20u32 + t3);
        bv_fp_load_store_imm(w, t0, t1, t2, t3);
    }
}

/// Bit-vector fact: a word built from the fields of a `FpLoadStoreReg` has the fixed bits of
/// class 12 and of no other class.
proof fn bv_fp_load_store_reg(w: u32, t0: u32, t1: u32, t2: u32, t3: u32, t4: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x2,
        t3 < 0x20,
        t4 < 0x20,
        w == 0xfc20_6800u32 + t0 * 0x40_0000u32 + t1 * 0x1_0000u32 + t2 * 0x1000u32 + t3 * 0x20u32 + t4,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 == 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FpLoadStoreReg` has class 12.
proof fn class_fp_load_store_reg(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FpLoadStoreReg,
        w as int == encode(i),
    ensures
        chain_class(w) == 12,
{
    if let Instr::FpLoadStoreReg { load, t, n, m, s } = i {
        lemma_signed_fits();
        let t0 = b(load) as u32;
        let t1 = (m as int) as u32;
        let t2 = b(s) as u32;
        let t3 = (n as int) as u32;
        let t4 = (t as int) as u32;
        assert(b(load) < 0x2);
        assert((m as int) < 0x20);
        assert(b(s) < 0x2);
        assert((n as int) < 0x20);
        assert((t as int) < 0x20);
        assert(w == 0xfc20_6800u32 + t0 * 0x40_0000u32 + t1 * 0x1_0000u32 + t2 * 0x1000u32 + t3 * 0x20u32 + t4);
        bv_fp_load_store_reg(w, t0, t1, t2, t3, t4);
    }
}

/// Bit-vector fact: a word built from the fields of a `B` has the fixed bits of
/// class 13 and of no other class.
proof fn bv_b(w: u32, t0: u32)
    by (bit_vector)
    requires
        t0 < 0x400_0000,
        w == 0x1400_0000u32 + t0,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 == 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `B` has class 13.
proof fn class_b(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is B,
        w as int == encode(i),
    ensures
        chain_class(w) == 13,
{
    if let Instr::B { imm26 } = i {
        lemma_signed_fits();
        let t0 = ((imm26 as int) % 0x400_0000) as u32;
        assert(((imm26 as int) % 0x400_0000) < 0x400_0000);
        assert(w == 0x1400_0000u32 + t0);
        bv_b(w, t0);
    }
}

/// Bit-vector fact: a word built from the fields of a `BCond` has the fixed bits of
/// class 14 and of no other class.
proof fn bv_b_cond(w: u32, t0: u32, t1: u32)
    by (bit_vector)
    requires
        t0 < 0x8_0000,
        t1 < 0x10,
        w == 0x5400_0000u32 + t0 * 0x20u32 + t1,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 == 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `BCond` has class 14.
proof fn class_b_cond(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is BCond,
        w as int == encode(i),
    ensures
        chain_class(w) == 14,
{
    if let Instr::BCond { cond, imm19 } = i {
        lemma_signed_fits();
        let t0 = ((imm19 as int) % 0x8_0000) as u32;
        let t1 = (cond as int) as u32;
        assert(((imm19 as int) % 0x8_0000) < 0x8_0000);
        assert((cond as int) < 0x10);
        assert(w == 0x5400_0000u32 + t0 * 0x20u32 + t1);
        bv_b_cond(w, t0, t1);
    }
}

/// Bit-vector fact: a word built from the fields of a `CompareBranch` has the fixed bits of
/// class 15 and of no other class.
proof fn bv_compare_branch(w: u32, t0: u32, t1: u32, t2: u32, t3: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x2,
        t2 < 0x8_0000,
        t3 < 0x20,
        w == 0x3400_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x100_0000u32 + t2 * 0x20u32 + t3,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 == 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `CompareBranch` has class 15.
proof fn class_compare_branch(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is CompareBranch,
        w as int == encode(i),
    ensures
        chain_class(w) == 15,
{
    if let Instr::CompareBranch { sf, iszero, t, imm19 } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = b(!iszero) as u32;
        let t2 = ((imm19 as int) % 0x8_0000) as u32;
        let t3 = (t as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert(b(!iszero) < 0x2);
        assert(((imm19 as int) % 0x8_0000) < 0x8_0000);
        assert((t as int) < 0x20);
        assert(w == 0x3400_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x100_0000u32 + t2 * 0x20u32 + t3);
        bv_compare_branch(w, t0, t1, t2, t3);
    }
}

/// Bit-vector fact: a word built from the fields of a `Ret` has the fixed bits of
/// class 16 and of no other class.
proof fn bv_ret(w: u32)
    by (bit_vector)
    requires
        true,
        w == 0xd65f_03c0u32,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff == 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `Ret` has class 16.
proof fn class_ret(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Ret,
        w as int == encode(i),
    ensures
        chain_class(w) == 16,
{
    if let Instr::Ret = i {
        lemma_signed_fits();
        assert(w == 0xd65f_03c0u32);
        bv_ret(w);
    }
}

/// Bit-vector fact: a word built from the fields of a `FAddSub` has the fixed bits of
/// class 17 and of no other class.
proof fn bv_f_add_sub(w: u32, t0: u32, t1: u32, t2: u32, t3: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x2,
        t2 < 0x20,
        t3 < 0x20,
        w == 0x1e60_2800u32 + t0 * 0x1_0000u32 + t1 * 0x1000u32 + t2 * 0x20u32 + t3,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 == 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FAddSub` has class 17.
proof fn class_f_add_sub(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FAddSub,
        w as int == encode(i),
    ensures
        chain_class(w) == 17,
{
    if let Instr::FAddSub { sub_op, d, n, m } = i {
        lemma_signed_fits();
        let t0 = (m as int) as u32;
        let t1 = b(sub_op) as u32;
        let t2 = (n as int) as u32;
        let t3 = (d as int) as u32;
        assert((m as int) < 0x20);
        assert(b(sub_op) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_2800u32 + t0 * 0x1_0000u32 + t1 * 0x1000u32 + t2 * 0x20u32 + t3);
        bv_f_add_sub(w, t0, t1, t2, t3);
    }
}

/// Bit-vector fact: a word built from the fields of a `FMul` has the fixed bits of
/// class 18 and of no other class.
proof fn bv_f_mul(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e60_0800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 == 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FMul` has class 18.
proof fn class_f_mul(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FMul,
        w as int == encode(i),
    ensures
        chain_class(w) == 18,
{
    if let Instr::FMul { d, n, m } = i {
        lemma_signed_fits();
        let t0 = (m as int) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert((m as int) < 0x20);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_0800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2);
        bv_f_mul(w, t0, t1, t2);
    }
}

/// Bit-vector fact: a word built from the fields of a `FDiv` has the fixed bits of
/// class 19 and of no other class.
proof fn bv_f_div(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e60_1800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 == 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FDiv` has class 19.
proof fn class_f_div(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FDiv,
        w as int == encode(i),
    ensures
        chain_class(w) == 19,
{
    if let Instr::FDiv { d, n, m } = i {
        lemma_signed_fits();
        let t0 = (m as int) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert((m as int) < 0x20);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_1800u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2);
        bv_f_div(w, t0, t1, t2);
    }
}

/// Bit-vector fact: a word built from the fields of a `FUnary` has the fixed bits of
/// class 20 and of no other class.
proof fn bv_f_unary(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x4,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e60_4000u32 + t0 * 0x8000u32 + t1 * 0x20u32 + t2,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 == 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FUnary` has class 20.
proof fn class_f_unary(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FUnary,
        w as int == encode(i),
    ensures
        chain_class(w) == 20,
{
    if let Instr::FUnary { fpop, d, n } = i {
        lemma_signed_fits();
        let t0 = fp_unary_opc_field(fpop) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(fp_unary_opc_field(fpop) < 0x4);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e60_4000u32 + t0 * 0x8000u32 + t1 * 0x20u32 + t2);
        bv_f_unary(w, t0, t1, t2);
    }
}

/// Bit-vector fact: a word built from the fields of a `FCmp` has the fixed bits of
/// class 21 and of no other class.
proof fn bv_f_cmp(w: u32, t0: u32, t1: u32)
    by (bit_vector)
    requires
        t0 < 0x20,
        t1 < 0x20,
        w == 0x1e60_2000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f == 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FCmp` has class 21.
proof fn class_f_cmp(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FCmp,
        w as int == encode(i),
    ensures
        chain_class(w) == 21,
{
    if let Instr::FCmp { n, m } = i {
        lemma_signed_fits();
        let t0 = (m as int) as u32;
        let t1 = (n as int) as u32;
        assert((m as int) < 0x20);
        assert((n as int) < 0x20);
        assert(w == 0x1e60_2000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32);
        bv_f_cmp(w, t0, t1);
    }
}

/// Bit-vector fact: a word built from the fields of a `FMovGen` has the fixed bits of
/// class 22 and of no other class.
proof fn bv_f_mov_gen(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x9e66_0000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 == 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `FMovGen` has class 22.
proof fn class_f_mov_gen(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is FMovGen,
        w as int == encode(i),
    ensures
        chain_class(w) == 22,
{
    if let Instr::FMovGen { to_fp, d, n } = i {
        lemma_signed_fits();
        let t0 = b(to_fp) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(b(to_fp) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x9e66_0000u32 + t0 * 0x1_0000u32 + t1 * 0x20u32 + t2);
        bv_f_mov_gen(w, t0, t1, t2);
    }
}

/// Bit-vector fact: a word built from the fields of a `Scvtf` has the fixed bits of
/// class 23 and of no other class.
proof fn bv_scvtf(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e62_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 == 0x1e62_0000,
        w & 0x7fff_fc00 != 0x1e78_0000,
{
}

/// The word of a valid `Scvtf` has class 23.
proof fn class_scvtf(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Scvtf,
        w as int == encode(i),
    ensures
        chain_class(w) == 23,
{
    if let Instr::Scvtf { sf, d, n } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e62_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2);
        bv_scvtf(w, t0, t1, t2);
    }
}

/// Bit-vector fact: a word built from the fields of a `Fcvtzs` has the fixed bits of
/// class 24 and of no other class.
proof fn bv_fcvtzs(w: u32, t0: u32, t1: u32, t2: u32)
    by (bit_vector)
    requires
        t0 < 0x2,
        t1 < 0x20,
        t2 < 0x20,
        w == 0x1e78_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2,
    ensures
        w & 0x1f20_0000 != 0xb00_0000,
        w & 0x1f80_0000 != 0x1100_0000,
        w & 0x7fe0_0000 != 0x1b00_0000,
        w & 0x7fe0_f800 != 0x1ac0_0800,
        w & 0x1f20_0000 != 0xa00_0000,
        w & 0x7fe0_f000 != 0x1ac0_2000,
        w & 0x3f80_0000 != 0x1300_0000,
        w & 0x5f80_0000 != 0x5280_0000,
        w & 0x3fe0_0800 != 0x1a80_0000,
        w & 0xbf80_0000 != 0xb900_0000,
        w & 0xbfa0_ec00 != 0xb820_6800,
        w & 0xff80_0000 != 0xfd00_0000,
        w & 0xffa0_ec00 != 0xfc20_6800,
        w & 0xfc00_0000 != 0x1400_0000,
        w & 0xff00_0010 != 0x5400_0000,
        w & 0x7e00_0000 != 0x3400_0000,
        w & 0xffff_ffff != 0xd65f_03c0,
        w & 0xffe0_ec00 != 0x1e60_2800,
        w & 0xffe0_fc00 != 0x1e60_0800,
        w & 0xffe0_fc00 != 0x1e60_1800,
        w & 0xfffe_7c00 != 0x1e60_4000,
        w & 0xffe0_fc1f != 0x1e60_2000,
        w & 0xfffe_fc00 != 0x9e66_0000,
        w & 0x7fff_fc00 != 0x1e62_0000,
        w & 0x7fff_fc00 == 0x1e78_0000,
{
}

/// The word of a valid `Fcvtzs` has class 24.
proof fn class_fcvtzs(w: u32, i: Instr)
    requires
        valid_instr(i),
        i is Fcvtzs,
        w as int == encode(i),
    ensures
        chain_class(w) == 24,
{
    if let Instr::Fcvtzs { sf, d, n } = i {
        lemma_signed_fits();
        let t0 = sf_bit(sf) as u32;
        let t1 = (n as int) as u32;
        let t2 = (d as int) as u32;
        assert(sf_bit(sf) < 0x2);
        assert((n as int) < 0x20);
        assert((d as int) < 0x20);
        assert(w == 0x1e78_0000u32 + t0 * 0x8000_0000u32 + t1 * 0x20u32 + t2);
        bv_fcvtzs(w, t0, t1, t2);
    }
}

/// The class of the word of a valid instruction is the instruction's class.
pub proof fn lemma_class_exact(w: u32, i: Instr)
    requires
        valid_instr(i),
        w as int == encode(i),
    ensures
        chain_class(w) == class_of(i),
{
    match i {
        Instr::AddSubShiftedReg { .. } => class_add_sub_shifted_reg(w, i),
        Instr::AddSubImm { .. } => class_add_sub_imm(w, i),
        Instr::MulAddSub { .. } => class_mul_add_sub(w, i),
        Instr::Div { .. } => class_div(w, i),
        Instr::LogicalShiftedReg { .. } => class_logical_shifted_reg(w, i),
        Instr::ShiftVariable { .. } => class_shift_variable(w, i),
        Instr::Bitfield { .. } => class_bitfield(w, i),
        Instr::MoveWide { .. } => class_move_wide(w, i),
        Instr::CondSelect { .. } => class_cond_select(w, i),
        Instr::LoadStoreImm { .. } => class_load_store_imm(w, i),
        Instr::LoadStoreReg { .. } => class_load_store_reg(w, i),
        Instr::FpLoadStoreImm { .. } => class_fp_load_store_imm(w, i),
        Instr::FpLoadStoreReg { .. } => class_fp_load_store_reg(w, i),
        Instr::B { .. } => class_b(w, i),
        Instr::BCond { .. } => class_b_cond(w, i),
        Instr::CompareBranch { .. } => class_compare_branch(w, i),
        Instr::Ret => class_ret(w, i),
        Instr::FAddSub { .. } => class_f_add_sub(w, i),
        Instr::FMul { .. } => class_f_mul(w, i),
        Instr::FDiv { .. } => class_f_div(w, i),
        Instr::FUnary { .. } => class_f_unary(w, i),
        Instr::FCmp { .. } => class_f_cmp(w, i),
        Instr::FMovGen { .. } => class_f_mov_gen(w, i),
        Instr::Scvtf { .. } => class_scvtf(w, i),
        Instr::Fcvtzs { .. } => class_fcvtzs(w, i),
    }
}

} // verus!
