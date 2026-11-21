//! Small examples evaluated against the spec: evidence that the canonical
//! encoding and some of the semantics compute what an assembler and the
//! programmer's reading of the instruction say.
//!
//! The words are the usual ones for these instructions (what any AArch64
//! assembler emits). They are not copied from the Arm Architecture
//! Reference Manual, which the author of the primary transcription does not
//! read. The decoder differential against `yaxpeax-arm` (J.4) is the
//! thorough check of the encoding; these are a smoke test of it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `add x0, x1, x2` is `8B020020`, `subs w3, w4, #1` is `71000483`, and
/// `cmp x0, x1` (`subs xzr, x0, x1`) is `EB01001F`.
pub proof fn example_add_sub()
    ensures
        encode(
            Instr::AddSubShiftedReg {
                sf: Width::W64,
                sub_op: false,
                setflags: false,
                d: 0,
                n: 1,
                m: 2,
                shift_type: ShiftType::Lsl,
                shift_amount: 0,
            },
        ) == 0x8B02_0020,
        encode(
            Instr::AddSubImm {
                sf: Width::W32,
                sub_op: true,
                setflags: true,
                d: 3,
                n: 4,
                imm12: 1,
                sh: false,
            },
        ) == 0x7100_0483,
        encode(
            Instr::AddSubShiftedReg {
                sf: Width::W64,
                sub_op: true,
                setflags: true,
                d: 31,
                n: 0,
                m: 1,
                shift_type: ShiftType::Lsl,
                shift_amount: 0,
            },
        ) == 0xEB01_001F,
{
}

/// `mov x0, x1` (`orr x0, xzr, x1`) is `AA0103E0`; `lsl x0, x1, #3`
/// (`ubfm x0, x1, #61, #60`) is `D37DF020`.
pub proof fn example_logic_shift()
    ensures
        encode(
            Instr::LogicalShiftedReg {
                sf: Width::W64,
                opc: LogicalOpc::Orr,
                d: 0,
                n: 31,
                m: 1,
                shift_type: ShiftType::Lsl,
                shift_amount: 0,
            },
        ) == 0xAA01_03E0,
        encode(Instr::Bitfield { sf: Width::W64, signed: false, d: 0, n: 1, immr: 61, imms: 60 })
            == 0xD37D_F020,
{
}

/// `movz x0, #0x1234` is `D2824680`; `movk x0, #0x5678, lsl #16` is
/// `F2AACF00`; `mul x0, x1, x2` (`madd x0, x1, x2, xzr`) is `9B027C20`;
/// `sdiv x0, x1, x2` is `9AC20C20`; `cset w0, eq` (`csinc w0, wzr, wzr,
/// ne`) is `1A9F17E0`.
pub proof fn example_constants_mul_select()
    ensures
        encode(
            Instr::MoveWide { sf: Width::W64, opcode: MoveWideOp::Z, d: 0, imm16: 0x1234, hw: 0 },
        ) == 0xD282_4680,
        encode(
            Instr::MoveWide { sf: Width::W64, opcode: MoveWideOp::K, d: 0, imm16: 0x5678, hw: 1 },
        ) == 0xF2AA_CF00,
        encode(Instr::MulAddSub { sf: Width::W64, sub_op: false, d: 0, n: 1, m: 2, a: 31 })
            == 0x9B02_7C20,
        encode(Instr::Div { sf: Width::W64, is_unsigned: false, d: 0, n: 1, m: 2 }) == 0x9AC2_0C20,
        encode(
            Instr::CondSelect {
                sf: Width::W32,
                else_inv: false,
                else_inc: true,
                d: 0,
                n: 31,
                m: 31,
                cond: 1,
            },
        ) == 0x1A9F_17E0,
{
}

/// `ldr x0, [x1, #8]` is `F9400420`; `str w2, [x3]` is `B9000062`;
/// `ldr x0, [x1, x2, lsl #3]` is `F8627820`; `ldr d0, [x1, #16]` is
/// `FD400820`.
pub proof fn example_loads_stores()
    ensures
        encode(Instr::LoadStoreImm { sf: Width::W64, load: true, t: 0, n: 1, imm12: 1 })
            == 0xF940_0420,
        encode(Instr::LoadStoreImm { sf: Width::W32, load: false, t: 2, n: 3, imm12: 0 })
            == 0xB900_0062,
        encode(Instr::LoadStoreReg { sf: Width::W64, load: true, t: 0, n: 1, m: 2, s: true })
            == 0xF862_7820,
        encode(Instr::FpLoadStoreImm { load: true, t: 0, n: 1, imm12: 2 }) == 0xFD40_0820,
{
}

/// `b .` is `14000000`; `b.eq .+8` is `54000040`; `cbz x0, .-4` is
/// `B4FFFFE0`; `ret` is `D65F03C0`.
pub proof fn example_branches()
    ensures
        encode(Instr::B { imm26: 0 }) == 0x1400_0000,
        encode(Instr::BCond { cond: 0, imm19: 2 }) == 0x5400_0040,
        encode(Instr::CompareBranch { sf: Width::W64, iszero: true, t: 0, imm19: -1i32 })
            == 0xB4FF_FFE0,
        encode(Instr::Ret) == 0xD65F_03C0,
{
}

/// `fadd d0, d1, d2` is `1E622820`; `fmul` `1E620820`; `fdiv`
/// `1E621820`; `fsqrt d0, d1` `1E61C020`; `fneg d0, d1` `1E614020`;
/// `fcmp d0, d1` `1E612000`; `fmov x0, d1` `9E660020`; `fmov d0, x1`
/// `9E670020`; `scvtf d0, x1` `9E620020`; `fcvtzs x0, d1` `9E780020`.
pub proof fn example_fp()
    ensures
        encode(Instr::FAddSub { sub_op: false, d: 0, n: 1, m: 2 }) == 0x1E62_2820,
        encode(Instr::FMul { d: 0, n: 1, m: 2 }) == 0x1E62_0820,
        encode(Instr::FDiv { d: 0, n: 1, m: 2 }) == 0x1E62_1820,
        encode(Instr::FUnary { fpop: FPUnaryOp::Sqrt, d: 0, n: 1 }) == 0x1E61_C020,
        encode(Instr::FUnary { fpop: FPUnaryOp::Neg, d: 0, n: 1 }) == 0x1E61_4020,
        encode(Instr::FCmp { n: 0, m: 1 }) == 0x1E61_2000,
        encode(Instr::FMovGen { to_fp: false, d: 0, n: 1 }) == 0x9E66_0020,
        encode(Instr::FMovGen { to_fp: true, d: 0, n: 1 }) == 0x9E67_0020,
        encode(Instr::Scvtf { sf: Width::W64, d: 0, n: 1 }) == 0x9E62_0020,
        encode(Instr::Fcvtzs { sf: Width::W64, d: 0, n: 1 }) == 0x9E78_0020,
{
}

/// `AddWithCarry` on 32 bits: `0xFFFFFFFF + 1` is 0 with `Z` and `C` set
/// (`nzcv = 0b0110`); `0x7FFFFFFF + 1` is `0x80000000` with `N` and `V` set
/// (`0b1001`).
pub proof fn example_add_with_carry()
    ensures
        add_with_carry(32, 0xFFFF_FFFF, 1, 0) == (0int, 0b0110int),
        add_with_carry(32, 0x7FFF_FFFF, 1, 0) == (0x8000_0000int, 0b1001int),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(p2(32) == 0x1_0000_0000);
    assert(p2(31) == 0x8000_0000);
    assert(p2(0) == 1);
    assert(trunc(32, 0x1_0000_0000) == 0);
    assert(sint(32, 0xFFFF_FFFF) == -1);
    assert(sint(32, 0x8000_0000) == -0x8000_0000);
    assert(sint(32, 0x7FFF_FFFF) == 0x7FFF_FFFF);
    assert(bit(0, 31) == 0);
    assert(bit(0x8000_0000, 31) == 1);
}

/// `ConditionHolds`: `EQ` (0) is `Z`, `NE` (1) its negation, `GE` (10) is
/// `N == V`.
pub proof fn example_condition_holds(s: State)
    ensures
        condition_holds(s, 0) == s.flag_z,
        condition_holds(s, 1) == !s.flag_z,
        condition_holds(s, 10) == (s.flag_n == s.flag_v),
{
}

} // verus!
