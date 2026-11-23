//! Small examples evaluated against the spec: evidence that the canonical
//! encoding and the semantics compute what an assembler and the programmer's
//! reading of the instruction say.
//!
//! The byte strings are the usual ones for the instructions (they are what
//! any x86-64 assembler emits for these forms, with the `mod = 10` SIB
//! memory operand the canonical encoding fixes). They are not copied from
//! the Intel SDM, which the author of the primary transcription does not
//! read. The decoder differential against `iced-x86` (J.3) is the thorough
//! check of the encoding; these are a smoke test of it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `add rax, rbx` is `48 01 D8`.
pub proof fn example_add_rax_rbx()
    ensures
        encode(Instr::AluRR { alu: AluOp::Add, sz: Size::W64, dst: 0, src: 3 })
            =~= seq![0x48u8, 0x01, 0xD8],
{
    reveal_with_fuel(le_bytes, 5);
}

/// `mov rax, [rbx + rcx*4 + 0x10]` with the fixed `mod = 10` SIB form is
/// `48 8B 84 8B 10 00 00 00`.
pub proof fn example_mov_load()
    ensures
        encode(
            Instr::MovLoad {
                sz: Size::W64,
                dst: 0,
                mem: Mem { base: 3, index: Some(Index { reg: 1, scale: 2 }), disp: 0x10 },
            },
        ) =~= seq![0x48u8, 0x8B, 0x84, 0x8B, 0x10, 0x00, 0x00, 0x00],
{
    reveal_with_fuel(le_bytes, 5);
}

/// `mov r8d, 0x12345678` is `41 B8 78 56 34 12`.
pub proof fn example_mov_imm32_r8()
    ensures
        encode(Instr::MovImm32 { dst: 8, imm_u32: 0x12345678 }) =~= seq![
            0x41u8, 0xB8, 0x78, 0x56, 0x34, 0x12,
        ],
{
    reveal_with_fuel(le_bytes, 5);
}

/// `sete sil` needs a `REX` byte: `40 0F 94 C6`.
pub proof fn example_sete_sil()
    ensures
        encode(Instr::Setcc { cc: 4, dst: 6 }) =~= seq![0x40u8, 0x0F, 0x94, 0xC6],
{
}

/// `addsd xmm1, xmm2` is `F2 0F 58 CA`.
pub proof fn example_addsd()
    ensures
        encode(Instr::FpArith { fop: BinOp::Add, dst: 1, xsrc: XmmSrc::Reg(2) }) =~= seq![
            0xF2u8, 0x0F, 0x58, 0xCA,
        ],
{
}

/// `movq xmm0, rax` is `66 48 0F 6E C0`.
pub proof fn example_movq_to_xmm()
    ensures
        encode(Instr::MovqToXmm { dst: 0, src: 0 }) =~= seq![0x66u8, 0x48, 0x0F, 0x6E, 0xC0],
{
}

/// `ret` is `C3` and `jmp +0` is `E9 00 00 00 00`.
pub proof fn example_ret_jmp()
    ensures
        encode(Instr::Ret) =~= seq![0xC3u8],
        encode(Instr::Jmp { rel: 0 }) =~= seq![0xE9u8, 0, 0, 0, 0],
{
    reveal_with_fuel(le_bytes, 5);
}

} // verus!
