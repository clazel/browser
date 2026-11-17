//! The reference disassembler builds and decodes (docs/phases/jit.md item J.2).
//!
//! `yaxpeax-x86` is a test dependency only (class `test` in
//! docs/DEPENDENCIES.md). Item J.3's decoder differential will compare it with
//! `clazel-x64` on every encoding of the subset; this test only shows that it
//! is wired in and answers for one instruction of each kind the subset has.
//! It replaced `iced-x86`, whose decoder Miri reports as undefined behaviour
//! under Stacked Borrows (iced-x86 1.22.0, `decoder/handlers/legacy.rs:2006`).

use yaxpeax_arch::{Decoder, LengthedInstruction, U8Reader};
use yaxpeax_x86::long_mode::{InstDecoder, Opcode};

fn decode(bytes: &[u8]) -> Option<(Opcode, u64)> {
    let mut reader = U8Reader::new(bytes);
    InstDecoder::default()
        .decode(&mut reader)
        .ok()
        .map(|inst| (inst.opcode(), inst.len().to_const()))
}

#[test]
fn add_rax_rbx() {
    // REX.W 01 /r: add r/m64, r64.
    assert_eq!(decode(&[0x48, 0x01, 0xd8]), Some((Opcode::ADD, 3)));
}

#[test]
fn jmp_rel32_and_ret() {
    assert_eq!(
        decode(&[0xe9, 0x10, 0x00, 0x00, 0x00]),
        Some((Opcode::JMP, 5))
    );
    assert_eq!(decode(&[0xc3]), Some((Opcode::RETURN, 1)));
}

#[test]
fn addsd_xmm0_xmm1() {
    // F2 0F 58 /r: addsd xmm1, xmm2/m64.
    assert_eq!(decode(&[0xf2, 0x0f, 0x58, 0xc1]), Some((Opcode::ADDSD, 4)));
}

#[test]
fn syscall_is_outside_the_subset_but_decodes() {
    assert_eq!(decode(&[0x0f, 0x05]), Some((Opcode::SYSCALL, 2)));
}
