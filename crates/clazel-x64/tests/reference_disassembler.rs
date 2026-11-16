//! The reference disassembler builds and decodes (docs/phases/jit.md item J.2).
//!
//! `iced-x86` is a test dependency only (class `test` in
//! docs/DEPENDENCIES.md). Item J.3's decoder differential will compare it with
//! `clazel-x64` on every encoding of the subset; this test only shows that it
//! is wired in and answers for one instruction of each kind the subset has.

use iced_x86::{Code, Decoder, DecoderOptions, Mnemonic};

fn decode(bytes: &[u8]) -> (Mnemonic, usize) {
    let mut decoder = Decoder::new(64, bytes, DecoderOptions::NONE);
    let inst = decoder.decode();
    (inst.mnemonic(), inst.len())
}

#[test]
fn add_rax_rbx() {
    // REX.W 01 /r: add r/m64, r64.
    assert_eq!(decode(&[0x48, 0x01, 0xd8]), (Mnemonic::Add, 3));
}

#[test]
fn jmp_rel32_and_ret() {
    assert_eq!(decode(&[0xe9, 0x10, 0x00, 0x00, 0x00]), (Mnemonic::Jmp, 5));
    assert_eq!(decode(&[0xc3]), (Mnemonic::Ret, 1));
}

#[test]
fn addsd_xmm0_xmm1() {
    // F2 0F 58 /r: addsd xmm1, xmm2/m64.
    assert_eq!(decode(&[0xf2, 0x0f, 0x58, 0xc1]), (Mnemonic::Addsd, 4));
}

#[test]
fn syscall_is_outside_the_subset_but_decodes() {
    let mut decoder = Decoder::new(64, &[0x0f, 0x05], DecoderOptions::NONE);
    assert_eq!(decoder.decode().code(), Code::Syscall);
}
