//! The reference disassembler builds and decodes (docs/phases/jit.md item J.2).
//!
//! `yaxpeax-arm` is a test dependency only (class `test` in
//! docs/DEPENDENCIES.md). Item J.4's decoder differential will compare it with
//! `clazel-a64` on every encoding of the subset; this test only shows that it
//! is wired in and answers for one instruction of each kind the subset has.

use yaxpeax_arch::{Decoder, U8Reader};
use yaxpeax_arm::armv8::a64::{InstDecoder, Opcode};

fn opcode_of(word: u32) -> Option<Opcode> {
    let bytes = word.to_le_bytes();
    let mut reader = U8Reader::new(&bytes);
    InstDecoder::default()
        .decode(&mut reader)
        .ok()
        .map(|inst| inst.opcode)
}

#[test]
fn add_x0_x1_x2() {
    assert_eq!(opcode_of(0x8b02_0020), Some(Opcode::ADD));
}

#[test]
fn b_and_ret() {
    assert_eq!(opcode_of(0x1400_0004), Some(Opcode::B));
    assert_eq!(opcode_of(0xd65f_03c0), Some(Opcode::RET));
}

#[test]
fn svc_is_outside_the_subset_but_decodes() {
    assert_eq!(opcode_of(0xd400_0001), Some(Opcode::SVC));
}
