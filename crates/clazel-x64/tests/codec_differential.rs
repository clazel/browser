//! Differential test of the encoder and the decoder (docs/phases/jit.md item
//! J.3, exit criterion 3) against the reference disassembler `yaxpeax-x86`.
//!
//! For a few thousand instructions of the subset (every operand shape, with
//! boundary registers, scales, displacements and immediates):
//!
//! 1. the decoder reads back what the encoder wrote, whatever follows it;
//! 2. the reference disassembler decodes the encoder's bytes, and reads the
//!    same length as the encoder wrote (so the encoding is a real x86-64
//!    instruction of that length);
//! 3. every strict prefix of the encoding is refused (a truncated
//!    instruction).
//!
//! It also decodes mutations of each encoding (one byte altered): whatever
//! the decoder accepts is again the canonical encoding of what it returned,
//! and the reference reads it with the same length.
//! This test is evidence, not proof; the proof is `codec.rs`, `encoder.rs`
//! and `decoder_exec.rs`.

use clazel_x64::api::X64Codec;
use clazel_x64::codec::X64;
use clazel_x64::spec::*;
use yaxpeax_arch::{Decoder, LengthedInstruction, U8Reader};
use yaxpeax_x86::long_mode::InstDecoder;

fn reference_len(bytes: &[u8]) -> Option<u64> {
    let mut reader = U8Reader::new(bytes);
    InstDecoder::default()
        .decode(&mut reader)
        .ok()
        .map(|inst| inst.len().to_const())
}

const REGS: [u8; 6] = [0, 3, 4, 5, 8, 15];
const IMMS: [i32; 5] = [0, 1, -1, 0x7fff_ffff, i32::MIN];

// The spec's types are not `Copy`, so each use builds a fresh value.
fn size(w64: bool) -> Size {
    if w64 { Size::W64 } else { Size::W32 }
}
fn alu(k: usize) -> AluOp {
    [
        AluOp::Add,
        AluOp::Or,
        AluOp::And,
        AluOp::Sub,
        AluOp::Xor,
        AluOp::Cmp,
    ]
    .into_iter()
    .nth(k)
    .unwrap()
}
fn shift(k: usize) -> ShiftOp {
    [ShiftOp::Shl, ShiftOp::Shr, ShiftOp::Sar]
        .into_iter()
        .nth(k)
        .unwrap()
}
fn fop(k: usize) -> BinOp {
    [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div]
        .into_iter()
        .nth(k)
        .unwrap()
}

/// A memory operand: base, optional (index, scale), displacement.
type MemSpec = (u8, Option<(u8, u8)>, i32);

fn mem((base, index, disp): MemSpec) -> Mem {
    Mem {
        base,
        index: index.map(|(reg, scale)| Index { reg, scale }),
        disp,
    }
}

fn mems() -> Vec<MemSpec> {
    let mut v = Vec::new();
    for &base in &REGS {
        for disp in [0, -8, 0x1234_5678] {
            v.push((base, None, disp));
            for reg in [0u8, 3, 5, 8, 15] {
                for scale in 0..4u8 {
                    v.push((base, Some((reg, scale)), disp));
                }
            }
        }
    }
    v
}

/// An XMM source: a register, or a memory operand.
fn xsrcs() -> Vec<Result<u8, MemSpec>> {
    let mut v: Vec<Result<u8, MemSpec>> = [0u8, 7, 8, 15].iter().map(|&r| Ok(r)).collect();
    v.extend(mems().into_iter().step_by(7).map(Err));
    v
}

fn xsrc(x: &Result<u8, MemSpec>) -> XmmSrc {
    match x {
        Ok(r) => XmmSrc::Reg(*r),
        Err(m) => XmmSrc::Mem(mem(*m)),
    }
}

fn instrs() -> Vec<Instr> {
    let mut v = vec![Instr::Ret];
    for w64 in [false, true] {
        let sz = || size(w64);
        for &dst in &REGS {
            for &src in &REGS {
                v.push(Instr::MovRR { sz: sz(), dst, src });
                for k in 0..6 {
                    v.push(Instr::AluRR {
                        alu: alu(k),
                        sz: sz(),
                        dst,
                        src,
                    });
                }
                v.push(Instr::TestRR {
                    sz: sz(),
                    a: dst,
                    b: src,
                });
                v.push(Instr::ImulRR { sz: sz(), dst, src });
                v.push(Instr::Cvtsi2sd { sz: sz(), dst, src });
                v.push(Instr::Cvttsd2si { sz: sz(), dst, src });
                v.push(Instr::Cvtsd2si { sz: sz(), dst, src });
                for cc in [0u8, 7, 15] {
                    v.push(Instr::Cmovcc {
                        cc,
                        sz: sz(),
                        dst,
                        src,
                    });
                }
                for &imm in &IMMS {
                    v.push(Instr::ImulRRI {
                        sz: sz(),
                        dst,
                        src,
                        imm,
                    });
                }
            }
            v.push(Instr::Neg { sz: sz(), r: dst });
            v.push(Instr::Not { sz: sz(), r: dst });
            for &imm in &IMMS {
                v.push(Instr::TestRI {
                    sz: sz(),
                    a: dst,
                    imm,
                });
                for k in 0..6 {
                    v.push(Instr::AluRI {
                        alu: alu(k),
                        sz: sz(),
                        dst,
                        imm,
                    });
                }
            }
            let max = if w64 { 63 } else { 31 };
            for k in 0..3 {
                v.push(Instr::ShiftCl {
                    shift: shift(k),
                    sz: sz(),
                    r: dst,
                });
                for count in [1u8, 2, max] {
                    v.push(Instr::ShiftImm {
                        shift: shift(k),
                        sz: sz(),
                        r: dst,
                        count,
                    });
                }
            }
            for m in mems().into_iter().step_by(11) {
                v.push(Instr::MovLoad {
                    sz: sz(),
                    dst,
                    mem: mem(m),
                });
                v.push(Instr::MovStore {
                    sz: sz(),
                    mem: mem(m),
                    src: dst,
                });
                for k in 0..6 {
                    v.push(Instr::AluRM {
                        alu: alu(k),
                        sz: sz(),
                        dst,
                        mem: mem(m),
                    });
                }
            }
        }
    }
    for &dst in &REGS {
        for imm_u32 in [0u32, 1, u32::MAX] {
            v.push(Instr::MovImm32 { dst, imm_u32 });
        }
        for &imm in &IMMS {
            v.push(Instr::MovImm32S { dst, imm });
        }
        for imm_u64 in [0u64, 1, u64::MAX, 0x0123_4567_89ab_cdef] {
            v.push(Instr::MovImm64 { dst, imm_u64 });
        }
        for cc in 0..16u8 {
            v.push(Instr::Setcc { cc, dst });
        }
        for x in [0u8, 15] {
            v.push(Instr::MovqToXmm { dst: x, src: dst });
            v.push(Instr::MovqFromXmm { dst, src: x });
        }
    }
    for cc in 0..16u8 {
        for &rel in &IMMS {
            v.push(Instr::Jcc { cc, rel });
        }
    }
    for &rel in &IMMS {
        v.push(Instr::Jmp { rel });
    }
    for x in xsrcs() {
        for dst in [0u8, 7, 8, 15] {
            for k in 0..4 {
                v.push(Instr::FpArith {
                    fop: fop(k),
                    dst,
                    xsrc: xsrc(&x),
                });
            }
            v.push(Instr::Sqrtsd {
                dst,
                xsrc: xsrc(&x),
            });
            v.push(Instr::Ucomisd {
                a: dst,
                xsrc: xsrc(&x),
            });
        }
    }
    for m in mems().into_iter().step_by(5) {
        for r in [0u8, 9] {
            v.push(Instr::MovsdLoad {
                dst: r,
                mem: mem(m),
            });
            v.push(Instr::MovsdStore {
                mem: mem(m),
                src: r,
            });
        }
    }
    v
}

#[test]
fn encoder_decoder_and_reference_agree() {
    let all = instrs();
    assert!(all.len() > 3000);
    for i in &all {
        let enc = X64::encode_instr(i);
        // 1. The decoder reads back the instruction, whatever follows.
        for tail in [&[][..], &[0x90][..], &[0xc3, 0x00, 0xff][..]] {
            let mut bytes = enc.clone();
            bytes.extend_from_slice(tail);
            let (j, n) = X64::decode_instr(&bytes).expect("canonical encoding refused");
            assert_eq!(n, enc.len());
            assert_eq!(X64::encode_instr(&j), enc);
        }
        // 2. The reference reads the same length.
        assert_eq!(reference_len(&enc), Some(enc.len() as u64), "{enc:02x?}");
        // 3. Truncations are refused.
        for cut in 0..enc.len() {
            assert!(X64::decode_instr(&enc[..cut]).is_none(), "{enc:02x?}");
        }
    }
}

#[test]
fn accepted_mutations_are_canonical_and_real() {
    for i in instrs().iter().step_by(13) {
        let enc = X64::encode_instr(i);
        for k in 0..enc.len() {
            for flip in [0x01u8, 0x40, 0x80, 0xff] {
                let mut bytes = enc.clone();
                bytes[k] ^= flip;
                if let Some((j, n)) = X64::decode_instr(&bytes) {
                    assert_eq!(X64::encode_instr(&j), bytes[..n], "{bytes:02x?}");
                    assert_eq!(reference_len(&bytes[..n]), Some(n as u64), "{bytes:02x?}");
                }
            }
        }
    }
}
