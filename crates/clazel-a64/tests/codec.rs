//! Tests of the executable encoder and decoder (jit.md J.4).
//!
//! The proofs in `src/` (`encoder`, `decoder`, `inverse`) say what the two
//! functions do for every input. These tests run the compiled code and
//! compare it with the independent disassembler `yaxpeax-arm` (a test
//! dependency only):
//!
//! - every instruction of the subset, with random fields, encodes to a word
//!   that the decoder reads back and that `yaxpeax-arm` reads as the
//!   instruction family it was meant to be;
//! - every word the decoder accepts, from random words and from words close
//!   to each variant's opcode bits, is one `yaxpeax-arm` also reads, and
//!   encodes back to the same word.
//!
//! Hardware differential tests on the macOS runner (jit.md exit criterion 3)
//! need to run the code, which this crate has no way to do (no `unsafe`);
//! they belong with the code that maps pages (J.7, J.8).

use clazel_a64::decoder::{classify, decode_instr, valid_exec};
use clazel_a64::encoder::encode_instr;
use clazel_a64::inverse::{decode_bytes, decode_encode_bytes, encode_bytes};
use clazel_a64::spec::{FPUnaryOp, Instr, LogicalOpc, MoveWideOp, ShiftType, Width};
use yaxpeax_arch::{Decoder, U8Reader};
use yaxpeax_arm::armv8::a64::InstDecoder;

/// A small deterministic generator (xorshift64*), so the tests need no `rand`.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn word(&mut self) -> u32 {
        (self.next() >> 32) as u32
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }

    fn bool(&mut self) -> bool {
        self.next() >> 63 == 1
    }

    fn reg(&mut self) -> u8 {
        self.below(32) as u8
    }

    fn width(&mut self) -> Width {
        if self.bool() { Width::W64 } else { Width::W32 }
    }

    fn shift(&mut self) -> ShiftType {
        match self.below(4) {
            0 => ShiftType::Lsl,
            1 => ShiftType::Lsr,
            2 => ShiftType::Asr,
            _ => ShiftType::Ror,
        }
    }

    /// A signed number in `-span / 2 .. span / 2`.
    fn signed(&mut self, span: u64) -> i32 {
        let v = self.below(span);
        (v as i64).wrapping_sub((span / 2) as i64) as i32
    }
}

/// An instruction of variant `k` (the order of [`Instr`]) with random fields,
/// not necessarily valid.
fn random_instr(r: &mut Rng, k: usize) -> Instr {
    match k {
        0 => Instr::AddSubShiftedReg {
            sf: r.width(),
            sub_op: r.bool(),
            setflags: r.bool(),
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
            shift_type: r.shift(),
            shift_amount: r.below(64) as u8,
        },
        1 => Instr::AddSubImm {
            sf: r.width(),
            sub_op: r.bool(),
            setflags: r.bool(),
            d: r.reg(),
            n: r.reg(),
            imm12: r.below(4096) as u16,
            sh: r.bool(),
        },
        2 => Instr::MulAddSub {
            sf: r.width(),
            sub_op: r.bool(),
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
            a: r.reg(),
        },
        3 => Instr::Div {
            sf: r.width(),
            is_unsigned: r.bool(),
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
        },
        4 => Instr::LogicalShiftedReg {
            sf: r.width(),
            opc: match r.below(4) {
                0 => LogicalOpc::And,
                1 => LogicalOpc::Orr,
                2 => LogicalOpc::Eor,
                _ => LogicalOpc::Ands,
            },
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
            shift_type: r.shift(),
            shift_amount: r.below(64) as u8,
        },
        5 => Instr::ShiftVariable {
            sf: r.width(),
            shift_type: r.shift(),
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
        },
        6 => Instr::Bitfield {
            sf: r.width(),
            signed: r.bool(),
            d: r.reg(),
            n: r.reg(),
            immr: r.below(64) as u8,
            imms: r.below(64) as u8,
        },
        7 => Instr::MoveWide {
            sf: r.width(),
            opcode: if r.bool() {
                MoveWideOp::Z
            } else {
                MoveWideOp::K
            },
            d: r.reg(),
            imm16: r.below(65536) as u16,
            hw: r.below(4) as u8,
        },
        8 => Instr::CondSelect {
            sf: r.width(),
            else_inv: r.bool(),
            else_inc: r.bool(),
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
            cond: r.below(16) as u8,
        },
        9 => Instr::LoadStoreImm {
            sf: r.width(),
            load: r.bool(),
            t: r.reg(),
            n: r.reg(),
            imm12: r.below(4096) as u16,
        },
        10 => Instr::LoadStoreReg {
            sf: r.width(),
            load: r.bool(),
            t: r.reg(),
            n: r.reg(),
            m: r.reg(),
            s: r.bool(),
        },
        11 => Instr::FpLoadStoreImm {
            load: r.bool(),
            t: r.reg(),
            n: r.reg(),
            imm12: r.below(4096) as u16,
        },
        12 => Instr::FpLoadStoreReg {
            load: r.bool(),
            t: r.reg(),
            n: r.reg(),
            m: r.reg(),
            s: r.bool(),
        },
        13 => Instr::B {
            imm26: r.signed(0x400_0000),
        },
        14 => Instr::BCond {
            cond: r.below(16) as u8,
            imm19: r.signed(0x8_0000),
        },
        15 => Instr::CompareBranch {
            sf: r.width(),
            iszero: r.bool(),
            t: r.reg(),
            imm19: r.signed(0x8_0000),
        },
        16 => Instr::Ret,
        17 => Instr::FAddSub {
            sub_op: r.bool(),
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
        },
        18 => Instr::FMul {
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
        },
        19 => Instr::FDiv {
            d: r.reg(),
            n: r.reg(),
            m: r.reg(),
        },
        20 => Instr::FUnary {
            fpop: match r.below(4) {
                0 => FPUnaryOp::Mov,
                1 => FPUnaryOp::Abs,
                2 => FPUnaryOp::Neg,
                _ => FPUnaryOp::Sqrt,
            },
            d: r.reg(),
            n: r.reg(),
        },
        21 => Instr::FCmp {
            n: r.reg(),
            m: r.reg(),
        },
        22 => Instr::FMovGen {
            to_fp: r.bool(),
            d: r.reg(),
            n: r.reg(),
        },
        23 => Instr::Scvtf {
            sf: r.width(),
            d: r.reg(),
            n: r.reg(),
        },
        _ => Instr::Fcvtzs {
            sf: r.width(),
            d: r.reg(),
            n: r.reg(),
        },
    }
}

const VARIANTS: usize = 25;

/// The `yaxpeax-arm` opcodes (their `Debug` names) a variant may be read as.
/// The disassembler has no opcodes for aliases (`cmp`, `mov`, `lsl`, `cset`
/// ...), so those read as the instruction they are an alias of.
fn expected(k: usize) -> &'static [&'static str] {
    match k {
        0 | 1 => &["ADD", "ADDS", "SUB", "SUBS", "NEG"],
        2 => &["MADD", "MSUB"],
        3 => &["SDIV", "UDIV"],
        4 => &["AND", "ANDS", "ORR", "EOR"],
        5 => &["LSLV", "LSRV", "ASRV"],
        6 => &["SBFM", "UBFM"],
        7 => &["MOVZ", "MOVK"],
        8 => &["CSEL", "CSINC", "CSINV", "CSNEG"],
        9..=12 => &["LDR", "STR"],
        13 => &["B"],
        14 => &["Bcc"],
        15 => &["CBZ", "CBNZ"],
        16 => &["RET"],
        17 => &["FADD", "FSUB"],
        18 => &["FMUL"],
        19 => &["FDIV"],
        20 => &["FMOV", "FABS", "FNEG", "FSQRT"],
        21 => &["FCMP"],
        22 => &["FMOV"],
        23 => &["SCVTF"],
        _ => &["FCVTZS"],
    }
}

/// The opcode name `yaxpeax-arm` gives a word, if it decodes it.
fn reference(word: u32) -> Option<String> {
    let bytes = word.to_le_bytes();
    let mut reader = U8Reader::new(&bytes);
    InstDecoder::default()
        .decode(&mut reader)
        .ok()
        .map(|inst| format!("{:?}", inst.opcode))
}

/// How many random cases of each kind to run. Miri is there to find
/// undefined behaviour in the code the tests run, not to repeat the sweep.
fn cases() -> u64 {
    if cfg!(miri) { 20 } else { 4000 }
}

#[test]
fn encoded_instructions_decode_to_themselves_and_the_reference_agrees() {
    let mut r = Rng(0x9e37_79b9_7f4a_7c15);
    for k in 0..VARIANTS {
        let mut checked = 0_u64;
        for _ in 0..cases().saturating_mul(20) {
            let i = random_instr(&mut r, k);
            if !valid_exec(&i) {
                continue;
            }
            let w = encode_instr(&i);
            let j = decode_instr(w);
            assert!(
                j.is_some(),
                "variant {k}, word {w:#010x}: the decoder refuses"
            );
            let Some(j) = j else { continue };
            assert_eq!(
                std::mem::discriminant(&i),
                std::mem::discriminant(&j),
                "variant {k}, word {w:#010x}"
            );
            assert_eq!(encode_instr(&j), w, "variant {k}, word {w:#010x}");
            assert_eq!(usize::from(classify(w)), k, "word {w:#010x}");
            let name = reference(w).unwrap_or_default();
            assert!(
                expected(k).iter().any(|e| name.starts_with(e)),
                "variant {k}, word {w:#010x}: reference says {name}"
            );
            let [b0, b1, b2, b3] = encode_bytes(&i);
            assert_eq!([b0, b1, b2, b3], w.to_le_bytes());
            assert_eq!(
                decode_bytes(b0, b1, b2, b3).map(|x| encode_instr(&x)),
                Some(w)
            );
            assert_eq!(decode_encode_bytes(&i).map(|x| encode_instr(&x)), Some(w));
            checked = checked.saturating_add(1);
            if checked == cases() {
                break;
            }
        }
        assert!(checked > 0, "no valid instruction found for variant {k}");
    }
}

#[test]
fn accepted_words_reencode_and_the_reference_reads_them() {
    let mut r = Rng(0x0123_4567_89ab_cdef);
    let mut accepted = 0_u64;
    // Random words, and the opcode bits of each variant with random fields:
    // the second kind is accepted often, the first mostly is not.
    for round in 0..cases().saturating_mul(50) {
        let w = if round % 2 == 0 {
            r.word()
        } else {
            let k = r.below(VARIANTS as u64) as usize;
            // The word of a valid-or-not instruction: its encoder output when
            // valid, else a random word with a mutated bit.
            let i = random_instr(&mut r, k);
            if valid_exec(&i) {
                let flip = 1_u32.rotate_left(r.below(32) as u32);
                if r.below(4) == 0 {
                    encode_instr(&i) ^ flip
                } else {
                    encode_instr(&i)
                }
            } else {
                r.word()
            }
        };
        if let Some(i) = decode_instr(w) {
            accepted = accepted.saturating_add(1);
            assert!(valid_exec(&i), "word {w:#010x}");
            assert_eq!(encode_instr(&i), w, "word {w:#010x}");
            let k = usize::from(classify(w));
            let name = reference(w).unwrap_or_default();
            assert!(
                expected(k).iter().any(|e| name.starts_with(e)),
                "class {k}, word {w:#010x}: reference says {name}"
            );
        }
    }
    assert!(accepted > 0);
}

#[test]
fn words_outside_the_subset_are_refused() {
    // svc #1, nop, a 64-bit `ror` (extr), `ldr x0, [sp]`, `b.al`, `ret x1`,
    // `add x0, x1, x2, ror #3`, and `rorv w0, w1, w2`.
    for w in [
        0xd400_0021_u32,
        0xd503_201f,
        0x93c1_0c20,
        0xf940_03e0,
        0x5400_000e,
        0xd65f_0020,
        0x8bc2_0c20,
        0x1ac2_2c20,
    ] {
        assert!(decode_instr(w).is_none(), "word {w:#010x}");
    }
    assert!(decode_instr(0xd65f_03c0).is_some());
}
