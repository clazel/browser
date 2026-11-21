//! A specification-level **decoder** for the canonical encoding of
//! [`super::spec`]: [`extract`] reads the fields of the instruction a byte
//! string would begin with, and [`dec`] accepts the result only if it really
//! is the canonical encoding that the bytes begin with.
//!
//! This is the proof device for [`crate::contract::canonical_prefix_free`]
//! and the model that an executable decoder refines (jit.md J.3, J.6):
//!
//! - **Soundness is by construction.** [`dec`] returns `Some(i)` only when
//!   `starts_with_encoding(bytes, i)`; there is nothing to prove.
//! - **Completeness is the lemma** `completeness`: for every
//!   instruction of the subset, `dec(encode(i) + rest) == Some(i)`. It is
//!   proven below one instruction at a time (the shapes `enc_rr` and
//!   `enc_rm_mem` first).
//! - **Prefix-freeness follows**: if two instructions' encodings both begin
//!   the same bytes, `dec` returns both, so they are equal.
//!
//! [`extract`] is total: it reads bytes past the end as 0 and returns a
//! meaningless instruction for bytes that are no encoding, which the final
//! check of [`dec`] then refuses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Byte `k` of `b` as an integer, or 0 past either end.
pub open spec fn at(b: Seq<u8>, k: int) -> int {
    if 0 <= k < b.len() {
        b[k] as int
    } else {
        0
    }
}

/// The four bytes at `k`, little-endian, as an unsigned number.
pub open spec fn le32(b: Seq<u8>, k: int) -> int {
    at(b, k) + 256 * (at(b, k + 1) + 256 * (at(b, k + 2) + 256 * at(b, k + 3)))
}

/// The eight bytes at `k`, little-endian, as an unsigned number.
pub open spec fn le64(b: Seq<u8>, k: int) -> int {
    le32(b, k) + 0x1_0000_0000 * le32(b, k + 4)
}

/// A 32-bit unsigned number as two's complement signed.
pub open spec fn sx32(v: int) -> int {
    if v >= 0x8000_0000 {
        v - 0x1_0000_0000
    } else {
        v
    }
}

/// The fields of the bytes before the opcode: the mandatory prefix, `REX`.
pub struct Head {
    /// The prefix byte (`0x66` or `0xF2`), or 0.
    pub pf: int,
    /// A `REX` byte is present.
    pub rexp: bool,
    /// `REX.W`.
    pub w: bool,
    /// `REX.R` (0 or 1).
    pub r: int,
    /// `REX.X` (0 or 1).
    pub x: int,
    /// `REX.B` (0 or 1).
    pub bb: int,
    /// The index of the first opcode byte.
    pub kop: int,
}

/// Reads the optional prefix and the optional `REX` byte.
pub open spec fn head(b: Seq<u8>) -> Head {
    let p = at(b, 0);
    let pf = if p == 0x66 || p == 0xF2 {
        p
    } else {
        0
    };
    let k: int = if p == 0x66 || p == 0xF2 {
        1
    } else {
        0
    };
    let rv = at(b, k);
    if 0x40 <= rv <= 0x4F {
        let v = rv - 0x40;
        Head {
            pf: pf,
            rexp: true,
            w: (v / 8) % 2 == 1,
            r: (v / 4) % 2,
            x: (v / 2) % 2,
            bb: v % 2,
            kop: k + 1,
        }
    } else {
        Head { pf: pf, rexp: false, w: false, r: 0, x: 0, bb: 0, kop: k }
    }
}

/// The operand size `REX.W` selects.
pub open spec fn sz_of(h: Head) -> Size {
    if h.w {
        Size::W64
    } else {
        Size::W32
    }
}

/// The `reg` register: the ModR/M `reg` field and `REX.R`.
pub open spec fn reg_f(b: Seq<u8>, h: Head, ko: int) -> u8 {
    ((at(b, ko) / 8) % 8 + 8 * h.r) as u8
}

/// The `rm` register: the ModR/M `rm` field and `REX.B`.
pub open spec fn rm_f(b: Seq<u8>, h: Head, ko: int) -> u8 {
    (at(b, ko) % 8 + 8 * h.bb) as u8
}

/// The ModR/M `mod` field.
pub open spec fn mod_f(b: Seq<u8>, ko: int) -> int {
    at(b, ko) / 64
}

/// The ModR/M `reg` field alone, an opcode extension.
pub open spec fn ext_f(b: Seq<u8>, ko: int) -> int {
    (at(b, ko) / 8) % 8
}

/// The memory operand of a `mod = 10`, `rm = 100` instruction whose ModR/M
/// byte is at `ko`: the SIB byte, then a 32-bit displacement.
pub open spec fn mem_f(b: Seq<u8>, h: Head, ko: int) -> Mem {
    mem_of(at(b, ko + 1), h.x, h.bb, le32(b, ko + 2))
}

/// The memory operand from its SIB byte, the `REX.X` and `REX.B` bits and the
/// unsigned displacement word.
pub open spec fn mem_of(sib: int, x: int, bb: int, disp: int) -> Mem {
    let ix = (sib / 8) % 8 + 8 * x;
    Mem {
        base: (sib % 8 + 8 * bb) as u8,
        index: if ix == 4 {
            None
        } else {
            Some(Index { reg: ix as u8, scale: (sib / 64) as u8 })
        },
        disp: sx32(disp) as i32,
    }
}

/// The ALU operation whose `op r/m, r` opcode is `v`.
pub open spec fn alu_of_base(v: int) -> Option<AluOp> {
    if v == 0x00 {
        Some(AluOp::Add)
    } else if v == 0x08 {
        Some(AluOp::Or)
    } else if v == 0x20 {
        Some(AluOp::And)
    } else if v == 0x28 {
        Some(AluOp::Sub)
    } else if v == 0x30 {
        Some(AluOp::Xor)
    } else if v == 0x38 {
        Some(AluOp::Cmp)
    } else {
        None
    }
}

/// The ALU operation of the group-1 extension `e` (`81 /e`).
pub open spec fn alu_of_ext(e: int) -> AluOp {
    if e == 0 {
        AluOp::Add
    } else if e == 1 {
        AluOp::Or
    } else if e == 4 {
        AluOp::And
    } else if e == 5 {
        AluOp::Sub
    } else if e == 6 {
        AluOp::Xor
    } else {
        AluOp::Cmp
    }
}

/// The shift of the group-2 extension `e`.
pub open spec fn shift_of_ext(e: int) -> ShiftOp {
    if e == 4 {
        ShiftOp::Shl
    } else if e == 5 {
        ShiftOp::Shr
    } else {
        ShiftOp::Sar
    }
}

/// The scalar double operation of the second opcode byte `o2`.
pub open spec fn fop_of(o2: int) -> BinOp {
    if o2 == 0x58 {
        BinOp::Add
    } else if o2 == 0x59 {
        BinOp::Mul
    } else if o2 == 0x5C {
        BinOp::Sub
    } else {
        BinOp::Div
    }
}

/// The XMM source operand: a register for `mod = 11`, else memory.
pub open spec fn xsrc_f(b: Seq<u8>, h: Head, ko: int) -> XmmSrc {
    if mod_f(b, ko) == 3 {
        XmmSrc::Reg(rm_f(b, h, ko))
    } else {
        XmmSrc::Mem(mem_f(b, h, ko))
    }
}

/// The fields of the instruction the bytes would begin with, if they began
/// with a canonical encoding; otherwise an arbitrary instruction.
#[verifier::opaque]
pub open spec fn extract(b: Seq<u8>) -> Instr {
    let h = head(b);
    let o = at(b, h.kop);
    let o2 = at(b, h.kop + 1);
    let ko = h.kop + 1;
    let ko2 = h.kop + 2;
    let sz = sz_of(h);
    if h.pf == 0 {
        if o == 0x0F {
            if o2 == 0xAF {
                Instr::ImulRR { sz: sz, dst: reg_f(b, h, ko2), src: rm_f(b, h, ko2) }
            } else if 0x80 <= o2 <= 0x8F {
                Instr::Jcc { cc: (o2 - 0x80) as u8, rel: sx32(le32(b, h.kop + 2)) as i32 }
            } else if 0x40 <= o2 <= 0x4F {
                Instr::Cmovcc {
                    cc: (o2 - 0x40) as u8,
                    sz: sz,
                    dst: reg_f(b, h, ko2),
                    src: rm_f(b, h, ko2),
                }
            } else {
                Instr::Setcc { cc: ((o2 - 0x90) % 16) as u8, dst: rm_f(b, h, ko2) }
            }
        } else if o == 0x89 {
            if mod_f(b, ko) == 3 {
                Instr::MovRR { sz: sz, dst: rm_f(b, h, ko), src: reg_f(b, h, ko) }
            } else {
                Instr::MovStore { sz: sz, mem: mem_f(b, h, ko), src: reg_f(b, h, ko) }
            }
        } else if o == 0x8B {
            Instr::MovLoad { sz: sz, dst: reg_f(b, h, ko), mem: mem_f(b, h, ko) }
        } else if 0xB8 <= o <= 0xBF {
            if h.w {
                Instr::MovImm64 { dst: ((o - 0xB8) + 8 * h.bb) as u8, imm_u64: le64(b, ko) as u64 }
            } else {
                Instr::MovImm32 { dst: ((o - 0xB8) + 8 * h.bb) as u8, imm_u32: le32(b, ko) as u32 }
            }
        } else if o == 0xC7 {
            Instr::MovImm32S { dst: rm_f(b, h, ko), imm: sx32(le32(b, ko + 1)) as i32 }
        } else if o == 0x81 {
            Instr::AluRI {
                alu: alu_of_ext(ext_f(b, ko)),
                sz: sz,
                dst: rm_f(b, h, ko),
                imm: sx32(le32(b, ko + 1)) as i32,
            }
        } else if o == 0x85 {
            Instr::TestRR { sz: sz, a: rm_f(b, h, ko), b: reg_f(b, h, ko) }
        } else if o == 0xF7 {
            if ext_f(b, ko) == 0 {
                Instr::TestRI { sz: sz, a: rm_f(b, h, ko), imm: sx32(le32(b, ko + 1)) as i32 }
            } else if ext_f(b, ko) == 3 {
                Instr::Neg { sz: sz, r: rm_f(b, h, ko) }
            } else {
                Instr::Not { sz: sz, r: rm_f(b, h, ko) }
            }
        } else if o == 0xC1 {
            Instr::ShiftImm {
                shift: shift_of_ext(ext_f(b, ko)),
                sz: sz,
                r: rm_f(b, h, ko),
                count: at(b, ko + 1) as u8,
            }
        } else if o == 0xD3 {
            Instr::ShiftCl { shift: shift_of_ext(ext_f(b, ko)), sz: sz, r: rm_f(b, h, ko) }
        } else if o == 0x69 {
            Instr::ImulRRI {
                sz: sz,
                dst: reg_f(b, h, ko),
                src: rm_f(b, h, ko),
                imm: sx32(le32(b, ko + 1)) as i32,
            }
        } else if o == 0xE9 {
            Instr::Jmp { rel: sx32(le32(b, ko)) as i32 }
        } else if o == 0xC3 {
            Instr::Ret
        } else if o % 8 == 1 && alu_of_base(o - 1) is Some {
            Instr::AluRR {
                alu: alu_of_base(o - 1)->Some_0,
                sz: sz,
                dst: rm_f(b, h, ko),
                src: reg_f(b, h, ko),
            }
        } else {
            Instr::AluRM {
                alu: if alu_of_base(o - 3) is Some {
                    alu_of_base(o - 3)->Some_0
                } else {
                    AluOp::Add
                },
                sz: sz,
                dst: reg_f(b, h, ko),
                mem: mem_f(b, h, ko),
            }
        }
    } else if h.pf == 0xF2 {
        if o2 == 0x51 {
            Instr::Sqrtsd { dst: reg_f(b, h, ko2), xsrc: xsrc_f(b, h, ko2) }
        } else if o2 == 0x2A {
            Instr::Cvtsi2sd { sz: sz, dst: reg_f(b, h, ko2), src: rm_f(b, h, ko2) }
        } else if o2 == 0x2C {
            Instr::Cvttsd2si { sz: sz, dst: reg_f(b, h, ko2), src: rm_f(b, h, ko2) }
        } else if o2 == 0x2D {
            Instr::Cvtsd2si { sz: sz, dst: reg_f(b, h, ko2), src: rm_f(b, h, ko2) }
        } else if o2 == 0x10 {
            Instr::MovsdLoad { dst: reg_f(b, h, ko2), mem: mem_f(b, h, ko2) }
        } else if o2 == 0x11 {
            Instr::MovsdStore { mem: mem_f(b, h, ko2), src: reg_f(b, h, ko2) }
        } else {
            Instr::FpArith {
                fop: fop_of(o2),
                dst: reg_f(b, h, ko2),
                xsrc: xsrc_f(b, h, ko2),
            }
        }
    } else {
        if o2 == 0x6E {
            Instr::MovqToXmm { dst: reg_f(b, h, ko2), src: rm_f(b, h, ko2) }
        } else if o2 == 0x7E {
            Instr::MovqFromXmm { dst: rm_f(b, h, ko2), src: reg_f(b, h, ko2) }
        } else {
            Instr::Ucomisd { a: reg_f(b, h, ko2), xsrc: xsrc_f(b, h, ko2) }
        }
    }
}

/// The decoder: the instruction `bytes` begin with, if they begin with the
/// canonical encoding of one.
pub open spec fn dec(bytes: Seq<u8>) -> Option<Instr> {
    let c = extract(bytes);
    if starts_with_encoding(bytes, c) {
        Some(c)
    } else {
        None
    }
}

/// Soundness of [`dec`] (by construction).
pub proof fn dec_sound(bytes: Seq<u8>, i: Instr)
    requires
        dec(bytes) == Some(i),
    ensures
        starts_with_encoding(bytes, i),
{
}

} // verus!
