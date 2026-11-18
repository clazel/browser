//! The **executable decoder**: [`extract_exec`] is proven equal to the
//! specification-level [`super::decoder::extract`], and [`decode_exec`]
//! meets [`crate::contract::decode_ensures`]: a `Some` result is the
//! canonical encoding of an instruction of the subset, and `None` means no
//! instruction's encoding begins the bytes (by the completeness of `extract`,
//! `decoder_proofs::lemma_extract_starts`, and the encoder
//! [`super::encoder::encode_exec`], which is equal to `encode`).
//!
//! Each function mirrors the spec function named in its doc, branch for
//! branch.

pub use super::decoder::*;
use super::encoder::encode_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Byte `k`, or 0 past the end (the spec's `at`).
pub fn at_e(b: &[u8], k: usize) -> (r: u8)
    ensures
        r as int == at(b@, k as int),
{
    match b.get(k) {
        Some(x) => *x,
        None => 0,
    }
}

/// Four bytes at `k`, little-endian (the spec's `le32`).
pub fn le32_e(b: &[u8], k: usize) -> (r: u32)
    requires
        k < 1000,
    ensures
        r as int == le32(b@, k as int),
{
    let b0 = at_e(b, k) as u32;
    let b1 = at_e(b, k.saturating_add(1)) as u32;
    let b2 = at_e(b, k.saturating_add(2)) as u32;
    let b3 = at_e(b, k.saturating_add(3)) as u32;
    b0.saturating_add(b1.saturating_add(b2.saturating_add(b3.saturating_mul(256)).saturating_mul(256)).saturating_mul(256))
}

/// Eight bytes at `k`, little-endian (the spec's `le64`).
pub fn le64_e(b: &[u8], k: usize) -> (r: u64)
    requires
        k < 990,
    ensures
        r as int == le64(b@, k as int),
{
    let lo = le32_e(b, k) as u64;
    let hi = le32_e(b, k.saturating_add(4)) as u64;
    lo.saturating_add(hi.saturating_mul(0x1_0000_0000))
}

/// A 32-bit word as a signed number (the spec's `sx32`).
pub fn sx32_e(x: u32) -> (r: i32)
    ensures
        r as int == sx32(x as int),
{
    if x >= 0x8000_0000 {
        ((x as i64).wrapping_add(-4294967296i64)) as i32
    } else {
        x as i32
    }
}

/// The prefix and `REX` fields (the spec's `Head`).
pub struct HeadE {
    /// The prefix byte or 0.
    pub pf: u8,
    /// `REX.W`.
    pub w: bool,
    /// `REX.R`.
    pub r: u8,
    /// `REX.X`.
    pub x: u8,
    /// `REX.B`.
    pub bb: u8,
    /// The index of the first opcode byte.
    pub kop: usize,
}

/// The exec head describes the spec head of `b`.
pub open spec fn hm(h: HeadE, b: Seq<u8>) -> bool {
    h.pf as int == head(b).pf && h.w == head(b).w && h.r as int == head(b).r && h.x as int == head(
        b,
    ).x && h.bb as int == head(b).bb && h.kop as int == head(b).kop && h.r <= 1 && h.x <= 1 && h.bb
        <= 1 && h.kop <= 2
}

/// The spec's `head`.
pub fn head_e(b: &[u8]) -> (h: HeadE)
    ensures
        hm(h, b@),
{
    let p = at_e(b, 0);
    let pf: u8 = if p == 0x66 || p == 0xF2 {
        p
    } else {
        0
    };
    let k: usize = if p == 0x66 || p == 0xF2 {
        1
    } else {
        0
    };
    let rv = at_e(b, k);
    if rv >= 0x40 && rv.saturating_sub(0x40) <= 0x0F {
        let v = rv.saturating_sub(0x40);
        HeadE {
            pf,
            w: (v / 8) % 2 == 1,
            r: (v / 4) % 2,
            x: (v / 2) % 2,
            bb: v % 2,
            kop: k.saturating_add(1),
        }
    } else {
        HeadE { pf, w: false, r: 0, x: 0, bb: 0, kop: k }
    }
}

/// The operand size `REX.W` selects.
pub fn sz_e(h: &HeadE) -> (r: Size)
    ensures
        r == sz_of(Head { pf: h.pf as int, rexp: false, w: h.w, r: 0, x: 0, bb: 0, kop: 0 }),
{
    if h.w {
        Size::W64
    } else {
        Size::W32
    }
}

/// The spec's `reg_f`.
pub fn reg_e(b: &[u8], h: &HeadE, ko: usize) -> (r: u8)
    requires
        hm(*h, b@),
        ko < 1000,
    ensures
        r == reg_f(b@, head(b@), ko as int),
{
    let m = at_e(b, ko);
    ((m / 8) % 8).saturating_add(h.r.saturating_mul(8))
}

/// The spec's `rm_f`.
pub fn rm_e(b: &[u8], h: &HeadE, ko: usize) -> (r: u8)
    requires
        hm(*h, b@),
        ko < 1000,
    ensures
        r == rm_f(b@, head(b@), ko as int),
{
    let m = at_e(b, ko);
    (m % 8).saturating_add(h.bb.saturating_mul(8))
}

/// The spec's `mod_f`.
pub fn mod_e(b: &[u8], ko: usize) -> (r: u8)
    ensures
        r as int == mod_f(b@, ko as int),
{
    at_e(b, ko) / 64
}

/// The spec's `ext_f`.
pub fn ext_e(b: &[u8], ko: usize) -> (r: u8)
    ensures
        r as int == ext_f(b@, ko as int),
{
    (at_e(b, ko) / 8) % 8
}

/// The spec's `mem_f`.
pub fn mem_e(b: &[u8], h: &HeadE, ko: usize) -> (r: Mem)
    requires
        hm(*h, b@),
        ko < 990,
    ensures
        r == mem_f(b@, head(b@), ko as int),
{
    let sib = at_e(b, ko.saturating_add(1));
    let ix: u8 = ((sib / 8) % 8).saturating_add(h.x.saturating_mul(8));
    let disp = sx32_e(le32_e(b, ko.saturating_add(2)));
    Mem {
        base: (sib % 8).saturating_add(h.bb.saturating_mul(8)),
        index: if ix == 4 {
            None
        } else {
            Some(Index { reg: ix, scale: sib / 64 })
        },
        disp,
    }
}

/// The spec's `alu_of_base`.
pub fn alu_of_base_e(v: u8) -> (r: Option<AluOp>)
    ensures
        r == alu_of_base(v as int),
{
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

/// The spec's `alu_of_ext`.
pub fn alu_of_ext_e(e: u8) -> (r: AluOp)
    ensures
        r == alu_of_ext(e as int),
{
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

/// The spec's `shift_of_ext`.
pub fn shift_of_ext_e(e: u8) -> (r: ShiftOp)
    ensures
        r == shift_of_ext(e as int),
{
    if e == 4 {
        ShiftOp::Shl
    } else if e == 5 {
        ShiftOp::Shr
    } else {
        ShiftOp::Sar
    }
}

/// The spec's `fop_of`.
pub fn fop_of_e(o2: u8) -> (r: BinOp)
    ensures
        r == fop_of(o2 as int),
{
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

/// The spec's `xsrc_f`.
pub fn xsrc_e(b: &[u8], h: &HeadE, ko: usize) -> (r: XmmSrc)
    requires
        hm(*h, b@),
        ko < 990,
    ensures
        r == xsrc_f(b@, head(b@), ko as int),
{
    if mod_e(b, ko) == 3 {
        XmmSrc::Reg(rm_e(b, h, ko))
    } else {
        XmmSrc::Mem(mem_e(b, h, ko))
    }
}

/// The spec's `extract`.
#[verifier::spinoff_prover]
#[verifier::rlimit(4000)]
pub fn extract_exec(b: &[u8]) -> (r: Instr)
    ensures
        r == extract(b@),
{
    reveal(extract);
    let h = head_e(b);
    let o = at_e(b, h.kop);
    let o2 = at_e(b, h.kop.saturating_add(1));
    let ko = h.kop.saturating_add(1);
    let ko2 = h.kop.saturating_add(2);
    let sz = sz_e(&h);
    if h.pf == 0 {
        if o == 0x0F {
            if o2 == 0xAF {
                Instr::ImulRR { sz, dst: reg_e(b, &h, ko2), src: rm_e(b, &h, ko2) }
            } else if o2 >= 0x80 && o2.saturating_sub(0x80) <= 0x0F {
                Instr::Jcc { cc: o2.saturating_sub(0x80), rel: sx32_e(le32_e(b, h.kop.saturating_add(2))) }
            } else if o2 >= 0x40 && o2.saturating_sub(0x40) <= 0x0F {
                Instr::Cmovcc {
                    cc: o2.saturating_sub(0x40),
                    sz,
                    dst: reg_e(b, &h, ko2),
                    src: rm_e(b, &h, ko2),
                }
            } else {
                Instr::Setcc { cc: o2 % 16, dst: rm_e(b, &h, ko2) }
            }
        } else if o == 0x89 {
            if mod_e(b, ko) == 3 {
                Instr::MovRR { sz, dst: rm_e(b, &h, ko), src: reg_e(b, &h, ko) }
            } else {
                Instr::MovStore { sz, mem: mem_e(b, &h, ko), src: reg_e(b, &h, ko) }
            }
        } else if o == 0x8B {
            Instr::MovLoad { sz, dst: reg_e(b, &h, ko), mem: mem_e(b, &h, ko) }
        } else if o >= 0xB8 && o.saturating_sub(0xB8) <= 0x07 {
            if h.w {
                Instr::MovImm64 { dst: o.saturating_sub(0xB8).saturating_add(h.bb.saturating_mul(8)), imm_u64: le64_e(b, ko) }
            } else {
                Instr::MovImm32 { dst: o.saturating_sub(0xB8).saturating_add(h.bb.saturating_mul(8)), imm_u32: le32_e(b, ko) }
            }
        } else if o == 0xC7 {
            Instr::MovImm32S { dst: rm_e(b, &h, ko), imm: sx32_e(le32_e(b, ko.saturating_add(1))) }
        } else if o == 0x81 {
            Instr::AluRI {
                alu: alu_of_ext_e(ext_e(b, ko)),
                sz,
                dst: rm_e(b, &h, ko),
                imm: sx32_e(le32_e(b, ko.saturating_add(1))),
            }
        } else if o == 0x85 {
            Instr::TestRR { sz, a: rm_e(b, &h, ko), b: reg_e(b, &h, ko) }
        } else if o == 0xF7 {
            let e = ext_e(b, ko);
            if e == 0 {
                Instr::TestRI { sz, a: rm_e(b, &h, ko), imm: sx32_e(le32_e(b, ko.saturating_add(1))) }
            } else if e == 3 {
                Instr::Neg { sz, r: rm_e(b, &h, ko) }
            } else {
                Instr::Not { sz, r: rm_e(b, &h, ko) }
            }
        } else if o == 0xC1 {
            Instr::ShiftImm {
                shift: shift_of_ext_e(ext_e(b, ko)),
                sz,
                r: rm_e(b, &h, ko),
                count: at_e(b, ko.saturating_add(1)),
            }
        } else if o == 0xD3 {
            Instr::ShiftCl { shift: shift_of_ext_e(ext_e(b, ko)), sz, r: rm_e(b, &h, ko) }
        } else if o == 0x69 {
            Instr::ImulRRI {
                sz,
                dst: reg_e(b, &h, ko),
                src: rm_e(b, &h, ko),
                imm: sx32_e(le32_e(b, ko.saturating_add(1))),
            }
        } else if o == 0xE9 {
            Instr::Jmp { rel: sx32_e(le32_e(b, ko)) }
        } else if o == 0xC3 {
            Instr::Ret
        } else {
            let am1 = if o >= 1 {
                alu_of_base_e(o.saturating_sub(1))
            } else {
                None
            };
            if o % 8 == 1 && am1.is_some() {
                Instr::AluRR {
                    alu: match am1 {
                        Some(a) => a,
                        None => AluOp::Add,
                    },
                    sz,
                    dst: rm_e(b, &h, ko),
                    src: reg_e(b, &h, ko),
                }
            } else {
                let am3 = if o >= 3 {
                    alu_of_base_e(o.saturating_sub(3))
                } else {
                    None
                };
                Instr::AluRM {
                    alu: match am3 {
                        Some(a) => a,
                        None => AluOp::Add,
                    },
                    sz,
                    dst: reg_e(b, &h, ko),
                    mem: mem_e(b, &h, ko),
                }
            }
        }
    } else if h.pf == 0xF2 {
        if o2 == 0x51 {
            Instr::Sqrtsd { dst: reg_e(b, &h, ko2), xsrc: xsrc_e(b, &h, ko2) }
        } else if o2 == 0x2A {
            Instr::Cvtsi2sd { sz, dst: reg_e(b, &h, ko2), src: rm_e(b, &h, ko2) }
        } else if o2 == 0x2C {
            Instr::Cvttsd2si { sz, dst: reg_e(b, &h, ko2), src: rm_e(b, &h, ko2) }
        } else if o2 == 0x2D {
            Instr::Cvtsd2si { sz, dst: reg_e(b, &h, ko2), src: rm_e(b, &h, ko2) }
        } else if o2 == 0x10 {
            Instr::MovsdLoad { dst: reg_e(b, &h, ko2), mem: mem_e(b, &h, ko2) }
        } else if o2 == 0x11 {
            Instr::MovsdStore { mem: mem_e(b, &h, ko2), src: reg_e(b, &h, ko2) }
        } else {
            Instr::FpArith {
                fop: fop_of_e(o2),
                dst: reg_e(b, &h, ko2),
                xsrc: xsrc_e(b, &h, ko2),
            }
        }
    } else {
        if o2 == 0x6E {
            Instr::MovqToXmm { dst: reg_e(b, &h, ko2), src: rm_e(b, &h, ko2) }
        } else if o2 == 0x7E {
            Instr::MovqFromXmm { dst: rm_e(b, &h, ko2), src: reg_e(b, &h, ko2) }
        } else {
            Instr::Ucomisd { a: reg_e(b, &h, ko2), xsrc: xsrc_e(b, &h, ko2) }
        }
    }
}

/// The spec's `mem_ok`.
pub fn mem_ok_e(m: &Mem) -> (r: bool)
    ensures
        r == mem_ok(*m),
{
    m.base < 16 && match &m.index {
        None => true,
        Some(ix) => ix.reg < 16 && ix.reg != 4 && ix.scale < 4,
    }
}

/// The spec's `xmm_src_ok`.
pub fn xmm_src_ok_e(s: &XmmSrc) -> (r: bool)
    ensures
        r == xmm_src_ok(*s),
{
    match s {
        XmmSrc::Reg(r) => *r < 16,
        XmmSrc::Mem(m) => mem_ok_e(m),
    }
}

/// The spec's `valid_instr`.
pub fn valid_exec(i: &Instr) -> (r: bool)
    ensures
        r == valid_instr(*i),
{
    match i {
        Instr::MovRR { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::MovLoad { dst, mem, .. } => *dst < 16 && mem_ok_e(mem),
        Instr::MovStore { mem, src, .. } => mem_ok_e(mem) && *src < 16,
        Instr::MovImm32 { dst, .. } => *dst < 16,
        Instr::MovImm32S { dst, .. } => *dst < 16,
        Instr::MovImm64 { dst, .. } => *dst < 16,
        Instr::AluRR { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::AluRM { dst, mem, .. } => *dst < 16 && mem_ok_e(mem),
        Instr::AluRI { dst, .. } => *dst < 16,
        Instr::TestRR { a, b, .. } => *a < 16 && *b < 16,
        Instr::TestRI { a, .. } => *a < 16,
        Instr::Neg { r, .. } => *r < 16,
        Instr::Not { r, .. } => *r < 16,
        Instr::ShiftImm { sz, r, count, .. } => *r < 16 && 1 <= *count && *count <= (match sz {
            Size::W64 => 63u8,
            Size::W32 => 31u8,
        }),
        Instr::ShiftCl { r, .. } => *r < 16,
        Instr::ImulRR { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::ImulRRI { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::Jcc { cc, .. } => *cc < 16,
        Instr::Jmp { .. } => true,
        Instr::Ret => true,
        Instr::Cmovcc { cc, dst, src, .. } => *cc < 16 && *dst < 16 && *src < 16,
        Instr::Setcc { cc, dst } => *cc < 16 && *dst < 16,
        Instr::FpArith { dst, xsrc, .. } => *dst < 16 && xmm_src_ok_e(xsrc),
        Instr::Sqrtsd { dst, xsrc } => *dst < 16 && xmm_src_ok_e(xsrc),
        Instr::Ucomisd { a, xsrc } => *a < 16 && xmm_src_ok_e(xsrc),
        Instr::Cvtsi2sd { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::Cvttsd2si { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::Cvtsd2si { dst, src, .. } => *dst < 16 && *src < 16,
        Instr::MovqToXmm { dst, src } => *dst < 16 && *src < 16,
        Instr::MovqFromXmm { dst, src } => *dst < 16 && *src < 16,
        Instr::MovsdLoad { dst, mem } => *dst < 16 && mem_ok_e(mem),
        Instr::MovsdStore { mem, src } => mem_ok_e(mem) && *src < 16,
    }
}

/// Whether `e` is a prefix of `b`.
pub fn starts_with_exec(b: &[u8], e: &[u8]) -> (r: bool)
    ensures
        r == (e@.len() <= b@.len() && b@.subrange(0, e@.len() as int) == e@),
{
    if e.len() > b.len() {
        return false;
    }
    let mut k: usize = 0;
    while k < e.len()
        invariant
            k <= e.len(),
            e.len() <= b.len(),
            forall|j: int| 0 <= j < k ==> b@[j] == e@[j],
        decreases e.len() - k,
    {
        let (x, y) = match (b.get(k), e.get(k)) {
            (Some(x), Some(y)) => (*x, *y),
            _ => (0u8, 0u8),
        };
        if x != y {
            proof {
                assert(b@.subrange(0, e@.len() as int)[k as int] != e@[k as int]);
            }
            return false;
        }
        k = k.saturating_add(1);
    }
    assert(b@.subrange(0, e@.len() as int) =~= e@);
    true
}

/// **The executable decoder**: meets [`crate::contract::decode_ensures`].
/// It reads the fields ([`extract_exec`]), re-encodes them
/// ([`encode_exec`]), and accepts only if the bytes begin with exactly that.
#[verifier::spinoff_prover]
#[verifier::rlimit(1000)]
pub fn decode_exec(bytes: &[u8]) -> (r: Option<(Instr, usize)>)
    ensures
        crate::contract::decode_ensures(bytes@, r),
{
    let c = extract_exec(bytes);
    let ok = valid_exec(&c);
    if !ok {
        proof {
            assert forall|i: Instr| !starts_with_encoding(bytes@, i) by {
                if starts_with_encoding(bytes@, i) {
                    super::decoder_proofs::lemma_extract_starts(bytes@, i);
                }
            }
        }
        return None;
    }
    let e = encode_exec(&c);
    let sw = starts_with_exec(bytes, &e);
    if sw {
        Some((c, e.len()))
    } else {
        proof {
            assert forall|i: Instr| !starts_with_encoding(bytes@, i) by {
                if starts_with_encoding(bytes@, i) {
                    super::decoder_proofs::lemma_extract_starts(bytes@, i);
                }
            }
        }
        None
    }
}

} // verus!
