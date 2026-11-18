//! The executable x86-64 validator: a decoder over the instruction subset of
//! `clazel-x64` and the scan of [`crate::spec::policy`], in linear time.
//!
//! **Not verified.** This is plain Rust that follows [`crate::spec`] and
//! [`clazel_x64::decoder`] function by function (each function names the
//! spec function it implements); no Verus proof connects it to
//! [`crate::contract::validate_ensures`] yet, so the crate stays at tier 0.
//! What backs it today is the tests in `tests/` (unit tests, a hostile corpus
//! and a differential test against the spec's own encoder, which is this
//! file's `encode`). It never panics: no indexing, no unchecked arithmetic.
//!
//! The decoder reads the fields of the instruction the bytes would begin
//! with ([`extract`], the spec's `extract`), then accepts only if the
//! canonical encoding of that instruction is exactly the bytes consumed
//! ([`decode`], the spec's `dec`). So it accepts nothing but canonical
//! encodings, whatever [`extract`] reads.

use clazel_x64::spec::{AluOp, BinOp, Index, Instr, Mem, ShiftOp, Size, XmmSrc};

/// The byte at `k`, or 0 past the end (the spec's `at`).
fn at(b: &[u8], k: usize) -> u8 {
    b.get(k).copied().unwrap_or(0)
}

/// Four bytes at `k`, little-endian (the spec's `le32`).
fn le32(b: &[u8], k: usize) -> u32 {
    let mut v: u32 = 0;
    for d in (0..4usize).rev() {
        v = v.wrapping_mul(256).wrapping_add(u32::from(at(b, k.saturating_add(d))));
    }
    v
}

/// Eight bytes at `k`, little-endian (the spec's `le64`).
fn le64(b: &[u8], k: usize) -> u64 {
    u64::from(le32(b, k)) | (u64::from(le32(b, k.saturating_add(4))) << 32)
}

/// The prefix and `REX` fields (the spec's `Head`).
struct Head {
    pf: u8,
    w: bool,
    r: u8,
    x: u8,
    bb: u8,
    kop: usize,
}

/// The spec's `head`.
fn head(b: &[u8]) -> Head {
    let p = at(b, 0);
    let (pf, k) = if p == 0x66 || p == 0xF2 { (p, 1usize) } else { (0, 0usize) };
    let rv = at(b, k);
    if (0x40..=0x4F).contains(&rv) {
        let v = rv.wrapping_sub(0x40);
        Head {
            pf,
            w: (v / 8) % 2 == 1,
            r: (v / 4) % 2,
            x: (v / 2) % 2,
            bb: v % 2,
            kop: k.saturating_add(1),
        }
    } else {
        Head { pf, w: false, r: 0, x: 0, bb: 0, kop: k }
    }
}

fn sx32(v: u32) -> i32 {
    i32::from_ne_bytes(v.to_ne_bytes())
}

fn reg_f(b: &[u8], h: &Head, ko: usize) -> u8 {
    ((at(b, ko) / 8) % 8).wrapping_add(h.r.wrapping_mul(8))
}

fn rm_f(b: &[u8], h: &Head, ko: usize) -> u8 {
    (at(b, ko) % 8).wrapping_add(h.bb.wrapping_mul(8))
}

fn mod_f(b: &[u8], ko: usize) -> u8 {
    at(b, ko) / 64
}

fn ext_f(b: &[u8], ko: usize) -> u8 {
    (at(b, ko) / 8) % 8
}

/// The spec's `mem_f`.
fn mem_f(b: &[u8], h: &Head, ko: usize) -> Mem {
    let sib = at(b, ko.saturating_add(1));
    let ix = ((sib / 8) % 8).wrapping_add(h.x.wrapping_mul(8));
    Mem {
        base: (sib % 8).wrapping_add(h.bb.wrapping_mul(8)),
        index: if ix == 4 { None } else { Some(Index { reg: ix, scale: sib / 64 }) },
        disp: sx32(le32(b, ko.saturating_add(2))),
    }
}

fn alu_of_base(v: u8) -> Option<AluOp> {
    match v {
        0x00 => Some(AluOp::Add),
        0x08 => Some(AluOp::Or),
        0x20 => Some(AluOp::And),
        0x28 => Some(AluOp::Sub),
        0x30 => Some(AluOp::Xor),
        0x38 => Some(AluOp::Cmp),
        _ => None,
    }
}

fn alu_of_ext(e: u8) -> AluOp {
    match e {
        0 => AluOp::Add,
        1 => AluOp::Or,
        4 => AluOp::And,
        5 => AluOp::Sub,
        6 => AluOp::Xor,
        _ => AluOp::Cmp,
    }
}

fn shift_of_ext(e: u8) -> ShiftOp {
    match e {
        4 => ShiftOp::Shl,
        5 => ShiftOp::Shr,
        _ => ShiftOp::Sar,
    }
}

fn fop_of(o2: u8) -> BinOp {
    match o2 {
        0x58 => BinOp::Add,
        0x59 => BinOp::Mul,
        0x5C => BinOp::Sub,
        _ => BinOp::Div,
    }
}

fn xsrc_f(b: &[u8], h: &Head, ko: usize) -> XmmSrc {
    if mod_f(b, ko) == 3 { XmmSrc::Reg(rm_f(b, h, ko)) } else { XmmSrc::Mem(mem_f(b, h, ko)) }
}

fn size_of(h: &Head) -> Size {
    if h.w { Size::W64 } else { Size::W32 }
}

/// The fields of the instruction the bytes would begin with if they began
/// with a canonical encoding; otherwise some instruction (the spec's
/// `extract`).
pub fn extract(b: &[u8]) -> Instr {
    let h = head(b);
    let o = at(b, h.kop);
    let o2 = at(b, h.kop.saturating_add(1));
    let ko = h.kop.saturating_add(1);
    let ko2 = h.kop.saturating_add(2);
    let sz = || size_of(&h);
    if h.pf == 0 {
        if o == 0x0F {
            if o2 == 0xAF {
                Instr::ImulRR { sz: sz(), dst: reg_f(b, &h, ko2), src: rm_f(b, &h, ko2) }
            } else if (0x80..=0x8F).contains(&o2) {
                Instr::Jcc { cc: o2.wrapping_sub(0x80), rel: sx32(le32(b, ko2)) }
            } else if (0x40..=0x4F).contains(&o2) {
                Instr::Cmovcc {
                    cc: o2.wrapping_sub(0x40),
                    sz: sz(),
                    dst: reg_f(b, &h, ko2),
                    src: rm_f(b, &h, ko2),
                }
            } else {
                Instr::Setcc { cc: o2.wrapping_sub(0x90) % 16, dst: rm_f(b, &h, ko2) }
            }
        } else if o == 0x89 {
            if mod_f(b, ko) == 3 {
                Instr::MovRR { sz: sz(), dst: rm_f(b, &h, ko), src: reg_f(b, &h, ko) }
            } else {
                Instr::MovStore { sz: sz(), mem: mem_f(b, &h, ko), src: reg_f(b, &h, ko) }
            }
        } else if o == 0x8B {
            Instr::MovLoad { sz: sz(), dst: reg_f(b, &h, ko), mem: mem_f(b, &h, ko) }
        } else if (0xB8..=0xBF).contains(&o) {
            let dst = o.wrapping_sub(0xB8).wrapping_add(h.bb.wrapping_mul(8));
            if h.w {
                Instr::MovImm64 { dst, imm_u64: le64(b, ko) }
            } else {
                Instr::MovImm32 { dst, imm_u32: le32(b, ko) }
            }
        } else if o == 0xC7 {
            Instr::MovImm32S { dst: rm_f(b, &h, ko), imm: sx32(le32(b, ko.saturating_add(1))) }
        } else if o == 0x81 {
            Instr::AluRI {
                alu: alu_of_ext(ext_f(b, ko)),
                sz: sz(),
                dst: rm_f(b, &h, ko),
                imm: sx32(le32(b, ko.saturating_add(1))),
            }
        } else if o == 0x85 {
            Instr::TestRR { sz: sz(), a: rm_f(b, &h, ko), b: reg_f(b, &h, ko) }
        } else if o == 0xF7 {
            match ext_f(b, ko) {
                0 => Instr::TestRI {
                    sz: sz(),
                    a: rm_f(b, &h, ko),
                    imm: sx32(le32(b, ko.saturating_add(1))),
                },
                3 => Instr::Neg { sz: sz(), r: rm_f(b, &h, ko) },
                _ => Instr::Not { sz: sz(), r: rm_f(b, &h, ko) },
            }
        } else if o == 0xC1 {
            Instr::ShiftImm {
                shift: shift_of_ext(ext_f(b, ko)),
                sz: sz(),
                r: rm_f(b, &h, ko),
                count: at(b, ko.saturating_add(1)),
            }
        } else if o == 0xD3 {
            Instr::ShiftCl { shift: shift_of_ext(ext_f(b, ko)), sz: sz(), r: rm_f(b, &h, ko) }
        } else if o == 0x69 {
            Instr::ImulRRI {
                sz: sz(),
                dst: reg_f(b, &h, ko),
                src: rm_f(b, &h, ko),
                imm: sx32(le32(b, ko.saturating_add(1))),
            }
        } else if o == 0xE9 {
            Instr::Jmp { rel: sx32(le32(b, ko)) }
        } else if o == 0xC3 {
            Instr::Ret
        } else if o % 8 == 1 && alu_of_base(o.wrapping_sub(1)).is_some() {
            Instr::AluRR {
                alu: alu_of_base(o.wrapping_sub(1)).unwrap_or(AluOp::Add),
                sz: sz(),
                dst: rm_f(b, &h, ko),
                src: reg_f(b, &h, ko),
            }
        } else {
            Instr::AluRM {
                alu: alu_of_base(o.wrapping_sub(3)).unwrap_or(AluOp::Add),
                sz: sz(),
                dst: reg_f(b, &h, ko),
                mem: mem_f(b, &h, ko),
            }
        }
    } else if h.pf == 0xF2 {
        match o2 {
            0x51 => Instr::Sqrtsd { dst: reg_f(b, &h, ko2), xsrc: xsrc_f(b, &h, ko2) },
            0x2A => Instr::Cvtsi2sd { sz: sz(), dst: reg_f(b, &h, ko2), src: rm_f(b, &h, ko2) },
            0x2C => Instr::Cvttsd2si { sz: sz(), dst: reg_f(b, &h, ko2), src: rm_f(b, &h, ko2) },
            0x2D => Instr::Cvtsd2si { sz: sz(), dst: reg_f(b, &h, ko2), src: rm_f(b, &h, ko2) },
            0x10 => Instr::MovsdLoad { dst: reg_f(b, &h, ko2), mem: mem_f(b, &h, ko2) },
            0x11 => Instr::MovsdStore { mem: mem_f(b, &h, ko2), src: reg_f(b, &h, ko2) },
            _ => Instr::FpArith {
                fop: fop_of(o2),
                dst: reg_f(b, &h, ko2),
                xsrc: xsrc_f(b, &h, ko2),
            },
        }
    } else {
        match o2 {
            0x6E => Instr::MovqToXmm { dst: reg_f(b, &h, ko2), src: rm_f(b, &h, ko2) },
            0x7E => Instr::MovqFromXmm { dst: rm_f(b, &h, ko2), src: reg_f(b, &h, ko2) },
            _ => Instr::Ucomisd { a: reg_f(b, &h, ko2), xsrc: xsrc_f(b, &h, ko2) },
        }
    }
}

// ---- the canonical encoder (the spec's `encode`) ----

fn bit(b: bool) -> u8 {
    u8::from(b)
}

fn rex(out: &mut Vec<u8>, w: bool, r: bool, x: bool, b: bool, force: bool) {
    if w || r || x || b || force {
        out.push(0x40 | (bit(w) << 3) | (bit(r) << 2) | (bit(x) << 1) | bit(b));
    }
}

fn enc_rr(out: &mut Vec<u8>, prefix: &[u8], w: bool, reg: u8, rm: u8, opc: &[u8], force: bool) {
    out.extend_from_slice(prefix);
    rex(out, w, reg >= 8, false, rm >= 8, force);
    out.extend_from_slice(opc);
    out.push(0xC0 | ((reg % 8) << 3) | (rm % 8));
}

fn enc_mem(out: &mut Vec<u8>, prefix: &[u8], w: bool, reg: u8, m: &Mem, opc: &[u8]) {
    let (ix, scale) = match &m.index {
        None => (4u8, 0u8),
        Some(i) => (i.reg, i.scale),
    };
    out.extend_from_slice(prefix);
    rex(out, w, reg >= 8, ix >= 8, m.base >= 8, false);
    out.extend_from_slice(opc);
    out.push(0x80 | ((reg % 8) << 3) | 4);
    out.push((scale << 6) | ((ix % 8) << 3) | (m.base % 8));
    out.extend_from_slice(&m.disp.to_le_bytes());
}

fn enc_xsrc(out: &mut Vec<u8>, prefix: &[u8], reg: u8, s: &XmmSrc, opc: &[u8]) {
    match s {
        XmmSrc::Reg(r) => enc_rr(out, prefix, false, reg, *r, opc, false),
        XmmSrc::Mem(m) => enc_mem(out, prefix, false, reg, m, opc),
    }
}

fn is64(sz: &Size) -> bool {
    matches!(sz, Size::W64)
}

fn alu_base(op: &AluOp) -> u8 {
    match op {
        AluOp::Add => 0x00,
        AluOp::Or => 0x08,
        AluOp::And => 0x20,
        AluOp::Sub => 0x28,
        AluOp::Xor => 0x30,
        AluOp::Cmp => 0x38,
    }
}

fn alu_ext(op: &AluOp) -> u8 {
    match op {
        AluOp::Add => 0,
        AluOp::Or => 1,
        AluOp::And => 4,
        AluOp::Sub => 5,
        AluOp::Xor => 6,
        AluOp::Cmp => 7,
    }
}

fn shift_ext(op: &ShiftOp) -> u8 {
    match op {
        ShiftOp::Shl => 4,
        ShiftOp::Shr => 5,
        ShiftOp::Sar => 7,
    }
}

fn fp_opcode(op: &BinOp) -> u8 {
    match op {
        BinOp::Add => 0x58,
        BinOp::Mul => 0x59,
        BinOp::Sub => 0x5C,
        BinOp::Div => 0x5E,
    }
}

/// The canonical encoding of `i` (the spec's `encode`).
pub fn encode(i: &Instr) -> Vec<u8> {
    let mut o = Vec::new();
    let o = &mut o;
    let none: &[u8] = &[];
    match i {
        Instr::MovRR { sz, dst, src } => enc_rr(o, none, is64(sz), *src, *dst, &[0x89], false),
        Instr::MovLoad { sz, dst, mem } => enc_mem(o, none, is64(sz), *dst, mem, &[0x8B]),
        Instr::MovStore { sz, mem, src } => enc_mem(o, none, is64(sz), *src, mem, &[0x89]),
        Instr::MovImm32 { dst, imm_u32 } => {
            rex(o, false, false, false, *dst >= 8, false);
            o.push(0xB8u8.wrapping_add(dst % 8));
            o.extend_from_slice(&imm_u32.to_le_bytes());
        }
        Instr::MovImm32S { dst, imm } => {
            enc_rr(o, none, true, 0, *dst, &[0xC7], false);
            o.extend_from_slice(&imm.to_le_bytes());
        }
        Instr::MovImm64 { dst, imm_u64 } => {
            rex(o, true, false, false, *dst >= 8, false);
            o.push(0xB8u8.wrapping_add(dst % 8));
            o.extend_from_slice(&imm_u64.to_le_bytes());
        }
        Instr::AluRR { alu, sz, dst, src } => {
            enc_rr(o, none, is64(sz), *src, *dst, &[alu_base(alu).wrapping_add(1)], false);
        }
        Instr::AluRM { alu, sz, dst, mem } => {
            enc_mem(o, none, is64(sz), *dst, mem, &[alu_base(alu).wrapping_add(3)]);
        }
        Instr::AluRI { alu, sz, dst, imm } => {
            enc_rr(o, none, is64(sz), alu_ext(alu), *dst, &[0x81], false);
            o.extend_from_slice(&imm.to_le_bytes());
        }
        Instr::TestRR { sz, a, b } => enc_rr(o, none, is64(sz), *b, *a, &[0x85], false),
        Instr::TestRI { sz, a, imm } => {
            enc_rr(o, none, is64(sz), 0, *a, &[0xF7], false);
            o.extend_from_slice(&imm.to_le_bytes());
        }
        Instr::Neg { sz, r } => enc_rr(o, none, is64(sz), 3, *r, &[0xF7], false),
        Instr::Not { sz, r } => enc_rr(o, none, is64(sz), 2, *r, &[0xF7], false),
        Instr::ShiftImm { shift, sz, r, count } => {
            enc_rr(o, none, is64(sz), shift_ext(shift), *r, &[0xC1], false);
            o.push(*count);
        }
        Instr::ShiftCl { shift, sz, r } => {
            enc_rr(o, none, is64(sz), shift_ext(shift), *r, &[0xD3], false);
        }
        Instr::ImulRR { sz, dst, src } => {
            enc_rr(o, none, is64(sz), *dst, *src, &[0x0F, 0xAF], false);
        }
        Instr::ImulRRI { sz, dst, src, imm } => {
            enc_rr(o, none, is64(sz), *dst, *src, &[0x69], false);
            o.extend_from_slice(&imm.to_le_bytes());
        }
        Instr::Jcc { cc, rel } => {
            o.extend_from_slice(&[0x0F, 0x80u8.wrapping_add(*cc)]);
            o.extend_from_slice(&rel.to_le_bytes());
        }
        Instr::Jmp { rel } => {
            o.push(0xE9);
            o.extend_from_slice(&rel.to_le_bytes());
        }
        Instr::Ret => o.push(0xC3),
        Instr::Cmovcc { cc, sz, dst, src } => {
            enc_rr(o, none, is64(sz), *dst, *src, &[0x0F, 0x40u8.wrapping_add(*cc)], false);
        }
        Instr::Setcc { cc, dst } => {
            let force = (4..8).contains(dst);
            enc_rr(o, none, false, 0, *dst, &[0x0F, 0x90u8.wrapping_add(*cc)], force);
        }
        Instr::FpArith { fop, dst, xsrc } => {
            enc_xsrc(o, &[0xF2], *dst, xsrc, &[0x0F, fp_opcode(fop)]);
        }
        Instr::Sqrtsd { dst, xsrc } => enc_xsrc(o, &[0xF2], *dst, xsrc, &[0x0F, 0x51]),
        Instr::Ucomisd { a, xsrc } => enc_xsrc(o, &[0x66], *a, xsrc, &[0x0F, 0x2E]),
        Instr::Cvtsi2sd { sz, dst, src } => {
            enc_rr(o, &[0xF2], is64(sz), *dst, *src, &[0x0F, 0x2A], false);
        }
        Instr::Cvttsd2si { sz, dst, src } => {
            enc_rr(o, &[0xF2], is64(sz), *dst, *src, &[0x0F, 0x2C], false);
        }
        Instr::Cvtsd2si { sz, dst, src } => {
            enc_rr(o, &[0xF2], is64(sz), *dst, *src, &[0x0F, 0x2D], false);
        }
        Instr::MovqToXmm { dst, src } => enc_rr(o, &[0x66], true, *dst, *src, &[0x0F, 0x6E], false),
        Instr::MovqFromXmm { dst, src } => {
            enc_rr(o, &[0x66], true, *src, *dst, &[0x0F, 0x7E], false);
        }
        Instr::MovsdLoad { dst, mem } => enc_mem(o, &[0xF2], false, *dst, mem, &[0x0F, 0x10]),
        Instr::MovsdStore { mem, src } => enc_mem(o, &[0xF2], false, *src, mem, &[0x0F, 0x11]),
    }
    core::mem::take(o)
}

/// The instruction is in the subset (the spec's `valid_instr`) for the
/// values `extract` can produce: registers are below 16 by construction, so
/// only a shift count can be out of range.
fn valid(i: &Instr) -> bool {
    match i {
        Instr::ShiftImm { sz, count, .. } => {
            let max = if is64(sz) { 63 } else { 31 };
            (1..=max).contains(count)
        }
        _ => true,
    }
}

/// The instruction the bytes begin with and its length, if they begin with
/// the canonical encoding of an instruction of the subset (the spec's `dec`).
pub fn decode(bytes: &[u8]) -> Option<(Instr, usize)> {
    let c = extract(bytes);
    if !valid(&c) {
        return None;
    }
    let e = encode(&c);
    if bytes.starts_with(&e) { Some((c, e.len())) } else { None }
}

// ---- the validator ----

/// What is known about one register (the spec's `Fact`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Fact {
    Unknown,
    Base(u8),
    Idx(u8, u8),
}

type Facts = [Fact; 16];
const NO_FACTS: Facts = [Fact::Unknown; 16];
const CTX: u8 = 15;
const SP: u8 = 4;
const CTX_SIZE: i64 = 512;
const EXIT_CODE_OFF: i64 = 256;

fn reserved(r: u8) -> bool {
    r == CTX || r == SP
}

fn fact_of(fs: &Facts, r: u8) -> Fact {
    fs.get(usize::from(r)).copied().unwrap_or(Fact::Unknown)
}

fn set_fact(fs: &mut Facts, r: u8, f: Fact) {
    if let Some(slot) = fs.get_mut(usize::from(r)) {
        *slot = f;
    }
}

/// The general register an instruction writes (the spec's `written_gpr`).
fn written_gpr(i: &Instr) -> Option<u8> {
    match i {
        Instr::MovRR { dst, .. }
        | Instr::MovLoad { dst, .. }
        | Instr::MovImm32 { dst, .. }
        | Instr::MovImm32S { dst, .. }
        | Instr::MovImm64 { dst, .. }
        | Instr::ImulRR { dst, .. }
        | Instr::ImulRRI { dst, .. }
        | Instr::Cmovcc { dst, .. }
        | Instr::Setcc { dst, .. }
        | Instr::Cvttsd2si { dst, .. }
        | Instr::Cvtsd2si { dst, .. }
        | Instr::MovqFromXmm { dst, .. } => Some(*dst),
        Instr::AluRR { alu, dst, .. }
        | Instr::AluRM { alu, dst, .. }
        | Instr::AluRI { alu, dst, .. } => {
            if matches!(alu, AluOp::Cmp) { None } else { Some(*dst) }
        }
        Instr::Neg { r, .. }
        | Instr::Not { r, .. }
        | Instr::ShiftImm { r, .. }
        | Instr::ShiftCl { r, .. } => Some(*r),
        _ => None,
    }
}

/// The memory access of an instruction: operand, size, store (the spec's
/// `mem_access`).
fn mem_access(i: &Instr) -> Option<(&Mem, i64, bool)> {
    let n = |sz: &Size| if is64(sz) { 8 } else { 4 };
    match i {
        Instr::MovLoad { sz, mem, .. } | Instr::AluRM { sz, mem, .. } => Some((mem, n(sz), false)),
        Instr::MovStore { sz, mem, .. } => Some((mem, n(sz), true)),
        Instr::FpArith { xsrc: XmmSrc::Mem(m), .. }
        | Instr::Sqrtsd { xsrc: XmmSrc::Mem(m), .. }
        | Instr::Ucomisd { xsrc: XmmSrc::Mem(m), .. } => Some((m, 8, false)),
        Instr::MovsdLoad { mem, .. } => Some((mem, 8, false)),
        Instr::MovsdStore { mem, .. } => Some((mem, 8, true)),
        _ => None,
    }
}

/// The spec's `access_ok`.
fn access_ok(fs: &Facts, m: &Mem, size: i64, store: bool) -> bool {
    let disp = i64::from(m.disp);
    if m.base == CTX {
        m.index.is_none()
            && disp >= 0
            && disp.saturating_add(size) <= CTX_SIZE
            && (!store || disp >= EXIT_CODE_OFF)
    } else {
        match &m.index {
            None => false,
            Some(ix) => {
                ix.scale == 0
                    && disp == 0
                    && match (fact_of(fs, m.base), fact_of(fs, ix.reg)) {
                        (Fact::Base(k), Fact::Idx(k2, n)) => k == k2 && size <= i64::from(n),
                        _ => false,
                    }
            }
        }
    }
}

/// The spec's `plain_ok`: updates `fs` and returns true if permitted.
fn plain_ok(fs: &mut Facts, i: &Instr) -> bool {
    if matches!(i, Instr::Ret) {
        return false;
    }
    if written_gpr(i).is_some_and(reserved) {
        return false;
    }
    if let Some((m, size, store)) = mem_access(i)
        && !access_ok(fs, m, size, store)
    {
        return false;
    }
    if matches!(i, Instr::Jmp { .. }) {
        *fs = NO_FACTS;
        return true;
    }
    if let Some(d) = written_gpr(i) {
        let f = match i {
            Instr::MovLoad { sz, mem, .. }
                if is64(sz)
                    && mem.base == CTX
                    && mem.index.is_none()
                    && (0..256).contains(&mem.disp)
                    && mem.disp % 16 == 0 =>
            {
                u8::try_from(mem.disp / 16).map_or(Fact::Unknown, Fact::Base)
            }
            _ => Fact::Unknown,
        };
        set_fact(fs, d, f);
    }
    true
}

/// A bounds-check sequence's parameters (the spec's `Chk`).
struct Chk {
    k: u8,
    n: u8,
    i: u8,
    t: u8,
    z: u8,
}

/// The spec's `check_unit_at`, with the parameters.
fn check_at(ins: &[Instr], j: usize) -> Option<Chk> {
    let w = ins.get(j..j.checked_add(8)?)?;
    let Some(Instr::MovRR { sz: Size::W64, dst: t, src: i }) = w.first() else {
        return None;
    };
    let Some(Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst: d1, imm: n }) = w.get(1) else {
        return None;
    };
    let Some(Instr::Jcc { cc: 2, .. }) = w.get(2) else {
        return None;
    };
    let Some(Instr::AluRM {
        alu: AluOp::Cmp,
        sz: Size::W64,
        dst: d3,
        mem: Mem { base: 15, index: None, disp },
    }) = w.get(3)
    else {
        return None;
    };
    let Some(Instr::Jcc { cc: 7, .. }) = w.get(4) else {
        return None;
    };
    let Some(Instr::MovImm32 { dst: z, imm_u32: 0 }) = w.get(5) else {
        return None;
    };
    let Some(Instr::AluRM {
        alu: AluOp::Cmp,
        sz: Size::W64,
        dst: d6,
        mem: Mem { base: 15, index: None, disp: disp6 },
    }) = w.get(6)
    else {
        return None;
    };
    let Some(Instr::Cmovcc { cc: 3, sz: Size::W64, dst: d7, src: s7 }) = w.get(7) else {
        return None;
    };
    if d1 != t || d3 != t || d6 != i || d7 != i || s7 != z || disp6 != disp {
        return None;
    }
    let off = disp.checked_sub(8)?;
    if off < 0 || off % 16 != 0 {
        return None;
    }
    let k = u8::try_from(off / 16).ok()?;
    let n = u8::try_from(*n).ok()?;
    if k >= 16 || !(1..=8).contains(&n) || i == t || i == z || t == z {
        return None;
    }
    if reserved(*i) || reserved(*t) || reserved(*z) {
        return None;
    }
    Some(Chk { k, n, i: *i, t: *t, z: *z })
}

/// The spec's `exit_unit_at`.
fn exit_at(ins: &[Instr], j: usize) -> bool {
    let Some(w) = ins.get(j..j.saturating_add(3)) else {
        return false;
    };
    matches!(
        (w.first(), w.get(1), w.get(2)),
        (
            Some(Instr::MovImm32 { dst: t, .. }),
            Some(Instr::MovStore { sz: Size::W64, mem: Mem { base: 15, index: None, disp: 256 }, src }),
            Some(Instr::Ret),
        ) if src == t && !reserved(*t)
    )
}

/// The jump displacement of a direct jump.
fn jump_rel(i: &Instr) -> Option<i32> {
    match i {
        Instr::Jcc { rel, .. } | Instr::Jmp { rel } => Some(*rel),
        _ => None,
    }
}

/// Whether `blob`, entered at the byte offsets `entries`, is accepted (the
/// spec's `accepted`, see [`crate::spec::accepted`]). One decode pass, one
/// scan; time and space linear in the blob.
pub fn validate(blob: &[u8], entries: &[usize]) -> bool {
    let len = blob.len();
    if len > 0x7FFF_FFFF || len == 0 {
        return false;
    }
    // Decode: the instructions and the offset each begins at.
    let mut ins: Vec<Instr> = Vec::new();
    let mut starts: Vec<usize> = Vec::new();
    let mut pos = 0usize;
    while pos < len {
        let Some((i, n)) = blob.get(pos..).and_then(decode) else {
            return false;
        };
        starts.push(pos);
        ins.push(i);
        pos = pos.saturating_add(n);
    }
    // Targets: the entries and every direct jump's target.
    let mut target = vec![false; len];
    for &e in entries {
        match target.get_mut(e) {
            Some(slot) => *slot = true,
            None => return false,
        }
    }
    for (j, i) in ins.iter().enumerate() {
        if let Some(rel) = jump_rel(i) {
            let next = starts.get(j.saturating_add(1)).copied().unwrap_or(len);
            let Some(t) = i64::try_from(next).ok().and_then(|n| n.checked_add(i64::from(rel)))
            else {
                return false;
            };
            let Some(slot) = usize::try_from(t).ok().and_then(|t| target.get_mut(t)) else {
                return false;
            };
            *slot = true;
        }
    }
    // The end: the last instruction is `ret` or `jmp`.
    if !matches!(ins.last(), Some(Instr::Ret | Instr::Jmp { .. })) {
        return false;
    }
    // The scan.
    let mut unit_start = vec![false; len];
    let mut fs = NO_FACTS;
    let mut j = 0usize;
    while let Some(i) = ins.get(j) {
        let Some(&here) = starts.get(j) else {
            return false;
        };
        if target.get(here).copied().unwrap_or(false) {
            fs = NO_FACTS;
        }
        if let Some(s) = unit_start.get_mut(here) {
            *s = true;
        }
        if exit_at(&ins, j) {
            fs = NO_FACTS;
            j = j.saturating_add(3);
        } else if let Some(c) = check_at(&ins, j) {
            set_fact(&mut fs, c.t, Fact::Unknown);
            set_fact(&mut fs, c.z, Fact::Unknown);
            set_fact(&mut fs, c.i, Fact::Idx(c.k, c.n));
            j = j.saturating_add(8);
        } else if plain_ok(&mut fs, i) {
            j = j.saturating_add(1);
        } else {
            return false;
        }
    }
    // Every target is a unit start.
    target.iter().zip(unit_start.iter()).all(|(t, u)| !*t || *u)
}
