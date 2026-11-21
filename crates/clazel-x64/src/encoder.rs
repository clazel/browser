//! The **executable encoder**: [`encode_exec`] writes the canonical encoding
//! of an instruction of the subset, and is proven equal to the specification
//! [`super::spec::encode`] for every form (jit.md J.3, J.6). It is the
//! building block of the executable decoder, which accepts bytes only if
//! they are exactly what this encoder writes for what it read.
//!
//! Every function ensures that the bytes it appends are the spec's
//! (`rex_seq`, `enc_rr`, `enc_rm_mem`, `le_bytes`), so the proof of
//! [`encode_exec`] is the composition of those facts.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The prefix byte as the spec's sequence: none for 0.
pub open spec fn pfx_seq(pf: u8) -> Seq<u8> {
    if pf == 0 {
        Seq::empty()
    } else {
        seq![pf]
    }
}

/// Four little-endian bytes depend only on the value modulo 2^32.
pub proof fn lemma_le_bytes_4_mod(v: int, u: int)
    requires
        u == v % 0x1_0000_0000,
    ensures
        le_bytes(v, 4) =~= le_bytes(u, 4),
{
    reveal_with_fuel(le_bytes, 5);
    let q = v / 0x1_0000_0000;
    assert(v == u + 0x1_0000_0000 * q);
    assert(v / 256 == u / 256 + 0x100_0000 * q) by (nonlinear_arith)
        requires
            v == u + 0x1_0000_0000 * q,
    ;
    let a = u / 256;
    assert((v / 256) / 256 == a / 256 + 0x1_0000 * q) by (nonlinear_arith)
        requires
            v / 256 == a + 0x100_0000 * q,
    ;
    let b = a / 256;
    assert(((v / 256) / 256) / 256 == b / 256 + 0x100 * q) by (nonlinear_arith)
        requires
            (v / 256) / 256 == b + 0x1_0000 * q,
    ;
    assert(v % 256 == u % 256) by (nonlinear_arith)
        requires
            v == u + 0x1_0000_0000 * q,
    ;
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(0x1_0000 * q, a, 256);
    assert(256 * (0x1_0000 * q) + a == v / 256);
    assert((v / 256) % 256 == (u / 256) % 256);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(0x100 * q, b, 256);
    assert(256 * (0x100 * q) + b == (v / 256) / 256);
    assert(((v / 256) / 256) % 256 == b % 256);
    vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(q, b / 256, 256);
    assert(256 * q + b / 256 == ((v / 256) / 256) / 256);
    assert((((v / 256) / 256) / 256) % 256 == (b / 256) % 256);
}

/// Appends the four little-endian bytes of `x`.
pub fn push_u32(out: &mut Vec<u8>, x: u32)
    ensures
        final(out)@ =~= old(out)@ + le_bytes(x as int, 4),
{
    reveal_with_fuel(le_bytes, 5);
    out.push((x % 256) as u8);
    out.push(((x / 256) % 256) as u8);
    out.push(((x / 65536) % 256) as u8);
    out.push((x / 16777216) as u8);
    assert(((x as int / 256) / 256) / 256 == x as int / 16777216);
    assert(((x as int / 256) / 256) == x as int / 65536);
    assert(out@ =~= old(out)@ + le_bytes(x as int, 4));
}

/// Appends the four little-endian bytes of `v`, two's complement.
pub fn push_i32(out: &mut Vec<u8>, v: i32)
    ensures
        final(out)@ =~= old(out)@ + le_bytes(v as int, 4),
{
    let x: u32 = if v >= 0 {
        v as u32
    } else {
        ((v as i64).wrapping_add(4294967296i64)) as u32
    };
    proof {
        assert(x as int == (v as int) % 0x1_0000_0000);
    }
    push_u32(out, x);
    proof {
        lemma_le_bytes_4_mod(v as int, x as int);
    }
}

/// Appends the eight little-endian bytes of `x`.
pub fn push_u64(out: &mut Vec<u8>, x: u64)
    ensures
        final(out)@ =~= old(out)@ + le_bytes(x as int, 8),
{
    let lo = (x % 0x1_0000_0000) as u32;
    let hi = (x / 0x1_0000_0000) as u32;
    push_u32(out, lo);
    push_u32(out, hi);
    proof {
        super::decoder_proofs::lemma_le_bytes_8(x as int);
        lemma_le_bytes_4_mod(x as int, lo as int);
        assert(out@ =~= old(out)@ + le_bytes(x as int, 8));
    }
}

/// Appends `opc`.
pub fn push_all(out: &mut Vec<u8>, opc: &[u8])
    ensures
        final(out)@ =~= old(out)@ + opc@,
{
    let mut k: usize = 0;
    while k < opc.len()
        invariant
            k <= opc.len(),
            out@ =~= old(out)@ + opc@.subrange(0, k as int),
        decreases opc.len() - k,
    {
        if let Some(bt) = opc.get(k) {
            out.push(*bt);
        }
        k = k.saturating_add(1);
        assert(opc@.subrange(0, k as int) =~= opc@.subrange(0, k as int - 1).push(opc@[k as int
            - 1]));
    }
    assert(opc@.subrange(0, opc.len() as int) =~= opc@);
}

/// Appends the `REX` prefix when [`rex_seq`] has one.
pub fn push_rex(out: &mut Vec<u8>, w: bool, r: bool, x: bool, b: bool, force: bool)
    ensures
        final(out)@ =~= old(out)@ + rex_seq(w, r, x, b, force),
{
    if w || r || x || b || force {
        let wv: u8 = if w {
            8
        } else {
            0
        };
        let rv: u8 = if r {
            4
        } else {
            0
        };
        let xv: u8 = if x {
            2
        } else {
            0
        };
        let bv: u8 = if b {
            1
        } else {
            0
        };
        let v: u8 = 0x40u8.saturating_add(wv).saturating_add(rv).saturating_add(xv).saturating_add(bv);
        out.push(v);
        assert(v as int == 0x40 + 8 * bool_to_bit(w) + 4 * bool_to_bit(r) + 2 * bool_to_bit(x)
            + bool_to_bit(b));
    }
}

/// Appends a register-direct instruction (the spec's `enc_rr`), `pf` being
/// the mandatory prefix or 0.
pub fn enc_rr_exec(out: &mut Vec<u8>, pf: u8, w: bool, reg: u8, rm: u8, opc: &[u8], force: bool)
    requires
        reg < 16,
        rm < 16,
    ensures
        final(out)@ =~= old(out)@ + enc_rr(pfx_seq(pf), w, reg, rm, opc@, force),
{
    if pf != 0 {
        out.push(pf);
    }
    push_rex(out, w, reg >= 8, false, rm >= 8, force);
    push_all(out, opc);
    out.push(0xC0u8.saturating_add((reg % 8).saturating_mul(8)).saturating_add(rm % 8));
    assert(out@ =~= old(out)@ + enc_rr(pfx_seq(pf), w, reg, rm, opc@, force));
}

/// Appends a memory instruction (the spec's `enc_rm_mem`).
pub fn enc_mem_exec(out: &mut Vec<u8>, pf: u8, w: bool, reg: u8, m: &Mem, opc: &[u8])
    requires
        reg < 16,
        mem_ok(*m),
    ensures
        final(out)@ =~= old(out)@ + enc_rm_mem(pfx_seq(pf), w, reg, *m, opc@),
{
    let ix: u8 = match &m.index {
        None => 4,
        Some(i) => i.reg,
    };
    let scale: u8 = match &m.index {
        None => 0,
        Some(i) => i.scale,
    };
    if pf != 0 {
        out.push(pf);
    }
    push_rex(out, w, reg >= 8, ix >= 8, m.base >= 8, false);
    push_all(out, opc);
    out.push(0x80u8.saturating_add((reg % 8).saturating_mul(8)).saturating_add(4));
    out.push(scale.saturating_mul(64).saturating_add((ix % 8).saturating_mul(8)).saturating_add(m.base % 8));
    push_i32(out, m.disp);
    assert(ix as int == sib_index_reg(*m));
    assert(scale as int == sib_scale(*m));
    assert(out@ =~= old(out)@ + enc_rm_mem(pfx_seq(pf), w, reg, *m, opc@));
}

/// Appends an instruction with an XMM source operand.
pub fn enc_xsrc_exec(out: &mut Vec<u8>, pf: u8, reg: u8, s: &XmmSrc, opc: &[u8])
    requires
        reg < 16,
        xmm_src_ok(*s),
    ensures
        final(out)@ =~= old(out)@ + enc_xmm_src(pfx_seq(pf), false, reg, *s, opc@),
{
    match s {
        XmmSrc::Reg(r) => enc_rr_exec(out, pf, false, reg, *r, opc, false),
        XmmSrc::Mem(m) => enc_mem_exec(out, pf, false, reg, m, opc),
    }
}

/// `REX.W` for an operand size.
pub fn is64_exec(sz: &Size) -> (r: bool)
    ensures
        r == is64(*sz),
{
    match sz {
        Size::W64 => true,
        Size::W32 => false,
    }
}

/// The opcode base of a group-1 operation.
pub fn alu_base_exec(op: &AluOp) -> (r: u8)
    ensures
        r as int == alu_base(*op),
{
    match op {
        AluOp::Add => 0x00,
        AluOp::Or => 0x08,
        AluOp::And => 0x20,
        AluOp::Sub => 0x28,
        AluOp::Xor => 0x30,
        AluOp::Cmp => 0x38,
    }
}

/// The ModR/M `reg` extension of a group-1 operation.
pub fn alu_ext_exec(op: &AluOp) -> (r: u8)
    ensures
        r as int == alu_ext(*op),
{
    match op {
        AluOp::Add => 0,
        AluOp::Or => 1,
        AluOp::And => 4,
        AluOp::Sub => 5,
        AluOp::Xor => 6,
        AluOp::Cmp => 7,
    }
}

/// The ModR/M `reg` extension of a shift.
pub fn shift_ext_exec(op: &ShiftOp) -> (r: u8)
    ensures
        r as int == shift_ext(*op),
{
    match op {
        ShiftOp::Shl => 4,
        ShiftOp::Shr => 5,
        ShiftOp::Sar => 7,
    }
}

/// The second opcode byte of a scalar double operation.
pub fn fp_opcode_exec(op: &BinOp) -> (r: u8)
    ensures
        r as int == fp_opcode(*op),
{
    match op {
        BinOp::Add => 0x58,
        BinOp::Mul => 0x59,
        BinOp::Sub => 0x5C,
        BinOp::Div => 0x5E,
    }
}

/// **The executable encoder**: the canonical encoding of an instruction of
/// the subset, equal to the spec's [`encode`].
#[verifier::spinoff_prover]
#[verifier::rlimit(3000)]
pub fn encode_exec(i: &Instr) -> (out: Vec<u8>)
    requires
        valid_instr(*i),
    ensures
        out@ =~= encode(*i),
{
    let mut o: Vec<u8> = Vec::new();
    let out = &mut o;
    match i {
        Instr::MovRR { sz, dst, src } => {
            enc_rr_exec(out, 0, is64_exec(sz), *src, *dst, &[0x89], false);
        },
        Instr::MovLoad { sz, dst, mem } => {
            enc_mem_exec(out, 0, is64_exec(sz), *dst, mem, &[0x8B]);
        },
        Instr::MovStore { sz, mem, src } => {
            enc_mem_exec(out, 0, is64_exec(sz), *src, mem, &[0x89]);
        },
        Instr::MovImm32 { dst, imm_u32 } => {
            push_rex(out, false, false, false, *dst >= 8, false);
            out.push(0xB8u8.saturating_add(*dst % 8));
            push_u32(out, *imm_u32);
        },
        Instr::MovImm32S { dst, imm } => {
            enc_rr_exec(out, 0, true, 0, *dst, &[0xC7], false);
            push_i32(out, *imm);
        },
        Instr::MovImm64 { dst, imm_u64 } => {
            push_rex(out, true, false, false, *dst >= 8, false);
            out.push(0xB8u8.saturating_add(*dst % 8));
            push_u64(out, *imm_u64);
        },
        Instr::AluRR { alu, sz, dst, src } => {
            let b = alu_base_exec(alu);
            enc_rr_exec(out, 0, is64_exec(sz), *src, *dst, &[b.saturating_add(1)], false);
        },
        Instr::AluRM { alu, sz, dst, mem } => {
            let b = alu_base_exec(alu);
            enc_mem_exec(out, 0, is64_exec(sz), *dst, mem, &[b.saturating_add(3)]);
        },
        Instr::AluRI { alu, sz, dst, imm } => {
            let e = alu_ext_exec(alu);
            enc_rr_exec(out, 0, is64_exec(sz), e, *dst, &[0x81], false);
            push_i32(out, *imm);
        },
        Instr::TestRR { sz, a, b } => {
            enc_rr_exec(out, 0, is64_exec(sz), *b, *a, &[0x85], false);
        },
        Instr::TestRI { sz, a, imm } => {
            enc_rr_exec(out, 0, is64_exec(sz), 0, *a, &[0xF7], false);
            push_i32(out, *imm);
        },
        Instr::Neg { sz, r } => {
            enc_rr_exec(out, 0, is64_exec(sz), 3, *r, &[0xF7], false);
        },
        Instr::Not { sz, r } => {
            enc_rr_exec(out, 0, is64_exec(sz), 2, *r, &[0xF7], false);
        },
        Instr::ShiftImm { shift, sz, r, count } => {
            let e = shift_ext_exec(shift);
            enc_rr_exec(out, 0, is64_exec(sz), e, *r, &[0xC1], false);
            out.push(*count);
        },
        Instr::ShiftCl { shift, sz, r } => {
            let e = shift_ext_exec(shift);
            enc_rr_exec(out, 0, is64_exec(sz), e, *r, &[0xD3], false);
        },
        Instr::ImulRR { sz, dst, src } => {
            enc_rr_exec(out, 0, is64_exec(sz), *dst, *src, &[0x0F, 0xAF], false);
        },
        Instr::ImulRRI { sz, dst, src, imm } => {
            enc_rr_exec(out, 0, is64_exec(sz), *dst, *src, &[0x69], false);
            push_i32(out, *imm);
        },
        Instr::Jcc { cc, rel } => {
            out.push(0x0F);
            out.push(0x80u8.saturating_add(*cc));
            push_i32(out, *rel);
        },
        Instr::Jmp { rel } => {
            out.push(0xE9);
            push_i32(out, *rel);
        },
        Instr::Ret => {
            out.push(0xC3);
        },
        Instr::Cmovcc { cc, sz, dst, src } => {
            enc_rr_exec(out, 0, is64_exec(sz), *dst, *src, &[0x0F, 0x40u8.saturating_add(*cc)], false);
        },
        Instr::Setcc { cc, dst } => {
            enc_rr_exec(out, 0, false, 0, *dst, &[0x0F, 0x90u8.saturating_add(*cc)], 4 <= *dst && *dst < 8);
        },
        Instr::FpArith { fop, dst, xsrc } => {
            let o2 = fp_opcode_exec(fop);
            enc_xsrc_exec(out, 0xF2, *dst, xsrc, &[0x0F, o2]);
        },
        Instr::Sqrtsd { dst, xsrc } => {
            enc_xsrc_exec(out, 0xF2, *dst, xsrc, &[0x0F, 0x51]);
        },
        Instr::Ucomisd { a, xsrc } => {
            enc_xsrc_exec(out, 0x66, *a, xsrc, &[0x0F, 0x2E]);
        },
        Instr::Cvtsi2sd { sz, dst, src } => {
            enc_rr_exec(out, 0xF2, is64_exec(sz), *dst, *src, &[0x0F, 0x2A], false);
        },
        Instr::Cvttsd2si { sz, dst, src } => {
            enc_rr_exec(out, 0xF2, is64_exec(sz), *dst, *src, &[0x0F, 0x2C], false);
        },
        Instr::Cvtsd2si { sz, dst, src } => {
            enc_rr_exec(out, 0xF2, is64_exec(sz), *dst, *src, &[0x0F, 0x2D], false);
        },
        Instr::MovqToXmm { dst, src } => {
            enc_rr_exec(out, 0x66, true, *dst, *src, &[0x0F, 0x6E], false);
        },
        Instr::MovqFromXmm { dst, src } => {
            enc_rr_exec(out, 0x66, true, *src, *dst, &[0x0F, 0x7E], false);
        },
        Instr::MovsdLoad { dst, mem } => {
            enc_mem_exec(out, 0xF2, false, *dst, mem, &[0x0F, 0x10]);
        },
        Instr::MovsdStore { mem, src } => {
            enc_mem_exec(out, 0xF2, false, *src, mem, &[0x0F, 0x11]);
        },
    }
    assert(o@ =~= encode(*i));
    o
}

} // verus!
