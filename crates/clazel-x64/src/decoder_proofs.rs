//! Proofs about [`super::decoder`]: its completeness, `dec(encode(i) + rest)
//! == Some(i)` for every instruction of the subset, and from it the
//! prefix-freeness of the canonical encoding.

pub use super::decoder::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Four little-endian bytes read back.
pub proof fn lemma_le32(pre: Seq<u8>, v: int, rest: Seq<u8>)
    ensures
        le32(pre + le_bytes(v, 4) + rest, pre.len() as int) == v % 0x1_0000_0000,
{
    reveal_with_fuel(le_bytes, 5);
    let s = pre + le_bytes(v, 4) + rest;
    let p = pre.len() as int;
    assert(le_bytes(v, 4).len() == 4);
    assert(at(s, p) == v % 256);
    assert(at(s, p + 1) == (v / 256) % 256);
    assert(at(s, p + 2) == ((v / 256) / 256) % 256);
    assert(at(s, p + 3) == (((v / 256) / 256) / 256) % 256);
    assert(le32(s, p) == v % 0x1_0000_0000);
}

/// Eight little-endian bytes are four, then four of the quotient.
pub proof fn lemma_le_bytes_8(v: int)
    ensures
        le_bytes(v, 8) =~= le_bytes(v, 4) + le_bytes(v / 0x1_0000_0000, 4),
{
    reveal_with_fuel(le_bytes, 9);
    let w = v / 0x1_0000_0000;
    assert(((v / 256) / 256) / 256 / 256 == w);
    assert(le_bytes(v, 8).len() == 8);
    assert((le_bytes(v, 4) + le_bytes(w, 4)).len() == 8);
    assert forall|k: int| 0 <= k < 8 implies le_bytes(v, 8)[k] == (le_bytes(v, 4) + le_bytes(
        w,
        4,
    ))[k] by {
        assert(((((v / 256) / 256) / 256) / 256) / 256 == w / 256);
        assert((((((v / 256) / 256) / 256) / 256) / 256) / 256 == (w / 256) / 256);
        assert(((((((v / 256) / 256) / 256) / 256) / 256) / 256) / 256 == ((w / 256) / 256) / 256);
    }
}

/// Eight little-endian bytes read back.
pub proof fn lemma_le64(pre: Seq<u8>, v: int, rest: Seq<u8>)
    ensures
        le64(pre + le_bytes(v, 8) + rest, pre.len() as int) == v % 0x1_0000_0000_0000_0000,
{
    lemma_le_bytes_8(v);
    let w = v / 0x1_0000_0000;
    let s = pre + le_bytes(v, 8) + rest;
    let p = pre.len() as int;
    assert(s =~= pre + le_bytes(v, 4) + (le_bytes(w, 4) + rest));
    lemma_le32(pre, v, le_bytes(w, 4) + rest);
    assert(s =~= (pre + le_bytes(v, 4)) + le_bytes(w, 4) + rest);
    lemma_le32(pre + le_bytes(v, 4), w, rest);
    reveal_with_fuel(le_bytes, 5);
    assert((pre + le_bytes(v, 4)).len() == p + 4);
    assert(le64(s, p) == v % 0x1_0000_0000_0000_0000);
}

/// The code [`Head`] gives a mandatory prefix.
pub open spec fn pfcode(pfx: Seq<u8>) -> int {
    if pfx.len() == 0 {
        0
    } else {
        pfx[0] as int
    }
}

/// `pfx` is none, `66` or `F2`.
pub open spec fn pfx_ok(pfx: Seq<u8>) -> bool {
    pfx.len() <= 1 && (pfx.len() == 1 ==> pfx[0] == 0x66 || pfx[0] == 0xF2)
}

/// `rest` starts with a byte that is neither a prefix nor `REX`.
pub open spec fn plain_start(rest: Seq<u8>) -> bool {
    rest.len() >= 1 && !(0x40 <= rest[0] <= 0x4F) && rest[0] != 0x66 && rest[0] != 0xF2
}

/// What [`head`] reads from a prefix, a `REX` byte and the rest.
pub proof fn lemma_head(pfx: Seq<u8>, w: bool, r: bool, x: bool, bb: bool, force: bool, rest: Seq<u8>)
    requires
        pfx_ok(pfx),
        plain_start(rest),
    ensures
        ({
            let e = pfx + rex_seq(w, r, x, bb, force) + rest;
            let h = head(e);
            &&& h.pf == pfcode(pfx)
            &&& h.rexp == (w || r || x || bb || force)
            &&& h.w == w
            &&& h.r == bool_to_bit(r)
            &&& h.x == bool_to_bit(x)
            &&& h.bb == bool_to_bit(bb)
            &&& h.kop == pfx.len() + rex_seq(w, r, x, bb, force).len()
            &&& forall|j: int|
                0 <= j < rest.len() ==> at(e, h.kop + j) == #[trigger] rest[j] as int
        }),
{
    let e = pfx + rex_seq(w, r, x, bb, force) + rest;
    let h = head(e);
    let rx = rex_seq(w, r, x, bb, force);
    if w || r || x || bb || force {
        assert(rx.len() == 1);
        assert(rx[0] == (0x40 + 8 * bool_to_bit(w) + 4 * bool_to_bit(r) + 2 * bool_to_bit(x)
            + bool_to_bit(bb)) as u8);
    } else {
        assert(rx.len() == 0);
    }
    assert(h.pf == pfcode(pfx));
    assert(h.kop == pfx.len() + rx.len());
    assert forall|j: int| 0 <= j < rest.len() implies at(e, h.kop + j) == #[trigger] rest[j] as int by {}
}

/// The ModR/M byte of a register-direct instruction, in numbers.
pub proof fn lemma_modrm_rr(reg: int, rm: int)
    requires
        0 <= reg < 16,
        0 <= rm < 16,
    ensures
        0 <= 192 + (reg % 8) * 8 + rm % 8 < 256,
        (192 + (reg % 8) * 8 + rm % 8) / 64 == 3,
        ((192 + (reg % 8) * 8 + rm % 8) / 8) % 8 + 8 * (if reg >= 8 {
            1int
        } else {
            0
        }) == reg,
        (192 + (reg % 8) * 8 + rm % 8) % 8 + 8 * (if rm >= 8 {
            1int
        } else {
            0
        }) == rm,
{
}

/// The ModR/M byte of a memory instruction with a SIB byte, in numbers.
pub proof fn lemma_modrm_mem(reg: int)
    requires
        0 <= reg < 16,
    ensures
        0 <= 128 + (reg % 8) * 8 + 4 < 256,
        (128 + (reg % 8) * 8 + 4) / 64 == 2,
        (((128 + (reg % 8) * 8 + 4) / 8) % 8) + 8 * (if reg >= 8 {
            1int
        } else {
            0
        }) == reg,
{
}

/// The SIB byte, in numbers.
pub proof fn lemma_sib(scale: int, ix: int, base: int)
    requires
        0 <= scale < 4,
        0 <= ix < 16,
        0 <= base < 16,
    ensures
        0 <= scale * 64 + (ix % 8) * 8 + base % 8 < 256,
        (scale * 64 + (ix % 8) * 8 + base % 8) % 8 + 8 * (if base >= 8 {
            1int
        } else {
            0
        }) == base,
        ((scale * 64 + (ix % 8) * 8 + base % 8) / 8) % 8 + 8 * (if ix >= 8 {
            1int
        } else {
            0
        }) == ix,
        (scale * 64 + (ix % 8) * 8 + base % 8) / 64 == scale,
{
}

/// What [`extract`]'s field readers see in a register-direct instruction
/// followed by `t`: the prefix, `W`, the opcode bytes, `mod = 11`, both
/// registers, and where the tail begins.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_rr(
    pfx: Seq<u8>,
    w: bool,
    reg: u8,
    rm: u8,
    opc: Seq<u8>,
    force: bool,
    t: Seq<u8>,
)
    requires
        reg < 16,
        rm < 16,
        pfx_ok(pfx),
        plain_start(opc),
    ensures
        ({
            let e = enc_rr(pfx, w, reg, rm, opc, force) + t;
            let h = head(e);
            let ko = h.kop + opc.len();
            &&& h.pf == pfcode(pfx)
            &&& h.w == w
            &&& forall|j: int| 0 <= j < opc.len() ==> at(e, h.kop + j) == #[trigger] opc[j] as int
            &&& mod_f(e, ko) == 3
            &&& reg_f(e, h, ko) == reg
            &&& rm_f(e, h, ko) == rm
            &&& ko + 1 == enc_rr(pfx, w, reg, rm, opc, force).len()
            &&& forall|j: int|
                0 <= j < t.len() ==> at(e, ko + 1 + j) == #[trigger] t[j] as int
        }),
{
    lemma_modrm_rr(reg as int, rm as int);
    let rx = rex_seq(w, reg >= 8, false, rm >= 8, force);
    let mb = modrm(3, reg as int, rm as int);
    let body = opc + seq![mb] + t;
    assert(plain_start(body));
    lemma_head(pfx, w, reg >= 8, false, rm >= 8, force, body);
    let e = enc_rr(pfx, w, reg, rm, opc, force) + t;
    assert(e =~= pfx + rx + body);
    let h = head(e);
    let ko = h.kop + opc.len();
    assert(body[opc.len() as int] == mb);
    assert(at(e, ko) == mb as int);
    assert(mb as int == 192 + (reg as int % 8) * 8 + rm as int % 8);
    assert forall|j: int| 0 <= j < opc.len() implies at(e, h.kop + j) == #[trigger] opc[j] as int by {
        assert(body[j] == opc[j]);
    }
    assert forall|j: int| 0 <= j < t.len() implies at(e, ko + 1 + j) == #[trigger] t[j] as int by {
        assert(body[opc.len() + 1 + j] == t[j]);
    }
}

/// The SIB byte of a memory operand, as a number.
pub open spec fn sib_int(m: Mem) -> int {
    sib_scale(m) * 64 + (sib_index_reg(m) % 8) * 8 + (m.base as int) % 8
}

/// The memory operand read back from its SIB byte, `REX.X`, `REX.B` and
/// displacement word is the one encoded.
pub proof fn lemma_mem_of(m: Mem)
    requires
        mem_ok(m),
    ensures
        mem_of(
            sib_int(m),
            bool_to_bit(sib_index_reg(m) >= 8),
            bool_to_bit(m.base >= 8),
            (m.disp as int) % 0x1_0000_0000,
        ) == m,
{
    let ix = sib_index_reg(m);
    lemma_sib(sib_scale(m), ix, m.base as int);
    lemma_sx32(m.disp as int);
    match m.index {
        None => {
            assert(ix == 4);
        },
        Some(i) => {
            assert(ix == i.reg as int);
        },
    }
}

/// The same for a memory operand with `mod = 10` and a SIB byte: the
/// operand read back is the one encoded.
#[verifier::spinoff_prover]
#[verifier::rlimit(400)]
pub proof fn lemma_mem(pfx: Seq<u8>, w: bool, reg: u8, m: Mem, opc: Seq<u8>, t: Seq<u8>)
    requires
        reg < 16,
        mem_ok(m),
        pfx_ok(pfx),
        plain_start(opc),
    ensures
        ({
            let e = enc_rm_mem(pfx, w, reg, m, opc) + t;
            let h = head(e);
            let ko = h.kop + opc.len();
            &&& h.pf == pfcode(pfx)
            &&& h.w == w
            &&& forall|j: int| 0 <= j < opc.len() ==> at(e, h.kop + j) == #[trigger] opc[j] as int
            &&& mod_f(e, ko) == 2
            &&& reg_f(e, h, ko) == reg
            &&& mem_f(e, h, ko) == m
            &&& ko + 6 == enc_rm_mem(pfx, w, reg, m, opc).len()
            &&& forall|j: int|
                0 <= j < t.len() ==> at(e, ko + 6 + j) == #[trigger] t[j] as int
        }),
{
    let ix = sib_index_reg(m);
    lemma_modrm_mem(reg as int);
    lemma_sib(sib_scale(m), ix, m.base as int);
    let rx = rex_seq(w, reg >= 8, ix >= 8, m.base >= 8, false);
    let mb = modrm(2, reg as int, 4);
    let sibv = (sib_scale(m) * 64 + (ix % 8) * 8 + (m.base as int) % 8) as u8;
    let dispb = le_bytes(m.disp as int, 4);
    reveal_with_fuel(le_bytes, 5);
    assert(dispb.len() == 4);
    let body = opc + seq![mb, sibv] + dispb + t;
    assert(plain_start(body));
    lemma_head(pfx, w, reg >= 8, ix >= 8, m.base >= 8, false, body);
    let e = enc_rm_mem(pfx, w, reg, m, opc) + t;
    assert(e =~= pfx + rx + body);
    let h = head(e);
    let ko = h.kop + opc.len();
    assert(body[opc.len() as int] == mb);
    assert(body[(opc.len() + 1) as int] == sibv);
    assert(at(e, ko) == mb as int);
    assert(at(e, ko + 1) == sibv as int);
    let pre = pfx + rx + opc + seq![mb, sibv];
    assert(e =~= pre + dispb + t);
    assert(pre.len() == ko + 2);
    lemma_le32(pre, m.disp as int, t);
    lemma_sx32(m.disp as int);
    lemma_mem_of(m);
    assert(at(e, ko + 1) == sib_int(m));
    assert(mem_f(e, h, ko) == mem_of(
        sib_int(m),
        bool_to_bit(ix >= 8),
        bool_to_bit(m.base >= 8),
        (m.disp as int) % 0x1_0000_0000,
    ));
    assert forall|j: int| 0 <= j < opc.len() implies at(e, h.kop + j) == #[trigger] opc[j] as int by {
        assert(body[j] == opc[j]);
    }
    assert forall|j: int| 0 <= j < t.len() implies at(e, ko + 6 + j) == #[trigger] t[j] as int by {
        assert(body[opc.len() + 6 + j] == t[j]);
    }
}

/// A register-direct instruction with a 32-bit immediate after the ModR/M
/// byte: [`lemma_rr`] with `t` the immediate then `rest`, and the immediate
/// read back.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_rr_imm(
    pfx: Seq<u8>,
    w: bool,
    reg: u8,
    rm: u8,
    opc: Seq<u8>,
    imm: i32,
    rest: Seq<u8>,
)
    requires
        reg < 16,
        rm < 16,
        pfx_ok(pfx),
        plain_start(opc),
    ensures
        ({
            let e = enc_rr(pfx, w, reg, rm, opc, false) + le_bytes(imm as int, 4) + rest;
            let h = head(e);
            let ko = h.kop + opc.len();
            &&& h.pf == pfcode(pfx)
            &&& h.w == w
            &&& forall|j: int| 0 <= j < opc.len() ==> at(e, h.kop + j) == #[trigger] opc[j] as int
            &&& mod_f(e, ko) == 3
            &&& ext_f(e, ko) == (reg % 8) as int
            &&& reg_f(e, h, ko) == reg
            &&& rm_f(e, h, ko) == rm
            &&& sx32(le32(e, ko + 1)) == imm as int
        }),
{
    let t = le_bytes(imm as int, 4) + rest;
    lemma_rr(pfx, w, reg, rm, opc, false, t);
    let pre = enc_rr(pfx, w, reg, rm, opc, false);
    let e = pre + le_bytes(imm as int, 4) + rest;
    assert(e =~= pre + t);
    lemma_le32(pre, imm as int, rest);
    lemma_sx32(imm as int);
    lemma_modrm_rr(reg as int, rm as int);
}

/// The immediate of a 4-byte value read back, unsigned.
pub proof fn lemma_dst_low(dst: u8)
    requires
        dst < 16,
    ensures
        (dst % 8) as int + 8 * bool_to_bit(dst >= 8) == dst as int,
{
}

// ---- completeness, one lemma per instruction ----
//
// Each says: `extract` of the canonical encoding of the instruction,
// followed by anything, is the instruction. The proof calls the shape lemma
// ([`lemma_rr`], [`lemma_mem`], ...) and leaves the rest to evaluating
// `extract` on the facts it gives.

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_mov_rr(sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovRR { sz, dst, src }),
    ensures
        extract(encode(Instr::MovRR { sz, dst, src }) + rest) == (Instr::MovRR { sz, dst, src }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), src, dst, seq![0x89u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_alu_rr(alu: AluOp, sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::AluRR { alu, sz, dst, src }),
    ensures
        extract(encode(Instr::AluRR { alu, sz, dst, src }) + rest) == (Instr::AluRR {
            alu,
            sz,
            dst,
            src,
        }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), src, dst, seq![(alu_base(alu) + 1) as u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_test_rr(sz: Size, a: u8, b: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::TestRR { sz, a, b }),
    ensures
        extract(encode(Instr::TestRR { sz, a, b }) + rest) == (Instr::TestRR { sz, a, b }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), b, a, seq![0x85u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_neg(sz: Size, r: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Neg { sz, r }),
    ensures
        extract(encode(Instr::Neg { sz, r }) + rest) == (Instr::Neg { sz, r }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), 3, r, seq![0xF7u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_not(sz: Size, r: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Not { sz, r }),
    ensures
        extract(encode(Instr::Not { sz, r }) + rest) == (Instr::Not { sz, r }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), 2, r, seq![0xF7u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_shift_cl(shift: ShiftOp, sz: Size, r: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::ShiftCl { shift, sz, r }),
    ensures
        extract(encode(Instr::ShiftCl { shift, sz, r }) + rest) == (Instr::ShiftCl { shift, sz, r }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), shift_ext(shift) as u8, r, seq![0xD3u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_imul_rr(sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::ImulRR { sz, dst, src }),
    ensures
        extract(encode(Instr::ImulRR { sz, dst, src }) + rest) == (Instr::ImulRR { sz, dst, src }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), dst, src, seq![0x0Fu8, 0xAFu8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_cmovcc(cc: u8, sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Cmovcc { cc, sz, dst, src }),
    ensures
        extract(encode(Instr::Cmovcc { cc, sz, dst, src }) + rest) == (Instr::Cmovcc {
            cc,
            sz,
            dst,
            src,
        }),
{
    reveal(extract);
    lemma_rr(Seq::empty(), is64(sz), dst, src, seq![0x0Fu8, (0x40 + cc as int) as u8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_setcc(cc: u8, dst: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Setcc { cc, dst }),
    ensures
        extract(encode(Instr::Setcc { cc, dst }) + rest) == (Instr::Setcc { cc, dst }),
{
    reveal(extract);
    lemma_rr(
        Seq::empty(),
        false,
        0,
        dst,
        seq![0x0Fu8, (0x90 + cc as int) as u8],
        4 <= dst && dst < 8,
        rest,
    );
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_cvtsi2sd(sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Cvtsi2sd { sz, dst, src }),
    ensures
        extract(encode(Instr::Cvtsi2sd { sz, dst, src }) + rest) == (Instr::Cvtsi2sd {
            sz,
            dst,
            src,
        }),
{
    reveal(extract);
    lemma_rr(seq![0xF2u8], is64(sz), dst, src, seq![0x0Fu8, 0x2Au8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_cvttsd2si(sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Cvttsd2si { sz, dst, src }),
    ensures
        extract(encode(Instr::Cvttsd2si { sz, dst, src }) + rest) == (Instr::Cvttsd2si {
            sz,
            dst,
            src,
        }),
{
    reveal(extract);
    lemma_rr(seq![0xF2u8], is64(sz), dst, src, seq![0x0Fu8, 0x2Cu8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_cvtsd2si(sz: Size, dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::Cvtsd2si { sz, dst, src }),
    ensures
        extract(encode(Instr::Cvtsd2si { sz, dst, src }) + rest) == (Instr::Cvtsd2si {
            sz,
            dst,
            src,
        }),
{
    reveal(extract);
    lemma_rr(seq![0xF2u8], is64(sz), dst, src, seq![0x0Fu8, 0x2Du8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_movq_to_xmm(dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovqToXmm { dst, src }),
    ensures
        extract(encode(Instr::MovqToXmm { dst, src }) + rest) == (Instr::MovqToXmm { dst, src }),
{
    reveal(extract);
    lemma_rr(seq![0x66u8], true, dst, src, seq![0x0Fu8, 0x6Eu8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_movq_from_xmm(dst: u8, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovqFromXmm { dst, src }),
    ensures
        extract(encode(Instr::MovqFromXmm { dst, src }) + rest) == (Instr::MovqFromXmm {
            dst,
            src,
        }),
{
    reveal(extract);
    lemma_rr(seq![0x66u8], true, src, dst, seq![0x0Fu8, 0x7Eu8], false, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_fp_arith(fop: BinOp, dst: u8, xsrc: XmmSrc, rest: Seq<u8>)
    requires
        valid_instr(Instr::FpArith { fop, dst, xsrc }),
    ensures
        extract(encode(Instr::FpArith { fop, dst, xsrc }) + rest) == (Instr::FpArith {
            fop,
            dst,
            xsrc,
        }),
{
    reveal(extract);
    let opc = seq![0x0Fu8, fp_opcode(fop) as u8];
    match xsrc {
        XmmSrc::Reg(r) => lemma_rr(seq![0xF2u8], false, dst, r, opc, false, rest),
        XmmSrc::Mem(m) => lemma_mem(seq![0xF2u8], false, dst, m, opc, rest),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_sqrtsd(dst: u8, xsrc: XmmSrc, rest: Seq<u8>)
    requires
        valid_instr(Instr::Sqrtsd { dst, xsrc }),
    ensures
        extract(encode(Instr::Sqrtsd { dst, xsrc }) + rest) == (Instr::Sqrtsd { dst, xsrc }),
{
    reveal(extract);
    let opc = seq![0x0Fu8, 0x51u8];
    match xsrc {
        XmmSrc::Reg(r) => lemma_rr(seq![0xF2u8], false, dst, r, opc, false, rest),
        XmmSrc::Mem(m) => lemma_mem(seq![0xF2u8], false, dst, m, opc, rest),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_ucomisd(a: u8, xsrc: XmmSrc, rest: Seq<u8>)
    requires
        valid_instr(Instr::Ucomisd { a, xsrc }),
    ensures
        extract(encode(Instr::Ucomisd { a, xsrc }) + rest) == (Instr::Ucomisd { a, xsrc }),
{
    reveal(extract);
    let opc = seq![0x0Fu8, 0x2Eu8];
    match xsrc {
        XmmSrc::Reg(r) => lemma_rr(seq![0x66u8], false, a, r, opc, false, rest),
        XmmSrc::Mem(m) => lemma_mem(seq![0x66u8], false, a, m, opc, rest),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_mov_load(sz: Size, dst: u8, mem: Mem, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovLoad { sz, dst, mem }),
    ensures
        extract(encode(Instr::MovLoad { sz, dst, mem }) + rest) == (Instr::MovLoad { sz, dst, mem }),
{
    reveal(extract);
    lemma_mem(Seq::empty(), is64(sz), dst, mem, seq![0x8Bu8], rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_mov_store(sz: Size, mem: Mem, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovStore { sz, mem, src }),
    ensures
        extract(encode(Instr::MovStore { sz, mem, src }) + rest) == (Instr::MovStore {
            sz,
            mem,
            src,
        }),
{
    reveal(extract);
    lemma_mem(Seq::empty(), is64(sz), src, mem, seq![0x89u8], rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_alu_rm(alu: AluOp, sz: Size, dst: u8, mem: Mem, rest: Seq<u8>)
    requires
        valid_instr(Instr::AluRM { alu, sz, dst, mem }),
    ensures
        extract(encode(Instr::AluRM { alu, sz, dst, mem }) + rest) == (Instr::AluRM {
            alu,
            sz,
            dst,
            mem,
        }),
{
    reveal(extract);
    lemma_mem(Seq::empty(), is64(sz), dst, mem, seq![(alu_base(alu) + 3) as u8], rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_movsd_load(dst: u8, mem: Mem, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovsdLoad { dst, mem }),
    ensures
        extract(encode(Instr::MovsdLoad { dst, mem }) + rest) == (Instr::MovsdLoad { dst, mem }),
{
    reveal(extract);
    lemma_mem(seq![0xF2u8], false, dst, mem, seq![0x0Fu8, 0x10u8], rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_movsd_store(mem: Mem, src: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovsdStore { mem, src }),
    ensures
        extract(encode(Instr::MovsdStore { mem, src }) + rest) == (Instr::MovsdStore { mem, src }),
{
    reveal(extract);
    lemma_mem(seq![0xF2u8], false, src, mem, seq![0x0Fu8, 0x11u8], rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_mov_imm32s(dst: u8, imm: i32, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovImm32S { dst, imm }),
    ensures
        extract(encode(Instr::MovImm32S { dst, imm }) + rest) == (Instr::MovImm32S { dst, imm }),
{
    reveal(extract);
    lemma_rr_imm(Seq::empty(), true, 0, dst, seq![0xC7u8], imm, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_alu_ri(alu: AluOp, sz: Size, dst: u8, imm: i32, rest: Seq<u8>)
    requires
        valid_instr(Instr::AluRI { alu, sz, dst, imm }),
    ensures
        extract(encode(Instr::AluRI { alu, sz, dst, imm }) + rest) == (Instr::AluRI {
            alu,
            sz,
            dst,
            imm,
        }),
{
    reveal(extract);
    lemma_rr_imm(Seq::empty(), is64(sz), alu_ext(alu) as u8, dst, seq![0x81u8], imm, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_test_ri(sz: Size, a: u8, imm: i32, rest: Seq<u8>)
    requires
        valid_instr(Instr::TestRI { sz, a, imm }),
    ensures
        extract(encode(Instr::TestRI { sz, a, imm }) + rest) == (Instr::TestRI { sz, a, imm }),
{
    reveal(extract);
    lemma_rr_imm(Seq::empty(), is64(sz), 0, a, seq![0xF7u8], imm, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_imul_rri(sz: Size, dst: u8, src: u8, imm: i32, rest: Seq<u8>)
    requires
        valid_instr(Instr::ImulRRI { sz, dst, src, imm }),
    ensures
        extract(encode(Instr::ImulRRI { sz, dst, src, imm }) + rest) == (Instr::ImulRRI {
            sz,
            dst,
            src,
            imm,
        }),
{
    reveal(extract);
    lemma_rr_imm(Seq::empty(), is64(sz), dst, src, seq![0x69u8], imm, rest);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_shift_imm(shift: ShiftOp, sz: Size, r: u8, count: u8, rest: Seq<u8>)
    requires
        valid_instr(Instr::ShiftImm { shift, sz, r, count }),
    ensures
        extract(encode(Instr::ShiftImm { shift, sz, r, count }) + rest) == (Instr::ShiftImm {
            shift,
            sz,
            r,
            count,
        }),
{
    reveal(extract);
    lemma_rr(
        Seq::empty(),
        is64(sz),
        shift_ext(shift) as u8,
        r,
        seq![0xC1u8],
        false,
        seq![count] + rest,
    );
    assert(seq![count].len() == 1);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_mov_imm32(dst: u8, imm_u32: u32, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovImm32 { dst, imm_u32 }),
    ensures
        extract(encode(Instr::MovImm32 { dst, imm_u32 }) + rest) == (Instr::MovImm32 {
            dst,
            imm_u32,
        }),
{
    reveal(extract);
    let empty = Seq::<u8>::empty();
    let rx = rex_seq(false, false, false, dst >= 8, false);
    let op = (0xB8 + (dst as int) % 8) as u8;
    let body = seq![op] + le_bytes(imm_u32 as int, 4) + rest;
    lemma_head(empty, false, false, false, dst >= 8, false, body);
    let e = encode(Instr::MovImm32 { dst, imm_u32 }) + rest;
    assert(e =~= empty + rx + body);
    let pre = rx + seq![op];
    assert(e =~= pre + le_bytes(imm_u32 as int, 4) + rest);
    lemma_le32(pre, imm_u32 as int, rest);
    lemma_dst_low(dst);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_mov_imm64(dst: u8, imm_u64: u64, rest: Seq<u8>)
    requires
        valid_instr(Instr::MovImm64 { dst, imm_u64 }),
    ensures
        extract(encode(Instr::MovImm64 { dst, imm_u64 }) + rest) == (Instr::MovImm64 {
            dst,
            imm_u64,
        }),
{
    reveal(extract);
    let empty = Seq::<u8>::empty();
    let rx = rex_seq(true, false, false, dst >= 8, false);
    let op = (0xB8 + (dst as int) % 8) as u8;
    let body = seq![op] + le_bytes(imm_u64 as int, 8) + rest;
    lemma_head(empty, true, false, false, dst >= 8, false, body);
    let e = encode(Instr::MovImm64 { dst, imm_u64 }) + rest;
    assert(e =~= empty + rx + body);
    let pre = rx + seq![op];
    assert(e =~= pre + le_bytes(imm_u64 as int, 8) + rest);
    lemma_le64(pre, imm_u64 as int, rest);
    lemma_dst_low(dst);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_jcc(cc: u8, rel: i32, rest: Seq<u8>)
    requires
        valid_instr(Instr::Jcc { cc, rel }),
    ensures
        extract(encode(Instr::Jcc { cc, rel }) + rest) == (Instr::Jcc { cc, rel }),
{
    reveal(extract);
    let empty = Seq::<u8>::empty();
    let body = seq![0x0Fu8, (0x80 + cc as int) as u8] + le_bytes(rel as int, 4) + rest;
    lemma_head(empty, false, false, false, false, false, body);
    let e = encode(Instr::Jcc { cc, rel }) + rest;
    assert(e =~= empty + rex_seq(false, false, false, false, false) + body);
    let pre = seq![0x0Fu8, (0x80 + cc as int) as u8];
    assert(e =~= pre + le_bytes(rel as int, 4) + rest);
    lemma_le32(pre, rel as int, rest);
    lemma_sx32(rel as int);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_jmp(rel: i32, rest: Seq<u8>)
    requires
        valid_instr(Instr::Jmp { rel }),
    ensures
        extract(encode(Instr::Jmp { rel }) + rest) == (Instr::Jmp { rel }),
{
    reveal(extract);
    let empty = Seq::<u8>::empty();
    let body = seq![0xE9u8] + le_bytes(rel as int, 4) + rest;
    lemma_head(empty, false, false, false, false, false, body);
    let e = encode(Instr::Jmp { rel }) + rest;
    assert(e =~= empty + rex_seq(false, false, false, false, false) + body);
    let pre = seq![0xE9u8];
    assert(e =~= pre + le_bytes(rel as int, 4) + rest);
    lemma_le32(pre, rel as int, rest);
    lemma_sx32(rel as int);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn c_ret(rest: Seq<u8>)
    ensures
        extract(encode(Instr::Ret) + rest) == Instr::Ret,
{
    reveal(extract);
    let empty = Seq::<u8>::empty();
    let body = seq![0xC3u8] + rest;
    lemma_head(empty, false, false, false, false, false, body);
    assert(encode(Instr::Ret) + rest =~= empty + rex_seq(false, false, false, false, false) + body);
}

/// Completeness of [`extract`]: for every instruction of the subset, the
/// fields read back from its canonical encoding, followed by any bytes, are
/// the instruction.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_extract_complete(i: Instr, rest: Seq<u8>)
    requires
        valid_instr(i),
    ensures
        extract(encode(i) + rest) == i,
{
    match i {
        Instr::MovRR { sz, dst, src } => c_mov_rr(sz, dst, src, rest),
        Instr::MovLoad { sz, dst, mem } => c_mov_load(sz, dst, mem, rest),
        Instr::MovStore { sz, mem, src } => c_mov_store(sz, mem, src, rest),
        Instr::MovImm32 { dst, imm_u32 } => c_mov_imm32(dst, imm_u32, rest),
        Instr::MovImm32S { dst, imm } => c_mov_imm32s(dst, imm, rest),
        Instr::MovImm64 { dst, imm_u64 } => c_mov_imm64(dst, imm_u64, rest),
        Instr::AluRR { alu, sz, dst, src } => c_alu_rr(alu, sz, dst, src, rest),
        Instr::AluRM { alu, sz, dst, mem } => c_alu_rm(alu, sz, dst, mem, rest),
        Instr::AluRI { alu, sz, dst, imm } => c_alu_ri(alu, sz, dst, imm, rest),
        Instr::TestRR { sz, a, b } => c_test_rr(sz, a, b, rest),
        Instr::TestRI { sz, a, imm } => c_test_ri(sz, a, imm, rest),
        Instr::Neg { sz, r } => c_neg(sz, r, rest),
        Instr::Not { sz, r } => c_not(sz, r, rest),
        Instr::ShiftImm { shift, sz, r, count } => c_shift_imm(shift, sz, r, count, rest),
        Instr::ShiftCl { shift, sz, r } => c_shift_cl(shift, sz, r, rest),
        Instr::ImulRR { sz, dst, src } => c_imul_rr(sz, dst, src, rest),
        Instr::ImulRRI { sz, dst, src, imm } => c_imul_rri(sz, dst, src, imm, rest),
        Instr::Jcc { cc, rel } => c_jcc(cc, rel, rest),
        Instr::Jmp { rel } => c_jmp(rel, rest),
        Instr::Ret => c_ret(rest),
        Instr::Cmovcc { cc, sz, dst, src } => c_cmovcc(cc, sz, dst, src, rest),
        Instr::Setcc { cc, dst } => c_setcc(cc, dst, rest),
        Instr::FpArith { fop, dst, xsrc } => c_fp_arith(fop, dst, xsrc, rest),
        Instr::Sqrtsd { dst, xsrc } => c_sqrtsd(dst, xsrc, rest),
        Instr::Ucomisd { a, xsrc } => c_ucomisd(a, xsrc, rest),
        Instr::Cvtsi2sd { sz, dst, src } => c_cvtsi2sd(sz, dst, src, rest),
        Instr::Cvttsd2si { sz, dst, src } => c_cvttsd2si(sz, dst, src, rest),
        Instr::Cvtsd2si { sz, dst, src } => c_cvtsd2si(sz, dst, src, rest),
        Instr::MovqToXmm { dst, src } => c_movq_to_xmm(dst, src, rest),
        Instr::MovqFromXmm { dst, src } => c_movq_from_xmm(dst, src, rest),
        Instr::MovsdLoad { dst, mem } => c_movsd_load(dst, mem, rest),
        Instr::MovsdStore { mem, src } => c_movsd_store(mem, src, rest),
    }
}

/// If `bytes` begin with the canonical encoding of `i`, `extract` reads `i`.
pub proof fn lemma_extract_starts(bytes: Seq<u8>, i: Instr)
    requires
        starts_with_encoding(bytes, i),
    ensures
        extract(bytes) == i,
{
    let n = encode(i).len() as int;
    let rest = bytes.subrange(n, bytes.len() as int);
    assert(bytes =~= encode(i) + rest);
    lemma_extract_complete(i, rest);
}

/// **Completeness of the decoder** (the `None` half of
/// [`crate::contract::decode_ensures`]): if some instruction's canonical
/// encoding begins `bytes`, [`dec`] finds it.
pub proof fn lemma_dec_complete(bytes: Seq<u8>, i: Instr)
    requires
        starts_with_encoding(bytes, i),
    ensures
        dec(bytes) == Some(i),
{
    lemma_extract_starts(bytes, i);
}

/// **The canonical encoding is a prefix code** (CLAUDE.md rule 7: proven,
/// not assumed): two instructions whose encodings both begin the same bytes
/// are equal, because the decoder reads both back from those bytes.
pub proof fn lemma_canonical_prefix_free()
    ensures
        crate::contract::canonical_prefix_free(),
{
    assert forall|i: Instr, j: Instr, bytes: Seq<u8>|
        starts_with_encoding(bytes, i) && starts_with_encoding(bytes, j) implies i == j by {
        lemma_extract_starts(bytes, i);
        lemma_extract_starts(bytes, j);
    }
}

/// A signed 32-bit number read back from its four bytes.
pub proof fn lemma_sx32(v: int)
    requires
        -0x8000_0000 <= v < 0x8000_0000,
    ensures
        sx32(v % 0x1_0000_0000) == v,
{
}

} // verus!
