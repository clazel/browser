//! What `add`, `cmp`, `jcc`, `cmovcc` and the moves of the bounds-check
//! sequence do to the registers and flags, exactly, in `clazel_x64::spec::step`.
//! The carry flag after `add t, n` says whether `t + n` wrapped; after
//! `cmp t, [bound]` the carry and zero flags say how `t` and the bound compare.

#[allow(unused_imports)]
use super::safety_flags::*;
#[allow(unused_imports)]
use super::safety_sem::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `bit` is 0 or 1.
proof fn lemma_bit_01(x: int, k: nat)
    ensures
        0 <= bit(x, k) <= 1,
{
}

/// `write_user_rflags` with no undefined flags writes the vector's six flag
/// bits.
pub proof fn lemma_wur_bit(u: spec_fn(nat) -> nat, s: State, vec: u32, k: nat)
    requires
        flag_pos(k),
    ensures
        flgi(write_user_rflags(u, s, vec, 0), k) == bit(vec as int, k),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(bit(0, 0) == 0 && bit(0, 2) == 0 && bit(0, 4) == 0 && bit(0, 6) == 0 && bit(0, 7) == 0
        && bit(0, 11) == 0);
    let s1 = write_flag_or_undefined(u, s, cf_bit(), vec, 0);
    let s2 = write_flag_or_undefined(u, s1, pf_bit(), vec, 0);
    let s3 = write_flag_or_undefined(u, s2, af_bit(), vec, 0);
    let s4 = write_flag_or_undefined(u, s3, zf_bit(), vec, 0);
    let s5 = write_flag_or_undefined(u, s4, sf_bit(), vec, 0);
    let s6 = write_flag_or_undefined(u, s5, of_bit(), vec, 0);
    assert(s6 == write_user_rflags(u, s, vec, 0));
    lemma_bit_set32(s.rflags, 0, bit(vec as int, 0), k);
    lemma_bit_set32(s1.rflags, 2, bit(vec as int, 2), k);
    lemma_bit_set32(s2.rflags, 4, bit(vec as int, 4), k);
    lemma_bit_set32(s3.rflags, 6, bit(vec as int, 6), k);
    lemma_bit_set32(s4.rflags, 7, bit(vec as int, 7), k);
    lemma_bit_set32(s5.rflags, 11, bit(vec as int, 11), k);
    lemma_bit_01(vec as int, k);
}

/// `change_rflags` with every flag given sets the carry and zero bits to the
/// given values (mod 2).
pub proof fn lemma_change_cf_zf(w: u32, f: FlagUpd)
    requires
        f.cf is Some,
        f.pf is Some,
        f.af is Some,
        f.zf is Some,
        f.sf is Some,
        f.of is Some,
    ensures
        bit(change_rflags(w, f) as int, 0) == f.cf->Some_0 % 2,
        bit(change_rflags(w, f) as int, 6) == f.zf->Some_0 % 2,
{
    let w1 = opt_set_bit(w, cf_bit(), f.cf);
    let w2 = opt_set_bit(w1, pf_bit(), f.pf);
    let w3 = opt_set_bit(w2, af_bit(), f.af);
    let w4 = opt_set_bit(w3, zf_bit(), f.zf);
    let w5 = opt_set_bit(w4, sf_bit(), f.sf);
    let w6 = opt_set_bit(w5, of_bit(), f.of);
    assert(w6 == change_rflags(w, f));
    lemma_bit_set32(w, 0, f.cf->Some_0, 0);
    lemma_bit_set32(w1, 2, f.pf->Some_0, 0);
    lemma_bit_set32(w2, 4, f.af->Some_0, 0);
    lemma_bit_set32(w3, 6, f.zf->Some_0, 0);
    lemma_bit_set32(w4, 7, f.sf->Some_0, 0);
    lemma_bit_set32(w5, 11, f.of->Some_0, 0);
    lemma_bit_set32(w, 0, f.cf->Some_0, 6);
    lemma_bit_set32(w1, 2, f.pf->Some_0, 6);
    lemma_bit_set32(w2, 4, f.af->Some_0, 6);
    lemma_bit_set32(w3, 6, f.zf->Some_0, 6);
    lemma_bit_set32(w4, 7, f.sf->Some_0, 6);
    lemma_bit_set32(w5, 11, f.of->Some_0, 6);
}

/// A value below 2^64 is its own low 64 bits.
proof fn lemma_loghead_id(x: int)
    requires
        0 <= x < 0x1_0000_0000_0000_0000,
    ensures
        loghead(64, x) == x,
{
    lemma_p2_vals();
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, 0x1_0000_0000_0000_0000nat);
}

/// The 64-bit `add`: the result, and the carry flag it writes.
proof fn lemma_add_spec(dst: int, src: int, w: u32)
    requires
        0 <= dst < 0x1_0000_0000_0000_0000,
        0 <= src < 0x1_0000_0000_0000_0000,
    ensures
        gpr_add_spec(64, dst, src, w).undef == 0,
        gpr_add_spec(64, dst, src, w).result == (dst + src) % 0x1_0000_0000_0000_0000,
        bit(gpr_add_spec(64, dst, src, w).rflags as int, 0) == if dst + src
            >= 0x1_0000_0000_0000_0000 {
            1int
        } else {
            0int
        },
{
    lemma_p2_vals();
    assert(loghead(64, dst) == dst && loghead(64, src) == src);
    let raw = dst + src;
    let result = loghead(64, raw);
    let f = FlagUpd {
        cf: Some(cf_spec(64, raw)),
        pf: Some(pf_spec(result)),
        af: Some(add_af_spec(dst, src)),
        zf: Some(zf_spec(result)),
        sf: Some(sf_spec(64, result)),
        of: Some(of_spec(64, logext(64, dst) + logext(64, src))),
    };
    assert(gpr_add_spec(64, dst, src, w).rflags == change_rflags(w, f));
    lemma_change_cf_zf(w, f);
    assert(cf_spec(64, raw) == if raw >= 0x1_0000_0000_0000_0000 {
        1int
    } else {
        0int
    });
}

/// **`add t, n` (64-bit)**: `t` becomes `t + n` modulo 2^64, and the carry flag
/// says whether the sum reached 2^64.
#[verifier::rlimit(2000)]
#[verifier::spinoff_prover]
pub proof fn lemma_step_add(u: spec_fn(nat) -> nat, s: State, s2: State, t: u8, n: i32)
    requires
        s.rgf.len() == 16,
        t < 16,
        0 < n,
        step(u, s, Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst: t, imm: n }) == Some(s2),
    ensures
        gpr_kept(s, s2, Some(t)),
        s2.rgf[t as int] as int == (s.rgf[t as int] as int + n) % 0x1_0000_0000_0000_0000,
        flgi(s2, cf_bit()) == if s.rgf[t as int] as int + n >= 0x1_0000_0000_0000_0000 {
            1int
        } else {
            0int
        },
        s2.mem == s.mem,
{
    let i = Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst: t, imm: n };
    lemma_p2_vals();
    assert(valid_instr(i));
    lemma_step_frame(u, s, i, s2);
    let r = gpr_arith_logic_spec(
        nbits(Size::W64),
        AluOp::Add,
        rgfi_size(s, Size::W64, t),
        loghead(nbits(Size::W64), n as int),
        s.rflags,
    );
    let s1 = set_rgfi_size(s, Size::W64, t, r.result);
    assert(nbits(Size::W64) == 64);
    assert(r.undef == 0);
    let sw = write_user_rflags(u, s1, r.rflags, r.undef);
    assert(effect(u, s, i) == Some(sw));
    lemma_wur(u, s1, r.rflags, r.undef);
    lemma_wur_bit(u, s1, r.rflags, 0);
    let tv = s.rgf[t as int] as int;
    lemma_loghead_id(tv);
    lemma_loghead_id(n as int);
    lemma_add_spec(tv, n as int, s.rflags);
    assert(r == gpr_add_spec(64, tv, n as int, s.rflags));
    assert(s2.rflags == sw.rflags);
    assert(s2.rgf[t as int] == sw.rgf[t as int]);
    lemma_set_rgfi(s, Size::W64, t, r.result);
}

/// **`cmp t, [mem]` (64-bit)** where the memory holds `b`, `0 <= b < 2^64`:
/// no register changes, the carry flag says `t < b` and the zero flag
/// `t == b` (unsigned).
#[verifier::rlimit(2000)]
#[verifier::spinoff_prover]
pub proof fn lemma_step_cmp(
    u: spec_fn(nat) -> nat,
    s: State,
    s2: State,
    t: u8,
    mem: Mem,
    b: int,
)
    requires
        s.rgf.len() == 16,
        t < 16,
        mem_ok(mem),
        read_operand_mem(s, Size::W64, mem) == Some(b),
        0 <= b < 0x1_0000_0000_0000_0000,
        step(u, s, Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: t, mem: mem }) == Some(s2),
    ensures
        s2.rgf == s.rgf,
        s2.mem == s.mem,
        flgi(s2, cf_bit()) == if (s.rgf[t as int] as int) < b {
            1int
        } else {
            0int
        },
        flgi(s2, zf_bit()) == if s.rgf[t as int] as int == b {
            1int
        } else {
            0int
        },
{
    let i = Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: t, mem: mem };
    lemma_p2_vals();
    assert(valid_instr(i));
    lemma_step_frame(u, s, i, s2);
    let tv = s.rgf[t as int] as int;
    let r = gpr_arith_logic_spec(nbits(Size::W64), AluOp::Cmp, rgfi_size(s, Size::W64, t), b, s.rflags);
    assert(nbits(Size::W64) == 64);
    assert(r.undef == 0);
    let sw = write_user_rflags(u, s, r.rflags, r.undef);
    assert(effect(u, s, i) == Some(sw));
    lemma_wur(u, s, r.rflags, r.undef);
    lemma_wur_bit(u, sw, r.rflags, 0);
    lemma_wur_bit(u, s, r.rflags, 0);
    lemma_wur_bit(u, s, r.rflags, 6);
    let lt = logext(64, tv);
    let lb = logext(64, b);
    let res = loghead(64, lt - lb);
    assert(r.result == res);
    assert(res == 0 <==> tv == b) by {
        assert(lt == tv || lt == tv - 0x1_0000_0000_0000_0000);
        assert(lb == b || lb == b - 0x1_0000_0000_0000_0000);
    }
    lemma_change_cf_zf(
        s.rflags,
        FlagUpd {
            cf: Some(bool_to_bit(tv < b)),
            pf: Some(pf_spec(res)),
            af: Some(sub_af_spec(tv, b)),
            zf: Some(zf_spec(res)),
            sf: Some(sf_spec(64, res)),
            of: Some(of_spec(64, lt - lb)),
        },
    );
    assert(s2.rflags == sw.rflags);
    assert(s2.rgf == s.rgf);
}

} // verus!
