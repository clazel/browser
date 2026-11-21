//! The status flags: what `cmp`, `test` and `setcc` do with them, and that
//! the condition code a comparison template uses holds exactly when LIR's
//! comparison does.
//!
//! The machine keeps the flags as bits of a 32-bit word (`rflags`), changed
//! one flag at a time by `set_bit32`. The six flags the subset writes are at
//! bit positions 0 (`cf`), 2 (`pf`), 4 (`af`), 6 (`zf`), 7 (`sf`) and 11
//! (`of`). The first lemmas say that changing one flag's bit changes no other
//! of the six; the rest compute the flags `cmp` and `test` leave.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `k` is the bit position of one of the six flags the subset writes.
pub open spec fn flagpos(k: nat) -> bool {
    k == 0 || k == 2 || k == 4 || k == 6 || k == 7 || k == 11
}

/// Setting the flag at bit 0: the new value there, the other five unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_sb_0(w: u32, v: int)
    ensures
        x64::bit(x64::set_bit32(w, 0, v) as int, 0) == v % 2,
        x64::bit(x64::set_bit32(w, 0, v) as int, 2) == x64::bit(w as int, 2),
        x64::bit(x64::set_bit32(w, 0, v) as int, 4) == x64::bit(w as int, 4),
        x64::bit(x64::set_bit32(w, 0, v) as int, 6) == x64::bit(w as int, 6),
        x64::bit(x64::set_bit32(w, 0, v) as int, 7) == x64::bit(w as int, 7),
        x64::bit(x64::set_bit32(w, 0, v) as int, 11) == x64::bit(w as int, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let c = v % 2;
    assert(0 <= c < 2);
    assert(x64::p2(0) == 1);
    assert(x64::p2(2) == 4);
    assert(x64::p2(4) == 16);
    assert(x64::p2(6) == 64);
    assert(x64::p2(7) == 128);
    assert(x64::p2(11) == 2048);
    let q = (w as int) / 2;
    let r = (w as int) % 1;
    let b = x64::bit(w as int, 0);
    assert(b == ((w as int) / 1) % 2);
    assert(0 <= r < 1 && 0 <= b < 2);
    assert((w as int) == 2 * q + b * 1 + r);
    let n = (w as int) - b * 1 + c * 1;
    assert(n == 2 * q + c * 1 + r);
    assert(0 <= n < 0x1_0000_0000);
    assert(x64::set_bit32(w, 0, v) as int == n);
    assert(x64::bit(n, 0) == c);
    assert(x64::bit(n, 2) == x64::bit(w as int, 2));
    assert(x64::bit(n, 4) == x64::bit(w as int, 4));
    assert(x64::bit(n, 6) == x64::bit(w as int, 6));
    assert(x64::bit(n, 7) == x64::bit(w as int, 7));
    assert(x64::bit(n, 11) == x64::bit(w as int, 11));
}

/// Setting the flag at bit 2: the new value there, the other five unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_sb_2(w: u32, v: int)
    ensures
        x64::bit(x64::set_bit32(w, 2, v) as int, 0) == x64::bit(w as int, 0),
        x64::bit(x64::set_bit32(w, 2, v) as int, 2) == v % 2,
        x64::bit(x64::set_bit32(w, 2, v) as int, 4) == x64::bit(w as int, 4),
        x64::bit(x64::set_bit32(w, 2, v) as int, 6) == x64::bit(w as int, 6),
        x64::bit(x64::set_bit32(w, 2, v) as int, 7) == x64::bit(w as int, 7),
        x64::bit(x64::set_bit32(w, 2, v) as int, 11) == x64::bit(w as int, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let c = v % 2;
    assert(0 <= c < 2);
    assert(x64::p2(0) == 1);
    assert(x64::p2(2) == 4);
    assert(x64::p2(4) == 16);
    assert(x64::p2(6) == 64);
    assert(x64::p2(7) == 128);
    assert(x64::p2(11) == 2048);
    let q = (w as int) / 8;
    let r = (w as int) % 4;
    let b = x64::bit(w as int, 2);
    assert(b == ((w as int) / 4) % 2);
    assert(0 <= r < 4 && 0 <= b < 2);
    assert((w as int) == 8 * q + b * 4 + r);
    let n = (w as int) - b * 4 + c * 4;
    assert(n == 8 * q + c * 4 + r);
    assert(0 <= n < 0x1_0000_0000);
    assert(x64::set_bit32(w, 2, v) as int == n);
    assert(x64::bit(n, 0) == x64::bit(w as int, 0));
    assert(x64::bit(n, 2) == c);
    assert(x64::bit(n, 4) == x64::bit(w as int, 4));
    assert(x64::bit(n, 6) == x64::bit(w as int, 6));
    assert(x64::bit(n, 7) == x64::bit(w as int, 7));
    assert(x64::bit(n, 11) == x64::bit(w as int, 11));
}

/// Setting the flag at bit 4: the new value there, the other five unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_sb_4(w: u32, v: int)
    ensures
        x64::bit(x64::set_bit32(w, 4, v) as int, 0) == x64::bit(w as int, 0),
        x64::bit(x64::set_bit32(w, 4, v) as int, 2) == x64::bit(w as int, 2),
        x64::bit(x64::set_bit32(w, 4, v) as int, 4) == v % 2,
        x64::bit(x64::set_bit32(w, 4, v) as int, 6) == x64::bit(w as int, 6),
        x64::bit(x64::set_bit32(w, 4, v) as int, 7) == x64::bit(w as int, 7),
        x64::bit(x64::set_bit32(w, 4, v) as int, 11) == x64::bit(w as int, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let c = v % 2;
    assert(0 <= c < 2);
    assert(x64::p2(0) == 1);
    assert(x64::p2(2) == 4);
    assert(x64::p2(4) == 16);
    assert(x64::p2(6) == 64);
    assert(x64::p2(7) == 128);
    assert(x64::p2(11) == 2048);
    let q = (w as int) / 32;
    let r = (w as int) % 16;
    let b = x64::bit(w as int, 4);
    assert(b == ((w as int) / 16) % 2);
    assert(0 <= r < 16 && 0 <= b < 2);
    assert((w as int) == 32 * q + b * 16 + r);
    let n = (w as int) - b * 16 + c * 16;
    assert(n == 32 * q + c * 16 + r);
    assert(0 <= n < 0x1_0000_0000);
    assert(x64::set_bit32(w, 4, v) as int == n);
    assert(x64::bit(n, 0) == x64::bit(w as int, 0));
    assert(x64::bit(n, 2) == x64::bit(w as int, 2));
    assert(x64::bit(n, 4) == c);
    assert(x64::bit(n, 6) == x64::bit(w as int, 6));
    assert(x64::bit(n, 7) == x64::bit(w as int, 7));
    assert(x64::bit(n, 11) == x64::bit(w as int, 11));
}

/// Setting the flag at bit 6: the new value there, the other five unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_sb_6(w: u32, v: int)
    ensures
        x64::bit(x64::set_bit32(w, 6, v) as int, 0) == x64::bit(w as int, 0),
        x64::bit(x64::set_bit32(w, 6, v) as int, 2) == x64::bit(w as int, 2),
        x64::bit(x64::set_bit32(w, 6, v) as int, 4) == x64::bit(w as int, 4),
        x64::bit(x64::set_bit32(w, 6, v) as int, 6) == v % 2,
        x64::bit(x64::set_bit32(w, 6, v) as int, 7) == x64::bit(w as int, 7),
        x64::bit(x64::set_bit32(w, 6, v) as int, 11) == x64::bit(w as int, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let c = v % 2;
    assert(0 <= c < 2);
    assert(x64::p2(0) == 1);
    assert(x64::p2(2) == 4);
    assert(x64::p2(4) == 16);
    assert(x64::p2(6) == 64);
    assert(x64::p2(7) == 128);
    assert(x64::p2(11) == 2048);
    let q = (w as int) / 128;
    let r = (w as int) % 64;
    let b = x64::bit(w as int, 6);
    assert(b == ((w as int) / 64) % 2);
    assert(0 <= r < 64 && 0 <= b < 2);
    assert((w as int) == 128 * q + b * 64 + r);
    let n = (w as int) - b * 64 + c * 64;
    assert(n == 128 * q + c * 64 + r);
    assert(0 <= n < 0x1_0000_0000);
    assert(x64::set_bit32(w, 6, v) as int == n);
    assert(x64::bit(n, 0) == x64::bit(w as int, 0));
    assert(x64::bit(n, 2) == x64::bit(w as int, 2));
    assert(x64::bit(n, 4) == x64::bit(w as int, 4));
    assert(x64::bit(n, 6) == c);
    assert(x64::bit(n, 7) == x64::bit(w as int, 7));
    assert(x64::bit(n, 11) == x64::bit(w as int, 11));
}

/// Setting the flag at bit 7: the new value there, the other five unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_sb_7(w: u32, v: int)
    ensures
        x64::bit(x64::set_bit32(w, 7, v) as int, 0) == x64::bit(w as int, 0),
        x64::bit(x64::set_bit32(w, 7, v) as int, 2) == x64::bit(w as int, 2),
        x64::bit(x64::set_bit32(w, 7, v) as int, 4) == x64::bit(w as int, 4),
        x64::bit(x64::set_bit32(w, 7, v) as int, 6) == x64::bit(w as int, 6),
        x64::bit(x64::set_bit32(w, 7, v) as int, 7) == v % 2,
        x64::bit(x64::set_bit32(w, 7, v) as int, 11) == x64::bit(w as int, 11),
{
    vstd::arithmetic::power2::lemma2_to64();
    let c = v % 2;
    assert(0 <= c < 2);
    assert(x64::p2(0) == 1);
    assert(x64::p2(2) == 4);
    assert(x64::p2(4) == 16);
    assert(x64::p2(6) == 64);
    assert(x64::p2(7) == 128);
    assert(x64::p2(11) == 2048);
    let q = (w as int) / 256;
    let r = (w as int) % 128;
    let b = x64::bit(w as int, 7);
    assert(b == ((w as int) / 128) % 2);
    assert(0 <= r < 128 && 0 <= b < 2);
    assert((w as int) == 256 * q + b * 128 + r);
    let n = (w as int) - b * 128 + c * 128;
    assert(n == 256 * q + c * 128 + r);
    assert(0 <= n < 0x1_0000_0000);
    assert(x64::set_bit32(w, 7, v) as int == n);
    assert(x64::bit(n, 0) == x64::bit(w as int, 0));
    assert(x64::bit(n, 2) == x64::bit(w as int, 2));
    assert(x64::bit(n, 4) == x64::bit(w as int, 4));
    assert(x64::bit(n, 6) == x64::bit(w as int, 6));
    assert(x64::bit(n, 7) == c);
    assert(x64::bit(n, 11) == x64::bit(w as int, 11));
}

/// Setting the flag at bit 11: the new value there, the other five unchanged.
#[verifier::rlimit(2000)]
pub proof fn lemma_sb_11(w: u32, v: int)
    ensures
        x64::bit(x64::set_bit32(w, 11, v) as int, 0) == x64::bit(w as int, 0),
        x64::bit(x64::set_bit32(w, 11, v) as int, 2) == x64::bit(w as int, 2),
        x64::bit(x64::set_bit32(w, 11, v) as int, 4) == x64::bit(w as int, 4),
        x64::bit(x64::set_bit32(w, 11, v) as int, 6) == x64::bit(w as int, 6),
        x64::bit(x64::set_bit32(w, 11, v) as int, 7) == x64::bit(w as int, 7),
        x64::bit(x64::set_bit32(w, 11, v) as int, 11) == v % 2,
{
    vstd::arithmetic::power2::lemma2_to64();
    let c = v % 2;
    assert(0 <= c < 2);
    assert(x64::p2(0) == 1);
    assert(x64::p2(2) == 4);
    assert(x64::p2(4) == 16);
    assert(x64::p2(6) == 64);
    assert(x64::p2(7) == 128);
    assert(x64::p2(11) == 2048);
    let q = (w as int) / 4096;
    let r = (w as int) % 2048;
    let b = x64::bit(w as int, 11);
    assert(b == ((w as int) / 2048) % 2);
    assert(0 <= r < 2048 && 0 <= b < 2);
    assert((w as int) == 4096 * q + b * 2048 + r);
    let n = (w as int) - b * 2048 + c * 2048;
    assert(n == 4096 * q + c * 2048 + r);
    assert(0 <= n < 0x1_0000_0000);
    assert(x64::set_bit32(w, 11, v) as int == n);
    assert(x64::bit(n, 0) == x64::bit(w as int, 0));
    assert(x64::bit(n, 2) == x64::bit(w as int, 2));
    assert(x64::bit(n, 4) == x64::bit(w as int, 4));
    assert(x64::bit(n, 6) == x64::bit(w as int, 6));
    assert(x64::bit(n, 7) == x64::bit(w as int, 7));
    assert(x64::bit(n, 11) == c);
}

/// Setting the flag at `k` sets that bit and no other of the six.
pub proof fn lemma_set_bit32_bit(w: u32, k: nat, v: int, j: nat)
    requires
        flagpos(k),
        flagpos(j),
    ensures
        x64::bit(x64::set_bit32(w, k, v) as int, j) == if j == k {
            v % 2
        } else {
            x64::bit(w as int, j)
        },
{
    lemma_sb_0(w, v);
    lemma_sb_2(w, v);
    lemma_sb_4(w, v);
    lemma_sb_6(w, v);
    lemma_sb_7(w, v);
    lemma_sb_11(w, v);
}

// ----------------------------------------------------------------------------
// Reading the flags back out of `change_rflags` and `write_user_rflags`
// ----------------------------------------------------------------------------

/// What bit `j` of the flags is after the update `f`, when it was `old`:
/// the new value of the flag at `j` if `f` names one, else `old`.
pub open spec fn upd_bit(f: x64::FlagUpd, j: nat, old: int) -> int {
    if j == 0 {
        match f.cf {
            Some(x) => x % 2,
            None => old,
        }
    } else if j == 2 {
        match f.pf {
            Some(x) => x % 2,
            None => old,
        }
    } else if j == 4 {
        match f.af {
            Some(x) => x % 2,
            None => old,
        }
    } else if j == 6 {
        match f.zf {
            Some(x) => x % 2,
            None => old,
        }
    } else if j == 7 {
        match f.sf {
            Some(x) => x % 2,
            None => old,
        }
    } else if j == 11 {
        match f.of {
            Some(x) => x % 2,
            None => old,
        }
    } else {
        old
    }
}

/// One optional flag update changes only its own bit.
pub proof fn lemma_opt_set_bit_bit(w: u32, k: nat, v: Option<int>, j: nat)
    requires
        flagpos(k),
        flagpos(j),
    ensures
        x64::bit(x64::opt_set_bit(w, k, v) as int, j) == match v {
            Some(x) => if j == k {
                x % 2
            } else {
                x64::bit(w as int, j)
            },
            None => x64::bit(w as int, j),
        },
{
    match v {
        Some(x) => {
            lemma_set_bit32_bit(w, k, x, j);
        },
        None => {},
    }
}

/// `change_rflags` sets exactly the flags the update names.
pub proof fn lemma_change_rflags_bit(inp: u32, f: x64::FlagUpd, j: nat)
    requires
        flagpos(j),
    ensures
        x64::bit(x64::change_rflags(inp, f) as int, j) == upd_bit(f, j, x64::bit(inp as int, j)),
{
    let w1 = x64::opt_set_bit(inp, x64::cf_bit(), f.cf);
    let w2 = x64::opt_set_bit(w1, x64::pf_bit(), f.pf);
    let w3 = x64::opt_set_bit(w2, x64::af_bit(), f.af);
    let w4 = x64::opt_set_bit(w3, x64::zf_bit(), f.zf);
    let w5 = x64::opt_set_bit(w4, x64::sf_bit(), f.sf);
    lemma_opt_set_bit_bit(inp, 0, f.cf, j);
    lemma_opt_set_bit_bit(w1, 2, f.pf, j);
    lemma_opt_set_bit_bit(w2, 4, f.af, j);
    lemma_opt_set_bit_bit(w3, 6, f.zf, j);
    lemma_opt_set_bit_bit(w4, 7, f.sf, j);
    lemma_opt_set_bit_bit(w5, 11, f.of, j);
}

/// One step of `write_user_rflags` changes only its own flag.
pub proof fn lemma_wfou_flag(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    k: nat,
    vec: u32,
    mask: u32,
    j: nat,
)
    requires
        flagpos(k),
        flagpos(j),
    ensures
        x64::flgi(x64::write_flag_or_undefined(cu, s, k, vec, mask), j) == if j == k {
            if x64::bit(mask as int, k) == 1 {
                (cu(s.undef) % 2) as int
            } else {
                x64::bit(vec as int, k)
            }
        } else {
            x64::flgi(s, j)
        },
{
    if x64::bit(mask as int, k) == 1 {
        lemma_set_bit32_bit(s.rflags, k, (cu(s.undef) % 2) as int, j);
    } else {
        lemma_set_bit32_bit(s.rflags, k, x64::bit(vec as int, k), j);
    }
}

/// A flag whose bit is clear in the undefined mask is set from the vector by
/// `write_user_rflags`.
pub proof fn lemma_wur_flag(cu: spec_fn(nat) -> nat, s: x64::State, vec: u32, mask: u32, j: nat)
    requires
        flagpos(j),
        x64::bit(mask as int, j) == 0,
    ensures
        x64::flgi(x64::write_user_rflags(cu, s, vec, mask), j) == x64::bit(vec as int, j),
{
    let s1 = x64::write_flag_or_undefined(cu, s, x64::cf_bit(), vec, mask);
    let s2 = x64::write_flag_or_undefined(cu, s1, x64::pf_bit(), vec, mask);
    let s3 = x64::write_flag_or_undefined(cu, s2, x64::af_bit(), vec, mask);
    let s4 = x64::write_flag_or_undefined(cu, s3, x64::zf_bit(), vec, mask);
    let s5 = x64::write_flag_or_undefined(cu, s4, x64::sf_bit(), vec, mask);
    lemma_wfou_flag(cu, s, 0, vec, mask, j);
    lemma_wfou_flag(cu, s1, 2, vec, mask, j);
    lemma_wfou_flag(cu, s2, 4, vec, mask, j);
    lemma_wfou_flag(cu, s3, 6, vec, mask, j);
    lemma_wfou_flag(cu, s4, 7, vec, mask, j);
    lemma_wfou_flag(cu, s5, 11, vec, mask, j);
}

// ----------------------------------------------------------------------------
// `cmp` and `test`
// ----------------------------------------------------------------------------

/// `cmp a, b` leaves the registers and memory alone and sets the flags of
/// `a - b`: `cf` is "a is below b" (unsigned), `zf` is "the difference is
/// 0", `sf` its top bit, `of` "the signed difference does not fit".
pub proof fn lemma_step_cmp(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    sz: x64::Size,
    a: u8,
    b: u8,
)
    requires
        x64::wf(m),
        a < 16,
        b < 16,
        x64::canonical(
            m.rip + x64::instr_len(
                x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: sz, dst: a, src: b },
            ),
        ),
    ensures
        x64::step(
            cu,
            m,
            x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: sz, dst: a, src: b },
        ) is Some,
        ({
            let m1 = x64::step(
                cu,
                m,
                x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: sz, dst: a, src: b },
            ).unwrap();
            let n = x64::nbits(sz);
            let lx = x64::loghead(n, x64::rgfi_size(m, sz, a));
            let ly = x64::loghead(n, x64::rgfi_size(m, sz, b));
            let sraw = x64::logext(n, lx) - x64::logext(n, ly);
            let res = x64::loghead(n, sraw);
            &&& m1.rgf == m.rgf && m1.mem == m.mem && m1.xmm == m.xmm && m1.rip == m.rip
                + x64::instr_len(x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: sz, dst: a, src: b })
            &&& x64::flgi(m1, x64::cf_bit()) == x64::bool_to_bit(lx < ly)
            &&& x64::flgi(m1, x64::zf_bit()) == x64::zf_spec(res)
            &&& x64::flgi(m1, x64::sf_bit()) == x64::sf_spec(n, res) % 2
            &&& x64::flgi(m1, x64::of_bit()) == x64::of_spec(n, sraw)
        }),
{
    let n = x64::nbits(sz);
    let x = x64::rgfi_size(m, sz, a);
    let y = x64::rgfi_size(m, sz, b);
    let r = x64::gpr_sub_spec(n, x, y, m.rflags);
    assert(x64::gpr_arith_logic_spec(n, x64::AluOp::Cmp, x, y, m.rflags) == r);
    super::alu::lemma_wur_frame(cu, m, r.rflags, r.undef);
    assert(r.undef == 0);
    assert(x64::bit(0, 0) == 0 && x64::bit(0, 6) == 0 && x64::bit(0, 7) == 0 && x64::bit(0, 11)
        == 0) by {
        vstd::arithmetic::power2::lemma2_to64();
        assert(x64::p2(0) == 1 && x64::p2(6) == 64 && x64::p2(7) == 128 && x64::p2(11) == 2048);
    }
    lemma_wur_flag(cu, m, r.rflags, r.undef, 0);
    lemma_wur_flag(cu, m, r.rflags, r.undef, 6);
    lemma_wur_flag(cu, m, r.rflags, r.undef, 7);
    lemma_wur_flag(cu, m, r.rflags, r.undef, 11);
    let lx = x64::loghead(n, x);
    let ly = x64::loghead(n, y);
    let sraw = x64::logext(n, lx) - x64::logext(n, ly);
    let res = x64::loghead(n, sraw);
    let f = x64::FlagUpd {
        cf: Some(x64::bool_to_bit(lx < ly)),
        pf: Some(x64::pf_spec(res)),
        af: Some(x64::sub_af_spec(lx, ly)),
        zf: Some(x64::zf_spec(res)),
        sf: Some(x64::sf_spec(n, res)),
        of: Some(x64::of_spec(n, sraw)),
    };
    assert(r.rflags == x64::change_rflags(m.rflags, f));
    lemma_change_rflags_bit(m.rflags, f, 0);
    lemma_change_rflags_bit(m.rflags, f, 6);
    lemma_change_rflags_bit(m.rflags, f, 7);
    lemma_change_rflags_bit(m.rflags, f, 11);
}

/// Bit 6 of `0x10` is clear.
pub proof fn lemma_bit_0x10()
    ensures
        x64::bit(16, 6) == 0,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::p2(6) == 64);
}

/// The flags of an `and`: `cf` and `of` cleared, `pf zf sf` from the result,
/// `af` undefined (mask `0x10`).
pub proof fn lemma_and_spec_shape(n: nat, x: int, y: int, rfl: u32)
    ensures
        x64::gpr_and_spec(n, x, y, rfl).undef == 0x10u32,
        x64::gpr_and_spec(n, x, y, rfl).rflags == x64::change_rflags(
            rfl,
            x64::FlagUpd {
                cf: Some(0),
                pf: Some(x64::pf_spec(x64::gpr_and_spec(n, x, y, rfl).result)),
                af: None,
                zf: Some(x64::zf_spec(x64::gpr_and_spec(n, x, y, rfl).result)),
                sf: Some(x64::sf_spec(n, x64::gpr_and_spec(n, x, y, rfl).result)),
                of: Some(0),
            },
        ),
{
}

/// `test a, b` leaves the registers and memory alone and sets `zf` to "the
/// bitwise and of the operands is 0".
pub proof fn lemma_step_test(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    sz: x64::Size,
    a: u8,
    b: u8,
)
    requires
        x64::wf(m),
        a < 16,
        b < 16,
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::TestRR { sz: sz, a: a, b: b }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::TestRR { sz: sz, a: a, b: b }) is Some,
        ({
            let m1 = x64::step(cu, m, x64::Instr::TestRR { sz: sz, a: a, b: b }).unwrap();
            let n = x64::nbits(sz);
            let r = x64::gpr_and_spec(
                n,
                x64::rgfi_size(m, sz, a),
                x64::rgfi_size(m, sz, b),
                m.rflags,
            );
            &&& m1.rgf == m.rgf && m1.mem == m.mem && m1.xmm == m.xmm && m1.rip == m.rip
                + x64::instr_len(x64::Instr::TestRR { sz: sz, a: a, b: b })
            &&& x64::flgi(m1, x64::zf_bit()) == x64::zf_spec(r.result)
        }),
{
    let n = x64::nbits(sz);
    let x = x64::rgfi_size(m, sz, a);
    let y = x64::rgfi_size(m, sz, b);
    lemma_and_spec_shape(n, x, y, m.rflags);
    let r = x64::gpr_and_spec(n, x, y, m.rflags);
    super::alu::lemma_wur_frame(cu, m, r.rflags, r.undef);
    lemma_bit_0x10();
    assert(r.undef as int == 16);
    assert(x64::bit(r.undef as int, 6) == 0);
    lemma_wur_flag(cu, m, r.rflags, r.undef, 6);
    let f = x64::FlagUpd {
        cf: Some(0),
        pf: Some(x64::pf_spec(r.result)),
        af: None,
        zf: Some(x64::zf_spec(r.result)),
        sf: Some(x64::sf_spec(n, r.result)),
        of: Some(0),
    };
    lemma_change_rflags_bit(m.rflags, f, 6);
}

// ----------------------------------------------------------------------------
// Condition codes
// ----------------------------------------------------------------------------

/// The flags of `a - b` at 32 bits: `zf` is "equal", `sf != of` is "signed less".
pub proof fn lemma_cmp_arith32(lx: int, ly: int)
    requires
        0 <= lx < 0x1_0000_0000,
        0 <= ly < 0x1_0000_0000,
    ensures
        ({
            let sraw = x64::logext(32, lx) - x64::logext(32, ly);
            let res = x64::loghead(32, sraw);
            &&& (x64::zf_spec(res) == 1) <==> (lx == ly)
            &&& ((x64::sf_spec(32, res) % 2 != x64::of_spec(32, sraw)) <==> (lir::signed_of(
                32,
                lx,
            ) < lir::signed_of(32, ly)))
            &&& lir::signed_of(32, lx) == x64::logext(32, lx)
            &&& lir::signed_of(32, ly) == x64::logext(32, ly)
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::p2(32) == 0x1_0000_0000);
    assert(x64::p2(31) == 0x8000_0000);
    assert(lir::pow2(32) == 0x1_0000_0000);
    assert(lir::pow2(32) / 2 == 0x8000_0000);
    assert(x64::loghead(32, lx) == lx && x64::loghead(32, ly) == ly);
    let sx = if lx >= 0x8000_0000 { lx - 0x1_0000_0000 } else { lx };
    let sy = if ly >= 0x8000_0000 { ly - 0x1_0000_0000 } else { ly };
    assert(x64::logext(32, lx) == sx && x64::logext(32, ly) == sy);
    assert(lir::signed_of(32, lx) == sx && lir::signed_of(32, ly) == sy);
    let sraw = sx - sy;
    let res = sraw % 0x1_0000_0000;
    assert(x64::loghead(32, sraw) == res);
    assert(x64::bit(res, 31) == (res / 0x8000_0000) % 2);
    assert(x64::sf_spec(32, res) == (res / 0x8000_0000) % 2);
    assert(x64::zf_spec(res) == 1 <==> res == 0);
    assert((sraw % 0x1_0000_0000 == 0) <==> (lx == ly));
    assert(x64::of_spec(32, sraw) == if -0x8000_0000 <= sraw && sraw < 0x8000_0000 { 0int } else { 1int });
    assert(((res / 0x8000_0000) % 2 != (if -0x8000_0000 <= sraw && sraw < 0x8000_0000 { 0int } else { 1int })) <==> (sx < sy));
}

/// The flags of `a - b` at 64 bits: `zf` is "equal", `sf != of` is "signed less".
pub proof fn lemma_cmp_arith64(lx: int, ly: int)
    requires
        0 <= lx < 0x1_0000_0000_0000_0000,
        0 <= ly < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let sraw = x64::logext(64, lx) - x64::logext(64, ly);
            let res = x64::loghead(64, sraw);
            &&& (x64::zf_spec(res) == 1) <==> (lx == ly)
            &&& ((x64::sf_spec(64, res) % 2 != x64::of_spec(64, sraw)) <==> (lir::signed_of(
                64,
                lx,
            ) < lir::signed_of(64, ly)))
            &&& lir::signed_of(64, lx) == x64::logext(64, lx)
            &&& lir::signed_of(64, ly) == x64::logext(64, ly)
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::p2(64) == 0x1_0000_0000_0000_0000);
    assert(x64::p2(63) == 0x8000_0000_0000_0000);
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    assert(lir::pow2(64) / 2 == 0x8000_0000_0000_0000);
    assert(x64::loghead(64, lx) == lx && x64::loghead(64, ly) == ly);
    let sx = if lx >= 0x8000_0000_0000_0000 { lx - 0x1_0000_0000_0000_0000 } else { lx };
    let sy = if ly >= 0x8000_0000_0000_0000 { ly - 0x1_0000_0000_0000_0000 } else { ly };
    assert(x64::logext(64, lx) == sx && x64::logext(64, ly) == sy);
    assert(lir::signed_of(64, lx) == sx && lir::signed_of(64, ly) == sy);
    let sraw = sx - sy;
    let res = sraw % 0x1_0000_0000_0000_0000;
    assert(x64::loghead(64, sraw) == res);
    assert(x64::bit(res, 63) == (res / 0x8000_0000_0000_0000) % 2);
    assert(x64::sf_spec(64, res) == (res / 0x8000_0000_0000_0000) % 2);
    assert(x64::zf_spec(res) == 1 <==> res == 0);
    assert((sraw % 0x1_0000_0000_0000_0000 == 0) <==> (lx == ly));
    assert(x64::of_spec(64, sraw) == if -0x8000_0000_0000_0000 <= sraw && sraw < 0x8000_0000_0000_0000 { 0int } else { 1int });
    assert(((res / 0x8000_0000_0000_0000) % 2 != (if -0x8000_0000_0000_0000 <= sraw && sraw < 0x8000_0000_0000_0000 { 0int } else { 1int })) <==> (sx < sy));
}

/// The arithmetic of the flags of `a - b`, at 32 or 64 bits.
pub proof fn lemma_cmp_arith(n: nat, lx: int, ly: int)
    requires
        n == 32 || n == 64,
        0 <= lx < x64::p2(n),
        0 <= ly < x64::p2(n),
    ensures
        ({
            let sraw = x64::logext(n, lx) - x64::logext(n, ly);
            let res = x64::loghead(n, sraw);
            &&& (x64::zf_spec(res) == 1) <==> (lx == ly)
            &&& ((x64::sf_spec(n, res) % 2 != x64::of_spec(n, sraw)) <==> (lir::signed_of(
                n,
                lx,
            ) < lir::signed_of(n, ly)))
            &&& lir::signed_of(n, lx) == x64::logext(n, lx)
            &&& lir::signed_of(n, ly) == x64::logext(n, ly)
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    if n == 32 {
        lemma_cmp_arith32(lx, ly);
    } else {
        lemma_cmp_arith64(lx, ly);
    }
}

/// Given the flags `cmp lx, ly` leaves, the condition code of the comparison
/// template holds exactly when LIR's comparison does.
pub proof fn lemma_cc_icmp(s: x64::State, op: lir::ICmp, n: nat, lx: int, ly: int)
    requires
        n == 32 || n == 64,
        0 <= lx < x64::p2(n),
        0 <= ly < x64::p2(n),
        ({
            let sraw = x64::logext(n, lx) - x64::logext(n, ly);
            let res = x64::loghead(n, sraw);
            &&& x64::flgi(s, x64::cf_bit()) == x64::bool_to_bit(lx < ly)
            &&& x64::flgi(s, x64::zf_bit()) == x64::zf_spec(res)
            &&& x64::flgi(s, x64::sf_bit()) == x64::sf_spec(n, res) % 2
            &&& x64::flgi(s, x64::of_bit()) == x64::of_spec(n, sraw)
        }),
    ensures
        x64::jcc_cmovcc_setcc_spec(s, super::templates::cc_of(op)) == lir::icmp(op, n, lx, ly),
{
    lemma_cmp_arith(n, lx, ly);
    assert(x64::cf_bit() == 0 && x64::zf_bit() == 6 && x64::sf_bit() == 7 && x64::of_bit() == 11);
}

/// `setcc dst` sets the low byte of `dst` to 1 or 0 by the condition, keeping
/// the other 56 bits.
pub proof fn lemma_step_setcc(cu: spec_fn(nat) -> nat, m: x64::State, cc: u8, dst: u8)
    requires
        x64::wf(m),
        cc < 16,
        dst < 16,
        x64::canonical(m.rip + x64::instr_len(x64::Instr::Setcc { cc: cc, dst: dst })),
    ensures
        x64::step(cu, m, x64::Instr::Setcc { cc: cc, dst: dst }) == Some(
            x64::State {
                rgf: m.rgf.update(
                    dst as int,
                    ((m.rgf[dst as int] as int) - (m.rgf[dst as int] as int) % 256 + if x64::jcc_cmovcc_setcc_spec(
                        m,
                        cc,
                    ) {
                        1int
                    } else {
                        0int
                    }) as u64,
                ),
                rip: m.rip + x64::instr_len(x64::Instr::Setcc { cc: cc, dst: dst }),
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    let old = m.rgf[dst as int] as int;
    let v: int = if x64::jcc_cmovcc_setcc_spec(m, cc) {
        1
    } else {
        0
    };
    assert(x64::loghead(8, v) == v);
    assert(old - old % 256 + v < 0x1_0000_0000_0000_0000);
    assert(x64::loghead(64, old - old % 256 + v) == old - old % 256 + v);
}

/// `cmovcc dst, src` (64-bit): `dst := src` when the condition holds, else
/// unchanged.
pub proof fn lemma_step_cmov64(cu: spec_fn(nat) -> nat, m: x64::State, cc: u8, dst: u8, src: u8)
    requires
        x64::wf(m),
        cc < 16,
        dst < 16,
        src < 16,
        x64::canonical(
            m.rip + x64::instr_len(
                x64::Instr::Cmovcc { cc: cc, sz: x64::Size::W64, dst: dst, src: src },
            ),
        ),
    ensures
        x64::step(
            cu,
            m,
            x64::Instr::Cmovcc { cc: cc, sz: x64::Size::W64, dst: dst, src: src },
        ) == Some(
            x64::State {
                rgf: if x64::jcc_cmovcc_setcc_spec(m, cc) {
                    m.rgf.update(dst as int, m.rgf[src as int])
                } else {
                    m.rgf
                },
                rip: m.rip + x64::instr_len(
                    x64::Instr::Cmovcc { cc: cc, sz: x64::Size::W64, dst: dst, src: src },
                ),
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    let v = m.rgf[src as int] as int;
    assert(x64::loghead(64, v) == v);
}

} // verus!
