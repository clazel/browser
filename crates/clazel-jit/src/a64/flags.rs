//! The flags `cmp` leaves and what `cset` and `csel` read from them: the
//! A64 counterpart of [`crate::flags`]. `cmp rn, rm` is `subs xzr, rn, rm`:
//! the flags are `NZCV` of `AddWithCarry(rn, NOT(rm), 1)`. The ten LIR
//! comparisons are ten of the condition codes of `ConditionHolds`, and
//! [`lemma_cc_icmp`] shows each is true exactly when LIR's comparison is.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `nzcv` that `cmp x, y` leaves at width `n`.
pub open spec fn cmp_nzcv(n: nat, x: int, y: int) -> int {
    isa::add_with_carry(n, x, isa::not_vec(n, y), 1).1
}

/// `n`, `z`, `c`, `v` are 0 or 1 and are the bits of `nzcv`.
pub proof fn lemma_nzcv_bits(a: int, b: int, c: int, d: int)
    requires
        0 <= a <= 1,
        0 <= b <= 1,
        0 <= c <= 1,
        0 <= d <= 1,
    ensures
        isa::bit(a * 8 + b * 4 + c * 2 + d, 3) == a,
        isa::bit(a * 8 + b * 4 + c * 2 + d, 2) == b,
        isa::bit(a * 8 + b * 4 + c * 2 + d, 1) == c,
        isa::bit(a * 8 + b * 4 + c * 2 + d, 0) == d,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(isa::p2(0) == 1 && isa::p2(1) == 2 && isa::p2(2) == 4 && isa::p2(3) == 8);
}

/// The flags of `x - y` at 32 bits: `C` is "unsigned greater or equal", `Z` is
/// "equal", and `N == V` is "signed greater or equal".
#[verifier::rlimit(400)]
pub proof fn lemma_cmp_arith32(x: int, y: int)
    requires
        0 <= x < 0x1_0000_0000,
        0 <= y < 0x1_0000_0000,
    ensures
        ({
            let nzcv = cmp_nzcv(32, x, y);
            &&& (isa::bit(nzcv, 1) == 1) <==> (x >= y)
            &&& (isa::bit(nzcv, 2) == 1) <==> (x == y)
            &&& (isa::bit(nzcv, 3) == isa::bit(nzcv, 0)) <==> (lir::signed_of(32, x)
                >= lir::signed_of(32, y))
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let p: int = 0x1_0000_0000;
    let h: int = 0x8000_0000;
    assert(isa::p2(32) == p && isa::p2(31) == h && lir::pow2(32) == p);
    let ys = p - 1 - y;
    assert(isa::not_vec(32, y) == ys);
    assert(isa::trunc(32, x) == x && isa::trunc(32, y) == y && isa::trunc(32, ys) == ys);
    let us = x + ys + 1;
    let res = us % p;
    let sx = if x >= h { x - p } else { x };
    let sy = if y >= h { y - p } else { y };
    let sys = if ys >= h { ys - p } else { ys };
    assert(isa::sint(32, x) == sx && isa::sint(32, y) == sy && isa::sint(32, ys) == sys);
    assert(lir::signed_of(32, x) == sx && lir::signed_of(32, y) == sy);
    let ss = sx + sys + 1;
    assert(ss == sx - sy);
    let fn_ = (res / h) % 2;
    let fz = if res == 0 {
        1int
    } else {
        0
    };
    let fc = if res == us {
        0int
    } else {
        1
    };
    let sres = if res >= h {
        res - p
    } else {
        res
    };
    assert(isa::sint(32, res) == sres);
    let fv = if sres == ss {
        0int
    } else {
        1
    };
    assert(isa::bit(res, 31) == fn_);
    assert(isa::add_with_carry(32, x, isa::not_vec(32, y), 1) == (res, fn_ * 8 + fz * 4 + fc * 2 + fv));
    assert(0 <= fn_ <= 1 && 0 <= res < p);
    lemma_nzcv_bits(fn_, fz, fc, fv);
}

/// The flags of `x - y` at 64 bits (see [`lemma_cmp_arith32`]).
#[verifier::rlimit(400)]
pub proof fn lemma_cmp_arith64(x: int, y: int)
    requires
        0 <= x < 0x1_0000_0000_0000_0000,
        0 <= y < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let nzcv = cmp_nzcv(64, x, y);
            &&& (isa::bit(nzcv, 1) == 1) <==> (x >= y)
            &&& (isa::bit(nzcv, 2) == 1) <==> (x == y)
            &&& (isa::bit(nzcv, 3) == isa::bit(nzcv, 0)) <==> (lir::signed_of(64, x)
                >= lir::signed_of(64, y))
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let p: int = 0x1_0000_0000_0000_0000;
    let h: int = 0x8000_0000_0000_0000;
    assert(isa::p2(64) == p && isa::p2(63) == h && lir::pow2(64) == p);
    let ys = p - 1 - y;
    assert(isa::not_vec(64, y) == ys);
    assert(isa::trunc(64, x) == x && isa::trunc(64, y) == y && isa::trunc(64, ys) == ys);
    let us = x + ys + 1;
    let res = us % p;
    let sx = if x >= h { x - p } else { x };
    let sy = if y >= h { y - p } else { y };
    let sys = if ys >= h { ys - p } else { ys };
    assert(isa::sint(64, x) == sx && isa::sint(64, y) == sy && isa::sint(64, ys) == sys);
    assert(lir::signed_of(64, x) == sx && lir::signed_of(64, y) == sy);
    let ss = sx + sys + 1;
    assert(ss == sx - sy);
    let fn_ = (res / h) % 2;
    let fz = if res == 0 {
        1int
    } else {
        0
    };
    let fc = if res == us {
        0int
    } else {
        1
    };
    let sres = if res >= h {
        res - p
    } else {
        res
    };
    assert(isa::sint(64, res) == sres);
    let fv = if sres == ss {
        0int
    } else {
        1
    };
    assert(isa::bit(res, 63) == fn_);
    assert(isa::add_with_carry(64, x, isa::not_vec(64, y), 1) == (res, fn_ * 8 + fz * 4 + fc * 2 + fv));
    assert(0 <= fn_ <= 1 && 0 <= res < p);
    lemma_nzcv_bits(fn_, fz, fc, fv);
}

/// The flags of `x - y` at 32 or 64 bits.
pub proof fn lemma_cmp_arith(n: nat, x: int, y: int)
    requires
        n == 32 || n == 64,
        0 <= x < isa::p2(n),
        0 <= y < isa::p2(n),
    ensures
        ({
            let nzcv = cmp_nzcv(n, x, y);
            &&& (isa::bit(nzcv, 1) == 1) <==> (x >= y)
            &&& (isa::bit(nzcv, 2) == 1) <==> (x == y)
            &&& (isa::bit(nzcv, 3) == isa::bit(nzcv, 0)) <==> (lir::signed_of(n, x)
                >= lir::signed_of(n, y))
        }),
{
    super::memlemmas::lemma_p2_consts();
    if n == 32 {
        lemma_cmp_arith32(x, y);
    } else {
        lemma_cmp_arith64(x, y);
    }
}

/// `set_nzcv(s, cmp_nzcv(..))` has the four flags of the comparison, and the
/// condition `cset_cond(c)` of the `csinc` fails exactly when LIR's comparison
/// `c` is true.
pub proof fn lemma_cc_icmp(s: isa::State, c: lir::ICmp, n: nat, x: int, y: int)
    requires
        n == 32 || n == 64,
        0 <= x < isa::p2(n),
        0 <= y < isa::p2(n),
    ensures
        ({
            let t = isa::set_nzcv(s, cmp_nzcv(n, x, y));
            !isa::condition_holds(t, super::templates::cset_cond(c)) == lir::icmp(c, n, x, y)
        }),
{
    lemma_cmp_arith(n, x, y);
    let t = isa::set_nzcv(s, cmp_nzcv(n, x, y));
    let nzcv = cmp_nzcv(n, x, y);
    assert(t.flag_n == (isa::bit(nzcv, 3) == 1));
    assert(t.flag_z == (isa::bit(nzcv, 2) == 1));
    assert(t.flag_c == (isa::bit(nzcv, 1) == 1));
    assert(t.flag_v == (isa::bit(nzcv, 0) == 1));
    // bits are 0 or 1
    assert(0 <= isa::bit(nzcv, 3) <= 1 && 0 <= isa::bit(nzcv, 0) <= 1) by {
        vstd::arithmetic::power2::lemma2_to64();
    }
    assert((t.flag_n == t.flag_v) == (isa::bit(nzcv, 3) == isa::bit(nzcv, 0)));
    match c {
        lir::ICmp::Eq => {},
        lir::ICmp::Ne => {},
        lir::ICmp::LtS => {},
        lir::ICmp::LtU => {},
        lir::ICmp::GtS => {},
        lir::ICmp::GtU => {},
        lir::ICmp::LeS => {},
        lir::ICmp::LeU => {},
        lir::ICmp::GeS => {},
        lir::ICmp::GeU => {},
    }
}

/// `cmp x0, x1` at width `sf` (flags only): the state after it is the state with
/// the flags of `x - y` and `pc` advanced by 4.
pub proof fn lemma_step_cmp(s: isa::State, sf: isa::Width, x: u64, y: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(super::alu::bits(sf)),
        y < isa::p2(super::alu::bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::cmp_rr(sf, 0, 1)) == Some(
            isa::State {
                pc: (s.pc + 4) as u64,
                ..isa::set_nzcv(s, cmp_nzcv(super::alu::bits(sf), x as int, y as int))
            },
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    super::alu::lemma_trunc_small(n, x as int);
    super::alu::lemma_trunc_small(n, y as int);
    assert(isa::lsl(n, y as int, 0) == y as int) by {
        assert(isa::p2(0) == 1);
    }
}

/// `cmp x0, #0` at width `sf`: the flags of `x - 0`.
pub proof fn lemma_step_cmp_zero(s: isa::State, sf: isa::Width, r: u8, x: u64)
    requires
        isa::wf(s),
        r < 31,
        s.r[r as int] == x,
        x < isa::p2(super::alu::bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::cmp_zero(sf, r)) == Some(
            isa::State {
                pc: (s.pc + 4) as u64,
                ..isa::set_nzcv(s, cmp_nzcv(super::alu::bits(sf), x as int, 0))
            },
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    super::alu::lemma_trunc_small(n, x as int);
    // operand2 is NOT(0) = ones, carry in 1
    assert(isa::not_vec(n, 0) == isa::p2(n) - 1);
}

/// `cset w0, cc` (`csinc w0, wzr, wzr, cond`): `x0` is 0 if `cond` holds and 1
/// if not.
pub proof fn lemma_step_cset(s: isa::State, cond: u8)
    requires
        isa::wf(s),
        cond < 14,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::cset0(cond)) == Some(
            super::alu::wrote_x0(s, if isa::condition_holds(s, cond) {
                0int
            } else {
                1int
            }, 32),
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    assert(isa::trunc(32, 0int + 1) == 1);
}

/// `csel x0, x0, x1, ne` after a `cmp w2, #0`: see [`super::mid::lemma_mid_select`];
/// the step itself.
pub proof fn lemma_step_csel_ne(s: isa::State, v1: u64, v2: u64)
    requires
        isa::wf(s),
        s.r[0] == v1,
        s.r[1] == v2,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::select_mid()[1]) == Some(
            super::alu::wrote_x0(s, if !s.flag_z {
                v1 as int
            } else {
                v2 as int
            }, 64),
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    super::alu::lemma_trunc_small(64, v1 as int);
    super::alu::lemma_trunc_small(64, v2 as int);
    assert(isa::condition_holds(s, 1) == !s.flag_z);
}

} // verus!
