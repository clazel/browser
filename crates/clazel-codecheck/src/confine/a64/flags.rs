//! **The flags of `adds` and `cmp`** (A64): what `add_with_carry` leaves in
//! `PSTATE.N Z C V` after the two instructions the bounds check relies on.
//! `adds t, i, #n` sets the carry exactly when `i + n` wrapped; `cmp t, b`
//! (`subs xzr, t, b`) sets the carry exactly when `t >= b` and the zero flag
//! exactly when `t == b`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bits of an `nzcv` value assembled as `add_with_carry` does.
pub proof fn lemma_nzcv_bits(n: int, z: int, c: int, v: int)
    requires
        0 <= n <= 1,
        0 <= z <= 1,
        0 <= c <= 1,
        0 <= v <= 1,
    ensures
        bit(n * 8 + z * 4 + c * 2 + v, 1) == c,
        bit(n * 8 + z * 4 + c * 2 + v, 2) == z,
{
    lemma_p2();
    let x = n * 8 + z * 4 + c * 2 + v;
    assert(bit(x, 1) == (x / 2) % 2);
    assert(bit(x, 2) == (x / 4) % 2);
    assert(x / 2 == n * 4 + z * 2 + c) by (nonlinear_arith)
        requires
            0 <= v <= 1,
            x == n * 8 + z * 4 + c * 2 + v,
    ;
    assert(x / 4 == n * 2 + z) by (nonlinear_arith)
        requires
            0 <= v <= 1,
            0 <= c <= 1,
            x == n * 8 + z * 4 + c * 2 + v,
    ;
    assert((n * 4 + z * 2 + c) % 2 == c) by (nonlinear_arith)
        requires
            0 <= c <= 1,
    ;
    assert((n * 2 + z) % 2 == z) by (nonlinear_arith)
        requires
            0 <= z <= 1,
    ;
}

/// **`add_with_carry` on 64 bits**: the result, and the carry and zero
/// flags, from a sum in `[0, 2^65)`.
pub proof fn lemma_awc64(x: int, y: int, cin: int)
    requires
        0 <= x < p2(64),
        0 <= y < p2(64),
        cin == 0 || cin == 1,
    ensures
        add_with_carry(64, x, y, cin).0 == (x + y + cin) % p2(64),
        (bit(add_with_carry(64, x, y, cin).1, 1) == 1) == (x + y + cin >= p2(64)),
        (bit(add_with_carry(64, x, y, cin).1, 2) == 1) == ((x + y + cin) % p2(64) == 0),
{
    lemma_p2();
    lemma_trunc64_id(x);
    lemma_trunc64_id(y);
    let us = x + y + cin;
    let m = p2(64);
    let result = trunc(64, us);
    assert(result == us % m);
    vstd::arithmetic::div_mod::lemma_mod_bound(us, m);
    if us < m {
        vstd::arithmetic::div_mod::lemma_small_mod(us as nat, m as nat);
        assert(result == us);
    } else {
        assert(us - m < m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(us, m, 1, us - m);
        assert(result == us - m);
    }
    let fn_ = bit(result, 63);
    assert(0 <= fn_ <= 1) by {
        vstd::arithmetic::div_mod::lemma_mod_bound(result / p2(63), 2);
    }
    let fz = if result == 0 {
        1int
    } else {
        0
    };
    let fc = if result == us {
        0int
    } else {
        1
    };
    let signed_sum = sint(64, x) + sint(64, y) + cin;
    let fv = if sint(64, result) == signed_sum {
        0int
    } else {
        1
    };
    let r = add_with_carry(64, x, y, cin);
    assert(r.1 == fn_ * 8 + fz * 4 + fc * 2 + fv);
    lemma_nzcv_bits(fn_, fz, fc, fv);
}

/// **`adds t, i, #n`** with `i` and `n` below `2^64`: the result is the sum
/// modulo `2^64` and the carry is set exactly when the sum wrapped.
pub proof fn lemma_adds_flags(i: int, n: int)
    requires
        0 <= i < p2(64),
        0 <= n < p2(64),
    ensures
        add_with_carry(64, i, n, 0).0 == (i + n) % p2(64),
        (bit(add_with_carry(64, i, n, 0).1, 1) == 1) == (i + n >= p2(64)),
{
    lemma_awc64(i, n, 0);
}

/// **`cmp t, b`** (`subs xzr, t, b`) with `t` and `b` below `2^64`: the carry
/// is set exactly when `t >= b` and the zero flag exactly when `t == b`.
pub proof fn lemma_cmp_flags(t: int, b: int)
    requires
        0 <= t < p2(64),
        0 <= b < p2(64),
    ensures
        (bit(add_with_carry(64, t, not_vec(64, b), 1).1, 1) == 1) == (t >= b),
        (bit(add_with_carry(64, t, not_vec(64, b), 1).1, 2) == 1) == (t == b),
{
    lemma_p2();
    lemma_trunc64_id(b);
    let nb = not_vec(64, b);
    assert(nb == p2(64) - 1 - b);
    assert(0 <= nb < p2(64));
    lemma_awc64(t, nb, 1);
    let us = t + nb + 1;
    assert(us == t - b + p2(64));
    let m = p2(64);
    if t >= b {
        assert(us >= m);
        assert(us - m < m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(us, m, 1, us - m);
        assert(us % m == t - b);
    } else {
        assert(0 < us < m);
        vstd::arithmetic::div_mod::lemma_small_mod(us as nat, m as nat);
        assert(us % m == us);
    }
}

/// **The effect of `adds xt, xa, #imm`** (64-bit): the destination gets the sum
/// modulo `2^64` and the carry is set exactly when the sum wrapped; nothing
/// else but the program counter changes.
pub proof fn lemma_adds_effect(s: State, i: Instr, t: u8, a: u8, imm: u16, s2: State)
    requires
        s.r.len() == 31,
        t < 31,
        a < 31,
        imm < 4096,
        i == (Instr::AddSubImm {
            sf: Width::W64,
            sub_op: false,
            setflags: true,
            d: t,
            n: a,
            imm12: imm,
            sh: false,
        }),
        step(s, i) == Some(s2),
    ensures
        s2.r == s.r.update(t as int, (((x_read(s, a, 64) + imm as int) % p2(64)) as u64)),
        s2.flag_c == (x_read(s, a, 64) + imm as int >= p2(64)),
        s2.sp == s.sp,
        s2.mem == s.mem,
        s2.vreg == s.vreg,
        s2.pc as int == trunc(64, s.pc as int + 4),
{
    lemma_p2();
    lemma_xr(s, a);
    let iv = x_read(s, a, 64);
    lemma_adds_flags(iv, imm as int);
    let r = add_with_carry(64, iv, imm as int, 0);
    assert(execute(s, i) == Some(x_set(set_nzcv(s, r.1), t, 64, r.0)));
    lemma_trunc64_range(r.0);
    lemma_trunc64_id(r.0);
    assert(s2.flag_c == (bit(r.1, 1) == 1));
}

/// **The effect of `cmp xa, xb`** (`subs xzr, xa, xb`, 64-bit): only the
/// flags and the program counter change; the carry is set exactly when
/// `a >= b` and the zero flag exactly when `a == b`.
pub proof fn lemma_cmp_effect(s: State, i: Instr, a: u8, bb: u8, s2: State)
    requires
        s.r.len() == 31,
        a < 31,
        bb < 31,
        i == (Instr::AddSubShiftedReg {
            sf: Width::W64,
            sub_op: true,
            setflags: true,
            d: abi::sp_reg(),
            n: a,
            m: bb,
            shift_type: ShiftType::Lsl,
            shift_amount: 0,
        }),
        step(s, i) == Some(s2),
    ensures
        s2.r == s.r,
        s2.flag_c == (x_read(s, a, 64) >= x_read(s, bb, 64)),
        s2.flag_z == (x_read(s, a, 64) == x_read(s, bb, 64)),
        s2.sp == s.sp,
        s2.mem == s.mem,
        s2.vreg == s.vreg,
        s2.pc as int == trunc(64, s.pc as int + 4),
{
    lemma_p2();
    lemma_xr(s, a);
    lemma_xr(s, bb);
    let x = x_read(s, a, 64);
    let y = x_read(s, bb, 64);
    lemma_cmp_flags(x, y);
    lemma_trunc64_id(y);
    assert(shift_reg(s, bb, ShiftType::Lsl, 0nat, 64nat) == y) by {
        assert(lsl(64, y, 0nat) == trunc(64, y * p2(0)));
    }
    let r = add_with_carry(64, x, not_vec(64, y), 1);
    assert(execute(s, i) == Some(x_set(set_nzcv(s, r.1), abi::sp_reg(), 64, r.0)));
    assert(s2.flag_c == (bit(r.1, 1) == 1));
    assert(s2.flag_z == (bit(r.1, 2) == 1));
}

} // verus!
