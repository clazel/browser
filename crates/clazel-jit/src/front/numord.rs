//! What the semantics' conversion of an int32 to a double does to order,
//! equality and ToInt32: the facts the comparison and bitwise lowerings of
//! [`super::intcmp`] and [`super::bitops`] need, because the bytecode
//! semantics compares and truncates the doubles that int32s stand for
//! (`num_bits`, `f64_of_int`), while LIR compares the integers themselves.
//!
//! Everything here is a proof about `clazel-js-vm`'s `f64_of_int` as it is
//! defined (an open function, not an uninterpreted one): no axiom. For an
//! integer `n` with `1 <= |n| < 2^32`, `f64_of_int(n)` has sign `n < 0`,
//! exponent `ilog2(|n|) + 1023` and fraction `|n| * 2^(52 - k) - 2^52`
//! (`k = ilog2(|n|)`), so its sign-magnitude key is [`korder`], which is
//! strictly increasing. From that: [`lemma_less_than_int`] (`Number::lessThan`
//! of two such doubles is `i < j`), [`lemma_equal_int`] (`Number::equal` is
//! `i == j`), [`lemma_to_int32`] and [`lemma_to_uint32`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

use vstd::arithmetic::power2::{
    lemma2_to64,
    lemma2_to64_rest,
    lemma_pow2_adds,
    lemma_pow2_pos,
    lemma_pow2_strictly_increases,
    pow2,
};

/// `2^52`.
pub open spec fn t52() -> int {
    4503599627370496
}

/// The fraction field of `f64_of_int(±m)`.
pub open spec fn mag_frac(m: nat) -> int {
    (m * pow2((52 - js::ilog2(m)) as nat)) as int - pow2(52) as int
}

/// The magnitude bits (exponent and fraction) of `f64_of_int(±m)`.
pub open spec fn pos_bits(m: nat) -> int {
    (js::ilog2(m) + 1023) * t52() + mag_frac(m)
}

/// The sign-magnitude key `f64_of_int(n)` has.
pub open spec fn korder(n: int) -> int {
    if n == 0 {
        0
    } else if n > 0 {
        pos_bits(n as nat)
    } else {
        -pos_bits((-n) as nat)
    }
}

/// `2^ilog2(n) <= n < 2^(ilog2(n) + 1)`.
pub proof fn lemma_ilog2_bounds(n: nat)
    requires
        n >= 1,
    ensures
        pow2(js::ilog2(n)) <= n,
        n < pow2(js::ilog2(n) + 1),
    decreases n,
{
    lemma2_to64();
    if n <= 1 {
        assert(n == 1);
    } else {
        let h = (n / 2) as nat;
        lemma_ilog2_bounds(h);
        let l = js::ilog2(h);
        assert(js::ilog2(n) == 1 + l);
        lemma_pow2_adds(1, l);
        lemma_pow2_adds(1, l + 1);
        assert(pow2(1 + l) == 2 * pow2(l));
        assert(pow2(l + 2) == 2 * pow2(l + 1));
    }
}

/// `ilog2` is monotone.
pub proof fn lemma_ilog2_mono(a: nat, b: nat)
    requires
        1 <= a <= b,
    ensures
        js::ilog2(a) <= js::ilog2(b),
{
    lemma_ilog2_bounds(a);
    lemma_ilog2_bounds(b);
    if js::ilog2(a) > js::ilog2(b) {
        let lb = js::ilog2(b);
        if js::ilog2(a) > lb + 1 {
            lemma_pow2_strictly_increases(lb + 1, js::ilog2(a));
        }
        assert(pow2(js::ilog2(a)) >= pow2(lb + 1));
        assert(false);
    }
}

/// The fraction of a magnitude below `2^32` is in `[0, 2^52)`, and its
/// `ilog2` is at most 31.
pub proof fn lemma_frac_bounds(m: nat)
    requires
        1 <= m < 0x1_0000_0000,
    ensures
        js::ilog2(m) <= 31,
        0 <= mag_frac(m) < t52(),
{
    lemma_ilog2_bounds(m);
    lemma2_to64();
    let k = js::ilog2(m);
    if k > 31 {
        lemma_pow2_strictly_increases(32, k);
        assert(false);
    }
    let p = pow2(k);
    let q = pow2((52 - k) as nat);
    lemma_pow2_adds(k, (52 - k) as nat);
    lemma_pow2_adds(k, 1);
    lemma_pow2_pos(k);
    lemma_pow2_pos((52 - k) as nat);
    assert(p * q == pow2(52));
    lemma2_to64_rest();
    assert(pow2(52) == t52());
    assert(m * q >= p * q) by (nonlinear_arith)
        requires
            m >= p,
            q > 0,
    ;
    assert(m * q < 2 * p * q) by (nonlinear_arith)
        requires
            m < 2 * p,
            q > 0,
            p > 0,
    ;
    assert(2 * p * q == 2 * (p * q)) by (nonlinear_arith);
}

/// `pos_bits` is in `[1023 * 2^52, 1055 * 2^52)`, so positive.
pub proof fn lemma_pos_bits_range(m: nat)
    requires
        1 <= m < 0x1_0000_0000,
    ensures
        1023 * t52() <= pos_bits(m) < 1055 * t52(),
{
    lemma_frac_bounds(m);
}

/// `pos_bits` is strictly increasing.
pub proof fn lemma_pos_mono(m1: nat, m2: nat)
    requires
        1 <= m1 < m2 < 0x1_0000_0000,
    ensures
        pos_bits(m1) < pos_bits(m2),
{
    lemma_frac_bounds(m1);
    lemma_frac_bounds(m2);
    lemma_ilog2_mono(m1, m2);
    let k1 = js::ilog2(m1);
    let k2 = js::ilog2(m2);
    if k1 == k2 {
        let q = pow2((52 - k1) as nat);
        lemma_pow2_pos((52 - k1) as nat);
        assert((m2 - m1) * q > 0) by (nonlinear_arith)
            requires
                m2 > m1,
                q > 0,
        ;
        assert(m2 * q - m1 * q == (m2 - m1) * q) by (nonlinear_arith);
    } else {
        assert(k1 < k2);
    }
}

/// `korder` is strictly increasing on `(-2^32, 2^32)`.
pub proof fn lemma_korder_mono(i: int, j: int)
    requires
        -0x1_0000_0000 < i < j < 0x1_0000_0000,
    ensures
        korder(i) < korder(j),
{
    if i > 0 {
        lemma_pos_mono(i as nat, j as nat);
    } else if j < 0 {
        lemma_pos_mono((-j) as nat, (-i) as nat);
    } else if i == 0 {
        lemma_pos_bits_range(j as nat);
    } else if j == 0 {
        lemma_pos_bits_range((-i) as nat);
    } else {
        lemma_pos_bits_range(j as nat);
        lemma_pos_bits_range((-i) as nat);
    }
}

/// Packing a sign, an exponent and a fraction into a double's bits and
/// reading them back.
pub proof fn lemma_pack(sg: u64, e: u64, f: u64)
    requires
        sg < 2,
        e < 2048,
        f < 0x10_0000_0000_0000,
    ensures
        ({
            let b = (sg << 63u64) | (e << 52u64) | f;
            &&& b as int == sg as int * 0x8000_0000_0000_0000int + e as int * 0x10_0000_0000_0000int
                + f as int
            &&& js::f64_sign(b) == sg
            &&& js::f64_exp(b) == e
            &&& js::f64_frac(b) == f
            &&& (b & 0x7FFF_FFFF_FFFF_FFFFu64) as int == e as int * 0x10_0000_0000_0000int + f as int
        }),
{
    assert((((sg << 63u64) | (e << 52u64) | f) as int) == sg as int * 0x8000_0000_0000_0000int
        + e as int * 0x10_0000_0000_0000int + f as int) by (bit_vector)
        requires
            sg < 2,
            e < 2048,
            f < 0x10_0000_0000_0000u64,
    ;
    assert((((sg << 63u64) | (e << 52u64) | f) >> 63u64) == sg) by (bit_vector)
        requires
            sg < 2,
            e < 2048,
            f < 0x10_0000_0000_0000u64,
    ;
    assert(((((sg << 63u64) | (e << 52u64) | f) >> 52u64) & 0x7FFu64) == e) by (bit_vector)
        requires
            sg < 2,
            e < 2048,
            f < 0x10_0000_0000_0000u64,
    ;
    assert((((sg << 63u64) | (e << 52u64) | f) & 0xF_FFFF_FFFF_FFFFu64) == f) by (bit_vector)
        requires
            sg < 2,
            e < 2048,
            f < 0x10_0000_0000_0000u64,
    ;
    assert(((((sg << 63u64) | (e << 52u64) | f) & 0x7FFF_FFFF_FFFF_FFFFu64) as int) == e as int
        * 0x10_0000_0000_0000int + f as int) by (bit_vector)
        requires
            sg < 2,
            e < 2048,
            f < 0x10_0000_0000_0000u64,
    ;
}

/// The fields of `f64_of_int(n)` for `n != 0` and `|n| < 2^32`: sign,
/// exponent, fraction, and the key.
pub proof fn lemma_fields(n: int)
    requires
        n != 0,
        -0x1_0000_0000 < n < 0x1_0000_0000,
    ensures
        ({
            let b = js::f64_of_int(n);
            let m = (if n < 0 { -n } else { n }) as nat;
            &&& js::f64_sign(b) == (if n < 0 { 1u64 } else { 0u64 })
            &&& js::f64_exp(b) as int == js::ilog2(m) + 1023
            &&& js::f64_frac(b) as int == mag_frac(m)
            &&& js::f64_key(b) == korder(n)
        }),
{
    let m = (if n < 0 { -n } else { n }) as nat;
    lemma_frac_bounds(m);
    lemma2_to64();
    lemma2_to64_rest();
    assert(pow2(52) == t52());
    let k = js::ilog2(m);
    let sg: u64 = if n < 0 { 1 } else { 0 };
    let e: u64 = (k + 1023) as u64;
    let f: u64 = mag_frac(m) as u64;
    lemma_pack(sg, e, f);
    let pk = (sg << 63u64) | (e << 52u64) | f;
    let b = js::f64_of_int(n);
    assert(b as int == pk as int) by {
        assert(pos_bits(m) == (k + 1023) * t52() + mag_frac(m));
    }
    assert(b == pk);
    if n > 0 {
        assert(js::f64_key(b) == pos_bits(m));
    } else {
        assert(js::f64_key(b) == -pos_bits(m));
    }
}

/// `f64_of_int(n)` is neither NaN, an infinity, nor a negative zero, and is
/// a zero exactly for `0`, which is `+0`.
pub proof fn lemma_shape(n: int)
    requires
        -0x1_0000_0000 < n < 0x1_0000_0000,
    ensures
        ({
            let b = js::f64_of_int(n);
            &&& !js::is_nan(b)
            &&& !js::is_inf(b)
            &&& b != 0x8000_0000_0000_0000u64
            &&& (n == 0) <==> b == 0
            &&& js::f64_key(b) == korder(n)
        }),
{
    if n == 0 {
        assert(js::f64_of_int(0) == 0u64);
        assert(js::f64_exp(0u64) == 0) by (bit_vector);
        assert((0u64 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64) by (bit_vector);
        assert((0u64 >> 63u64) == 0u64) by (bit_vector);
        assert(js::f64_key(0u64) == 0);
    } else {
        lemma_fields(n);
        let b = js::f64_of_int(n);
        let m = (if n < 0 { -n } else { n }) as nat;
        lemma_frac_bounds(m);
        assert(js::f64_exp(b) != 0x7FF);
        assert(js::f64_exp(b) != 0);
        assert(b != 0u64) by {
            if b == 0 {
                assert(js::f64_exp(0u64) == 0) by (bit_vector);
            }
        }
        assert(b != 0x8000_0000_0000_0000u64) by {
            if b == 0x8000_0000_0000_0000u64 {
                assert(js::f64_exp(0x8000_0000_0000_0000u64) == 0) by (bit_vector);
            }
        }
        assert(b != 0x7FF0_0000_0000_0000u64) by {
            if b == 0x7FF0_0000_0000_0000u64 {
                assert(js::f64_exp(0x7FF0_0000_0000_0000u64) == 0x7FF) by (bit_vector);
            }
        }
        assert(b != 0xFFF0_0000_0000_0000u64) by {
            if b == 0xFFF0_0000_0000_0000u64 {
                assert(js::f64_exp(0xFFF0_0000_0000_0000u64) == 0x7FF) by (bit_vector);
            }
        }
    }
}

/// `Number::lessThan` of the doubles two integers stand for is `i < j`
/// (never `undefined`).
pub proof fn lemma_less_than_int(i: int, j: int)
    requires
        -0x1_0000_0000 < i < 0x1_0000_0000,
        -0x1_0000_0000 < j < 0x1_0000_0000,
    ensures
        js::number_less_than(js::f64_of_int(i), js::f64_of_int(j)) == Some(i < j),
{
    lemma_shape(i);
    lemma_shape(j);
    let x = js::f64_of_int(i);
    let y = js::f64_of_int(j);
    if i == j {
    } else if i < j {
        lemma_korder_mono(i, j);
        assert(x != y);
    } else {
        lemma_korder_mono(j, i);
        assert(x != y);
    }
}

/// `Number::equal` of the doubles two integers stand for is `i == j`.
pub proof fn lemma_equal_int(i: int, j: int)
    requires
        -0x1_0000_0000 < i < 0x1_0000_0000,
        -0x1_0000_0000 < j < 0x1_0000_0000,
    ensures
        js::number_equal(js::f64_of_int(i), js::f64_of_int(j)) == (i == j),
{
    lemma_shape(i);
    lemma_shape(j);
    let x = js::f64_of_int(i);
    let y = js::f64_of_int(j);
    if i == j {
    } else if i < j {
        lemma_korder_mono(i, j);
        assert(x != y);
    } else {
        lemma_korder_mono(j, i);
        assert(x != y);
    }
}

/// The truncated magnitude of `f64_of_int(n)` is `|n|`.
pub proof fn lemma_trunc_abs(n: int)
    requires
        n != 0,
        -0x1_0000_0000 < n < 0x1_0000_0000,
    ensures
        js::f64_trunc_abs(js::f64_of_int(n)) == (if n < 0 { -n } else { n }) as nat,
{
    lemma_fields(n);
    let b = js::f64_of_int(n);
    let m = (if n < 0 { -n } else { n }) as nat;
    lemma_frac_bounds(m);
    lemma2_to64();
    let k = js::ilog2(m);
    let q = pow2((52 - k) as nat);
    lemma_pow2_pos((52 - k) as nat);
    let e: int = js::f64_exp(b) as int;
    assert(e == k + 1023);
    let mm: int = pow2(52) as int + js::f64_frac(b) as int;
    lemma2_to64_rest();
    assert(pow2(52) == t52());
    assert(mm == m * q);
    let kk: int = e - 1075;
    assert(kk < 0);
    assert(-kk == 52 - k);
    assert(((m * q) as int) / (q as int) == m as int) by {
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(m as int, q as int);
        assert(q * m == m * q) by (nonlinear_arith);
    }
}

/// `ToInt32` of the double an int32 stands for is that int32.
pub proof fn lemma_to_int32(i: i32)
    ensures
        js::to_int32(js::f64_of_int(i as int)) == i,
{
    let n = i as int;
    lemma_shape(n);
    let b = js::f64_of_int(n);
    if n == 0 {
        assert(b == 0u64);
    } else {
        lemma_fields(n);
        lemma_trunc_abs(n);
        assert(js::is_finite(b));
        assert(!js::is_zero(b));
        let t: int = js::f64_trunc_abs(b) as int;
        let sgn: int = if js::f64_sign(b) == 1 { -t } else { t };
        assert(sgn == n);
        assert(js::f64_int32bit(b) as int == n % 4294967296int);
        if n > 0 {
            assert(n % 4294967296int == n);
        } else {
            assert(n % 4294967296int == n + 4294967296int);
        }
    }
}

/// `ToUint32` of the double an int32 stands for is the int32 read unsigned.
pub proof fn lemma_to_uint32(i: i32)
    ensures
        js::to_uint32(js::f64_of_int(i as int)) == (i as u32),
{
    let n = i as int;
    lemma_shape(n);
    let b = js::f64_of_int(n);
    assert(((i as u32) as int) == (if i >= 0 { i as int } else { i as int + 4294967296int })) by (bit_vector);
    if n == 0 {
        assert(b == 0u64);
    } else {
        lemma_fields(n);
        lemma_trunc_abs(n);
        assert(js::is_finite(b));
        assert(!js::is_zero(b));
        let t: int = js::f64_trunc_abs(b) as int;
        let sgn: int = if js::f64_sign(b) == 1 { -t } else { t };
        assert(sgn == n);
        assert(js::f64_int32bit(b) as int == n % 4294967296int);
        if n > 0 {
            assert(n % 4294967296int == n);
        } else {
            assert(n % 4294967296int == n + 4294967296int);
        }
    }
}

} // verus!
