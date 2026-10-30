//! Facts the executable field code is proven from: about the spec's
//! constants, about `value`, and the modular arithmetic of Montgomery form.
//! Everything here is proven, none is assumed.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The constants.
// ---------------------------------------------------------------------

/// `R^(-1) mod m` as a number: `((2^64)⁻¹ mod m)^6 mod m`, the factor that
/// fiat's `from_montgomery` multiplies by.
pub open spec fn rinv(w: Which) -> nat {
    match w {
        Which::P => 0x00000014_00000014_0000000c_00000002_fffffffc_fffffffa_fffffffb_fffffffd_ffffffeb_ffffffd8_ffffffe1_00000006nat,
        Which::N => 0x355ca87d_e39dbb1f_a150206c_e4f194ac_78d4ba58_66d61787_e29f9fb7_0a9da219_d26d4aeb_a664edb0_610ae855_f2c0d911nat,
    }
}

/// `limb_pow` at the arguments the code uses, as numerals.
pub proof fn lemma_limb_pow_consts()
    ensures
        limb_pow(0) == 1,
        limb_pow(1) == 0x1_0000_0000_0000_0000nat,
        limb_pow(2) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat,
        limb_pow(3) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat,
        limb_pow(4) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat,
        limb_pow(5) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat,
        limb_pow(6) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat,
{
    assert(limb_pow(1) == 0x1_0000_0000_0000_0000nat) by (compute_only);
    assert(limb_pow(2) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat) by (compute_only);
    assert(limb_pow(3) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat) by (compute_only);
    assert(limb_pow(4) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat) by (compute_only);
    assert(limb_pow(5) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat) by (compute_only);
    assert(limb_pow(6) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat) by (compute_only);
}

/// The moduli are odd numbers between 2 and `R = 2^384`.
pub proof fn lemma_modulus(w: Which)
    ensures
        2 < modulus(w) < radix(),
        modulus(w) % 2 == 1,
{
    lemma_limb_pow_consts();
    match w {
        Which::P => {
            assert(modulus(Which::P) == crate::spec::p384().p);
            assert(2 < crate::spec::p384().p < limb_pow(6) && crate::spec::p384().p % 2 == 1) by (compute_only);
        },
        Which::N => {
            assert(2 < crate::spec::p384().n < limb_pow(6) && crate::spec::p384().n % 2 == 1) by (compute_only);
        },
    }
}

/// `(2^64)⁻¹ mod m` is an inverse of `2^64`, below `m`, and `rinv` is its
/// sixth power, which inverts `R`.
pub proof fn lemma_rinv(w: Which)
    ensures
        base_inv(w) < modulus(w),
        base() * base_inv(w) % modulus(w) == 1,
        rinv(w) < modulus(w),
        (base_inv(w) * base_inv(w) * base_inv(w) * base_inv(w) * base_inv(w) * base_inv(w)) % modulus(w) == rinv(w),
        radix() * rinv(w) % modulus(w) == 1,
{
    match w {
        Which::P => {
            assert(base_inv(Which::P) < modulus(Which::P)
                && base() * base_inv(Which::P) % modulus(Which::P) == 1
                && rinv(Which::P) < modulus(Which::P)
                && (base_inv(Which::P) * base_inv(Which::P) * base_inv(Which::P) * base_inv(Which::P) * base_inv(Which::P) * base_inv(Which::P)) % modulus(Which::P) == rinv(Which::P)
                && radix() * rinv(Which::P) % modulus(Which::P) == 1) by (compute_only);
        },
        Which::N => {
            assert(base_inv(Which::N) < modulus(Which::N)
                && base() * base_inv(Which::N) % modulus(Which::N) == 1
                && rinv(Which::N) < modulus(Which::N)
                && (base_inv(Which::N) * base_inv(Which::N) * base_inv(Which::N) * base_inv(Which::N) * base_inv(Which::N) * base_inv(Which::N)) % modulus(Which::N) == rinv(Which::N)
                && radix() * rinv(Which::N) % modulus(Which::N) == 1) by (compute_only);
        },
    }
}

/// `from_montgomery` multiplies by `rinv` (fiat's `((2^64)⁻¹ mod m)^6`, reduced).
pub proof fn lemma_from_montgomery(w: Which, z: Seq<u64>)
    ensures
        from_montgomery(w, z) == value(z) * rinv(w) % modulus(w),
        from_montgomery(w, z) < modulus(w),
{
    lemma_modulus(w);
    lemma_rinv(w);
    let q = base_inv(w) * base_inv(w) * base_inv(w) * base_inv(w) * base_inv(w) * base_inv(w);
    let m = modulus(w);
    // value * q % m == value * (q % m) % m
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(value(z) as int, q as int, m as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(value(z) as int * q as int, m as int);
}

// ---------------------------------------------------------------------
// Modular arithmetic of Montgomery form, on abstract numbers: `m` the
// modulus, `rr` the radix `R` and `r` its inverse, `rr * r ≡ 1 (mod m)`.
// ---------------------------------------------------------------------

/// `x r R ≡ x`.
proof fn lemma_unit(m: nat, rr: nat, r: nat, x: nat)
    requires
        m > 0,
        rr * r % m == 1,
    ensures
        (x * r) * rr % m == x % m,
{
    assert((x * r) * rr == x * (rr * r)) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(x as int, (rr * r) as int, m as int);
    assert(x * ((rr * r) % m) == x * 1);
}

/// Multiplying by `r` can be undone: `x r ≡ y r` gives `x ≡ y`.
pub proof fn lemma_cancel(m: nat, rr: nat, r: nat, x: nat, y: nat)
    requires
        m > 0,
        rr * r % m == 1,
        x * r % m == y * r % m,
    ensures
        x % m == y % m,
{
    lemma_unit(m, rr, r, x);
    lemma_unit(m, rr, r, y);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left((x * r) as int, rr as int, m as int);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left((y * r) as int, rr as int, m as int);
}

/// Into the Montgomery domain: multiplying `x` (as a Montgomery-domain
/// number) by `R^2 mod m` stands for `x`: `(x r)(r2 r) ≡ x` when `r2 ≡ R R`.
pub proof fn lemma_to_mont(m: nat, rr: nat, r: nat, r2: nat, x: nat)
    requires
        m > 0,
        rr * r % m == 1,
        r2 % m == (rr * rr) % m,
    ensures
        ((x * r % m) * (r2 * r % m)) % m == x % m,
{
    let t = rr * r;
    vstd::arithmetic::div_mod::lemma_mul_mod_noop((x * r) as int, (r2 * r) as int, m as int);
    // (x r)(r2 r) = (x r r) r2
    assert((x * r) * (r2 * r) == (x * r * r) * r2) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right((x * r * r) as int, r2 as int, m as int);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right((x * r * r) as int, (rr * rr) as int, m as int);
    // (x r r)(R R) = x (R r)(R r)
    assert((x * r * r) * (rr * rr) == x * ((rr * r) * (rr * r))) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(t as int, t as int, m as int);
    assert(t * t % m == 1) by {
        assert((t % m) * (t % m) == 1);
        vstd::arithmetic::div_mod::lemma_small_mod(1nat, m);
    }
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(x as int, (t * t) as int, m as int);
    assert(x * ((t * t) % m) == x * 1);
}

/// The Montgomery form of `x` stands for `x`: `(x R mod m) r ≡ x`.
pub proof fn lemma_mont_inv(m: nat, rr: nat, r: nat, x: nat)
    requires
        m > 0,
        rr * r % m == 1,
    ensures
        (x * rr % m) * r % m == x % m,
{
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left((x * rr) as int, r as int, m as int);
    assert((x * rr) * r == x * (rr * r)) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(x as int, (rr * r) as int, m as int);
    assert(x * ((rr * r) % m) == x * 1);
}

/// `mont(x)` stands for `x`: for `x < m`, `from_montgomery` of any limbs of
/// value `mont(x)` is `x`.
pub proof fn lemma_mont_roundtrip(w: Which, z: Seq<u64>, x: nat)
    requires
        x < modulus(w),
        value(z) == mont(w, x),
    ensures
        from_montgomery(w, z) == x,
{
    lemma_modulus(w);
    lemma_rinv(w);
    lemma_from_montgomery(w, z);
    lemma_mont_inv(modulus(w), radix(), rinv(w), x);
    vstd::arithmetic::div_mod::lemma_small_mod(x, modulus(w));
}

// ---------------------------------------------------------------------
// Limb sequences.
// ---------------------------------------------------------------------

/// A sequence of `n` limbs is below `base^n`.
pub proof fn lemma_value_bound(s: Seq<u64>)
    ensures
        value(s) < limb_pow(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_value_bound(d);
        let p = limb_pow(d.len());
        let l = s.last() as nat;
        assert(limb_pow(s.len()) == p * base());
        assert(value(s) == value(d) + l * p);
        assert(value(s) < p * base()) by (nonlinear_arith)
            requires
                value(d) < p,
                l < base(),
                value(s) == value(d) + l * p,
        ;
    }
}

/// `limb_pow` is positive.
pub proof fn lemma_limb_pow_pos(i: nat)
    ensures
        limb_pow(i) > 0,
    decreases i,
{
    if i > 0 {
        lemma_limb_pow_pos((i - 1) as nat);
        assert(limb_pow((i - 1) as nat) * base() > 0) by (nonlinear_arith)
            requires
                limb_pow((i - 1) as nat) > 0,
                base() > 0,
        ;
    }
}

/// Six limbs, written out: the sum fiat's header calls `eval`.
pub proof fn lemma_value6(s: Seq<u64>)
    requires
        s.len() == 6,
    ensures
        value(s) == s[0] + s[1] * 0x1_0000_0000_0000_0000nat + s[2] * 0x1_0000_0000_0000_0000_0000_0000_0000_0000nat + s[3] * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat + s[4] * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat + s[5] * 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000nat,
        value(s) < radix(),
{
    lemma_limb_pow_consts();
    lemma_value_bound(s);
    let s5 = s.drop_last();
    let s4 = s5.drop_last();
    let s3 = s4.drop_last();
    let s2 = s3.drop_last();
    let s1 = s2.drop_last();
    let s0 = s1.drop_last();
    assert(s5.len() == 5 && s4.len() == 4 && s3.len() == 3 && s2.len() == 2 && s1.len() == 1
        && s0.len() == 0);
    assert(s.last() == s[5] && s5.last() == s[4] && s4.last() == s[3] && s3.last() == s[2]
        && s2.last() == s[1] && s1.last() == s[0]);
    assert(value(s) == value(s5) + s[5] * limb_pow(5));
    assert(value(s5) == value(s4) + s[4] * limb_pow(4));
    assert(value(s4) == value(s3) + s[3] * limb_pow(3));
    assert(value(s3) == value(s2) + s[2] * limb_pow(2));
    assert(value(s2) == value(s1) + s[1] * limb_pow(1));
    assert(value(s1) == value(s0) + s[0] * limb_pow(0));
    assert(value(s0) == 0);
}

/// One limb and the rest: `v1 + l1 p = v2 + l2 p` with `v1, v2 < p` gives
/// `l1 = l2` and `v1 = v2`.
proof fn lemma_digit_split(p: nat, v1: nat, l1: nat, v2: nat, l2: nat)
    requires
        p > 0,
        v1 < p,
        v2 < p,
        v1 + l1 * p == v2 + l2 * p,
    ensures
        l1 == l2,
        v1 == v2,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (v1 + l1 * p) as int,
        p as int,
        l1 as int,
        v1 as int,
    );
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (v2 + l2 * p) as int,
        p as int,
        l2 as int,
        v2 as int,
    );
}

/// Limb sequences of one length with one value are one sequence.
pub proof fn lemma_value_inj(a: Seq<u64>, b: Seq<u64>)
    requires
        a.len() == b.len(),
        value(a) == value(b),
    ensures
        a =~= b,
    decreases a.len(),
{
    if a.len() > 0 {
        let da = a.drop_last();
        let db = b.drop_last();
        lemma_value_bound(da);
        lemma_value_bound(db);
        lemma_limb_pow_pos(da.len());
        lemma_digit_split(
            limb_pow(da.len()),
            value(da),
            a.last() as nat,
            value(db),
            b.last() as nat,
        );
        lemma_value_inj(da, db);
        assert(a =~= da.push(a.last()));
        assert(b =~= db.push(b.last()));
    }
}

// ---------------------------------------------------------------------
// Octet strings.
// ---------------------------------------------------------------------

/// `256^n`.
pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        pow256((n - 1) as nat) * 256
    }
}

/// Appending an octet is Horner's step.
pub proof fn lemma_os2ip_push(s: Seq<u8>, b: u8)
    ensures
        crate::spec::os2ip(s.push(b)) == crate::spec::os2ip(s) * 256 + b as nat,
{
    assert(s.push(b).drop_last() =~= s);
}

/// An octet string of `n` octets is below `256^n`.
pub proof fn lemma_os2ip_bound(s: Seq<u8>)
    ensures
        crate::spec::os2ip(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_os2ip_bound(d);
        let p = pow256(d.len());
        let x = crate::spec::os2ip(d);
        let l = s.last() as nat;
        assert(crate::spec::os2ip(s) == x * 256 + l);
        assert(pow256(s.len()) == p * 256);
        assert(x * 256 + l < p * 256) by (nonlinear_arith)
            requires
                x < p,
                l < 256,
        ;
    }
}

/// `256^8` is the limb radix.
pub proof fn lemma_pow256_8()
    ensures
        pow256(8) == base(),
{
    reveal_with_fuel(pow256, 9);
}

/// `256^i <= 256^j` for `i <= j`.
pub proof fn lemma_pow256_mono(i: nat, j: nat)
    requires
        i <= j,
    ensures
        pow256(i) <= pow256(j),
    decreases j,
{
    if i < j {
        lemma_pow256_mono(i, (j - 1) as nat);
    }
}

/// Concatenation: `os2ip(a || b) = os2ip(a) 256^|b| + os2ip(b)`.
pub proof fn lemma_os2ip_concat(a: Seq<u8>, b: Seq<u8>)
    ensures
        crate::spec::os2ip(a + b) == crate::spec::os2ip(a) * pow256(b.len()) + crate::spec::os2ip(
            b,
        ),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(pow256(0) == 1);
        assert(crate::spec::os2ip(b) == 0);
        assert(crate::spec::os2ip(a) * 1 == crate::spec::os2ip(a));
    } else {
        let bd = b.drop_last();
        lemma_os2ip_concat(a, bd);
        assert((a + b).drop_last() =~= a + bd);
        assert((a + b).last() == b.last());
        let x = crate::spec::os2ip(a);
        let y = crate::spec::os2ip(bd);
        let p = pow256(bd.len());
        let l = b.last() as nat;
        assert(pow256(b.len()) == p * 256);
        assert(crate::spec::os2ip(a + b) == crate::spec::os2ip(a + bd) * 256 + l);
        assert(crate::spec::os2ip(b) == y * 256 + l);
        assert(crate::spec::os2ip(a + bd) == x * p + y);
        assert(crate::spec::os2ip(a + b) == (x * p + y) * 256 + l);
        assert((x * p + y) * 256 + l == x * (p * 256) + (y * 256 + l)) by (nonlinear_arith);
        assert(crate::spec::os2ip(a) * pow256(b.len()) == x * (p * 256));
    }
}

/// Forty-eight octets as six chunks of eight, each chunk a limb's worth
/// (Horner's rule with radix `2^64`).
pub proof fn lemma_os2ip_chunks(s: Seq<u8>)
    requires
        s.len() == 48,
    ensures
        crate::spec::os2ip(s) == (((((crate::spec::os2ip(s.subrange(0, 8)) * 0x1_0000_0000_0000_0000nat
            + crate::spec::os2ip(s.subrange(8, 16))) * 0x1_0000_0000_0000_0000nat + crate::spec::os2ip(
            s.subrange(16, 24),
        )) * 0x1_0000_0000_0000_0000nat + crate::spec::os2ip(s.subrange(24, 32))) * 0x1_0000_0000_0000_0000nat + crate::spec::os2ip(
            s.subrange(32, 40),
        )) * 0x1_0000_0000_0000_0000nat + crate::spec::os2ip(s.subrange(40, 48))),
{
    lemma_pow256_8();
    let c0 = s.subrange(0, 8);
    let c1 = s.subrange(8, 16);
    let c2 = s.subrange(16, 24);
    let c3 = s.subrange(24, 32);
    let c4 = s.subrange(32, 40);
    let c5 = s.subrange(40, 48);
    let s2 = c0 + c1;
    let s3 = s2 + c2;
    let s4 = s3 + c3;
    let s5 = s4 + c4;
    assert(s5 + c5 =~= s);
    lemma_os2ip_concat(s5, c5);
    lemma_os2ip_concat(s4, c4);
    lemma_os2ip_concat(s3, c3);
    lemma_os2ip_concat(s2, c2);
    lemma_os2ip_concat(c0, c1);
}

/// The first `k + 1` octets are the first `k` and octet `k`.
pub proof fn lemma_os2ip_take(s: Seq<u8>, k: int)
    requires
        0 <= k < s.len(),
    ensures
        crate::spec::os2ip(s.take(k + 1)) == crate::spec::os2ip(s.take(k)) * 256 + s[k] as nat,
{
    lemma_os2ip_push(s.take(k), s[k]);
    assert(s.take(k + 1) =~= s.take(k).push(s[k]));
}

/// Eight octets, written out (Horner's rule with radix 256).
pub proof fn lemma_os2ip8(s: Seq<u8>)
    requires
        s.len() == 8,
    ensures
        crate::spec::os2ip(s) == ((((((s[0] as nat * 256 + s[1] as nat) * 256 + s[2] as nat) * 256
            + s[3] as nat) * 256 + s[4] as nat) * 256 + s[5] as nat) * 256 + s[6] as nat) * 256
            + s[7] as nat,
{
    lemma_os2ip_take(s, 0);
    lemma_os2ip_take(s, 1);
    lemma_os2ip_take(s, 2);
    lemma_os2ip_take(s, 3);
    lemma_os2ip_take(s, 4);
    lemma_os2ip_take(s, 5);
    lemma_os2ip_take(s, 6);
    lemma_os2ip_take(s, 7);
    assert(s.take(0) =~= Seq::<u8>::empty());
    assert(s.take(8) =~= s);
}

/// Seven octets are below `2^56`, so a limb built from them can take
/// another octet.
pub proof fn lemma_os2ip_below_2_56(s: Seq<u8>)
    requires
        s.len() <= 7,
    ensures
        crate::spec::os2ip(s) * 256 + 255 < 0x1_0000_0000_0000_0000nat,
{
    lemma_os2ip_bound(s);
    lemma_pow256_mono(s.len(), 7);
    reveal_with_fuel(pow256, 8);
    assert(pow256(7) == 0x100_0000_0000_0000nat);
}

/// For `Which::P`, `from_octets_ensures` is SEC 1 §2.3.6 (`os2fe`).
pub proof fn lemma_from_octets_os2fe(o: Seq<u8>, r: Option<nat>)
    requires
        super::contract::from_octets_ensures(Which::P, o, r),
    ensures
        r == crate::spec::os2fe(crate::spec::p384(), o),
{
}

// ---------------------------------------------------------------------
// The spec's residue arithmetic.
// ---------------------------------------------------------------------

/// Fiat's `(x - y) mod m` (mathematical modulus) is the spec's `fe_sub`.
pub proof fn lemma_fe_sub(m: nat, x: nat, y: nat)
    requires
        m > 0,
        x < m,
        y < m,
    ensures
        (x as int - y as int) % (m as int) == crate::spec::fe_sub(m, x, y) as int,
{
    vstd::arithmetic::div_mod::lemma_small_mod(x, m);
    vstd::arithmetic::div_mod::lemma_small_mod(y, m);
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(x as int - y as int, m as int);
    assert((m as int + (x as int - y as int)) == (x % m + m - y % m) as int);
}

/// One bit of square-and-multiply: `pow_mod(a, 2q + bit) = pow_mod(a, q)^2`
/// times `a` if the bit is set.
pub proof fn lemma_pow_mod_step(a: nat, q: nat, bit: bool, m: nat)
    requires
        m > 1,
    ensures
        crate::spec::pow_mod(a, 2 * q + (if bit { 1nat } else { 0nat }), m) == (if bit {
            (crate::spec::pow_mod(a, q, m) * crate::spec::pow_mod(a, q, m) % m) * (a % m) % m
        } else {
            crate::spec::pow_mod(a, q, m) * crate::spec::pow_mod(a, q, m) % m
        }),
{
    let e = 2 * q + (if bit { 1nat } else { 0nat });
    let h = crate::spec::pow_mod(a, q, m);
    if e == 0 {
        // q = 0 and the bit is clear: pow_mod(a, 0) = 1 % m, and 1 % m
        // squared is 1 % m.
        assert(q == 0 && !bit);
        assert(crate::spec::pow_mod(a, 0, m) == 1nat % m);
        vstd::arithmetic::div_mod::lemma_small_mod(1nat, m);
        assert(h == 1);
        assert(crate::spec::pow_mod(a, e, m) == 1nat % m);
        assert(h * h == 1) by (nonlinear_arith)
            requires
                h == 1,
        ;
        assert(h * h % m == 1);
    } else {
        assert(e / 2 == q);
        assert(e % 2 == (if bit { 1nat } else { 0nat }));
        assert(crate::spec::pow_mod(a, e, m) == (if e % 2 == 0 {
            h * h % m
        } else {
            (h * h % m) * (a % m) % m
        }));
    }
}

// ---------------------------------------------------------------------
// The exponent of Fermat's inverse.
// ---------------------------------------------------------------------

/// The octets of `m - 2`, big-endian, for the exponent of the inverse.
pub open spec fn exponent_octets(w: Which) -> Seq<u8> {
    match w {
        Which::P => seq![0xffu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xfd],
        Which::N => seq![0xffu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37, 0x2d, 0xdf, 0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec, 0x19, 0x6a, 0xcc, 0xc5, 0x29, 0x71],
    }
}

/// `exponent_octets` is 48 octets and is `m - 2`.
pub proof fn lemma_exponent(w: Which)
    ensures
        exponent_octets(w).len() == 48,
        crate::spec::os2ip(exponent_octets(w)) == modulus(w) - 2,
{
    match w {
        Which::P => {
            assert(exponent_octets(Which::P).len() == 48 && crate::spec::os2ip(exponent_octets(Which::P))
                == modulus(Which::P) - 2) by (compute_only);
        },
        Which::N => {
            assert(exponent_octets(Which::N).len() == 48 && crate::spec::os2ip(exponent_octets(Which::N))
                == modulus(Which::N) - 2) by (compute_only);
        },
    }
}

} // verus!
