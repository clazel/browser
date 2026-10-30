//! [`crate::independent`] equals [`crate::spec`]: SEC 1 §4.1.4, transcribed
//! without reading `spec.rs`, accepts exactly the signatures that FIPS 186-5
//! §6.4.2 as `spec.rs` transcribes it accepts (docs/VERIFICATION.md, "Trust
//! without reviewers", item 2). The theorem is
//! [`lemma_independent_equals_spec`].
//!
//! The two texts share the conventions listed in `independent.rs`'s header.
//! What this file proves equal is everything else:
//! - the arithmetic: `inv` by square-and-multiply with reductions against
//!   `inv` by an unreduced power, and `fe_sub` against `fmod`;
//! - SEC 1 §2.3: octet strings read first-octet-first against
//!   last-octet-first, and the octet length of a field element given against
//!   computed;
//! - step 3: bit-string truncation through SEC 1 §2.3.2, §2.3.1 and §2.3.8
//!   against FIPS 186-5 B.2.1;
//! - the group law, whose rule 3 the two texts read differently: `spec.rs`
//!   as `y1 + y2 ≡ 0`, `independent.rs` as SEC 1's words, "either distinct or
//!   have y-coordinate 0". For two points on the curve with the same x,
//!   `y1^2 ≡ y2^2`; that makes the two tests agree only if p is prime
//!   (Euclid's lemma, [`euclid`]), and only for points on the curve. So the
//!   proof also shows that every point the verification adds is on the curve
//!   ([`good`]): SEC 1 §2.2.1's closure, proven here for the chord and the
//!   tangent from the curve equation alone.
//! - O as an enum against an enum, and a step-indexed `Result` against a
//!   `bool`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Modular arithmetic.
// ---------------------------------------------------------------------

/// `independent::power` is vstd's `pow`.
pub proof fn lemma_power_is_pow(b: nat, e: nat)
    ensures
        crate::independent::power(b, e) == vstd::arithmetic::power::pow(b as int, e),
    decreases e,
{
    reveal(vstd::arithmetic::power::pow);
    if e > 0 {
        lemma_power_is_pow(b, (e - 1) as nat);
    }
}

/// Square-and-multiply with reductions is the power, reduced.
pub proof fn lemma_pow_mod_is_power(a: nat, e: nat, m: nat)
    requires
        m > 0,
    ensures
        pow_mod(a, e, m) == crate::independent::power(a, e) % m,
    decreases e,
{
    lemma_power_is_pow(a, e);
    if e > 0 {
        let h = e / 2;
        lemma_pow_mod_is_power(a, h, m);
        lemma_power_is_pow(a, h);
        let ph = vstd::arithmetic::power::pow(a as int, h);
        vstd::arithmetic::power::lemma_pow_adds(a as int, h, h);
        vstd::arithmetic::div_mod::lemma_mul_mod_noop(ph, ph, m as int);
        if e % 2 == 1 {
            vstd::arithmetic::power::lemma_pow_adds(a as int, h + h, 1);
            vstd::arithmetic::power::lemma_pow1(a as int);
            vstd::arithmetic::div_mod::lemma_mul_mod_noop(ph * ph, a as int, m as int);
            vstd::arithmetic::div_mod::lemma_mod_twice(ph * ph, m as int);
        }
    }
}

/// The two `inv`s are the same function.
pub proof fn lemma_inv(m: nat, a: nat)
    requires
        m > 0,
    ensures
        inv(m, a) == crate::independent::inv(m, a),
{
    let e = (m - 2) as nat;
    lemma_pow_mod_is_power(a, e, m);
    let pw = crate::independent::power(a, e);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(a as int, pw as int, m as int);
}

/// `fe_sub` is `fmod` of the difference.
pub proof fn lemma_fe_sub(m: nat, x: nat, y: nat)
    requires
        m > 0,
    ensures
        fe_sub(m, x, y) == crate::independent::fmod(x - y, m),
        fe_sub(m, x, y) == (x - y) % (m as int),
        fe_sub(m, x, y) < m,
{
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(x as int, y as int, m as int);
    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish((x % m) - (y % m), m as int);
    vstd::arithmetic::div_mod::lemma_mod_bound(x - y, m as int);
}

// ---------------------------------------------------------------------
// SEC 1 §2.3: octet strings, field elements, points.
// ---------------------------------------------------------------------

/// SEC 1 §2.3.8 peeling the first octet ([`crate::independent::octets_to_integer`])
/// is the same sum as peeling the last ([`os2ip`]).
pub proof fn lemma_os2ip_first(s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        os2ip(s) == (s[0] as nat) * crate::independent::power(256, (s.len() - 1) as nat) + os2ip(
            s.skip(1),
        ),
    decreases s.len(),
{
    let x0 = s[0] as nat;
    let big = crate::independent::power(256, (s.len() - 1) as nat);
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        assert(s.skip(1) =~= Seq::<u8>::empty());
        assert(os2ip(Seq::<u8>::empty()) == 0);
        assert(big == 1);
        assert(os2ip(s) == os2ip(s.drop_last()) * 256 + s.last() as nat);
        assert(os2ip(s) == x0);
        vstd::arithmetic::mul::lemma_mul_basics(x0 as int);
        assert(x0 * big == x0);
    } else {
        let d = s.drop_last();
        lemma_os2ip_first(d);
        assert(d.skip(1) =~= s.skip(1).drop_last());
        assert(s.skip(1).last() == s.last());
        let pw = crate::independent::power(256, (s.len() - 2) as nat);
        assert((d.len() - 1) as nat == (s.len() - 2) as nat);
        assert(big == 256 * pw);
        assert(d[0] == s[0]);
        let o1 = os2ip(d.skip(1));
        let l = s.last() as nat;
        assert(os2ip(d) == x0 * pw + o1);
        assert(os2ip(s) == os2ip(d) * 256 + l);
        assert(os2ip(s.skip(1)) == o1 * 256 + l);
        assert((x0 * pw + o1) * 256 + l == x0 * (256 * pw) + (o1 * 256 + l)) by (nonlinear_arith);
        assert(x0 * big == x0 * (256 * pw)) by (nonlinear_arith)
            requires
                big == 256 * pw,
        ;
    }
}

/// [`crate::independent::octets_to_integer`] is [`os2ip`].
pub proof fn lemma_octets_to_integer(s: Seq<u8>)
    ensures
        crate::independent::octets_to_integer(s) == os2ip(s),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_octets_to_integer(s.skip(1));
        lemma_os2ip_first(s);
    }
}

/// An independent point as a `spec` point.
pub open spec fn pt(q: crate::independent::EcPoint) -> Point {
    match q {
        crate::independent::EcPoint::O => Point::Infinity,
        crate::independent::EcPoint::Aff { x, y } => Point::Affine { x, y },
    }
}

/// [`pt`] under an `Option`.
pub open spec fn opt_pt(o: Option<crate::independent::EcPoint>) -> Option<Point> {
    match o {
        None => None,
        Some(q) => Some(pt(q)),
    }
}

/// The two curve records hold the same domain parameters: the six numbers
/// are equal, and `spec`'s stored octet length is `independent`'s computed
/// one.
pub open spec fn corresponds(c: Curve, d: crate::independent::Curve) -> bool {
    c.p == d.p && c.a == d.a && c.b == d.b && c.gx == d.gx && c.gy == d.gy && c.n == d.n
        && c.octets == crate::independent::field_octets(d)
}

/// The public key, decoded and validated, is the same point or the same
/// rejection.
pub proof fn lemma_decode_public_key(c: Curve, d: crate::independent::Curve, q: Seq<u8>)
    requires
        corresponds(c, d),
        c.p > 0,
    ensures
        decode_public_key(c, q) == opt_pt(crate::independent::decode_public_key(d, q)),
{
    let mlen = c.octets;
    if q.len() == 2 * mlen + 1 && !(q.len() == 1 && q[0] == 0x00u8) && q.len() != mlen + 1 {
        let xs = q.subrange(1, 1 + mlen as int);
        let ys = q.subrange(1 + mlen as int, 1 + 2 * mlen as int);
        lemma_octets_to_integer(xs);
        lemma_octets_to_integer(ys);
    }
}

// ---------------------------------------------------------------------
// FIPS 186-5 step 3, SEC 1 §4.1.4 step 3.
// ---------------------------------------------------------------------

/// `two_to` and `power(2, _)` agree on the eight shifts of an octet.
proof fn lemma_two_to_is_power(k: nat)
    requires
        k < 8,
    ensures
        two_to(k) == crate::independent::power(2, k),
{
    assert(two_to(0) == crate::independent::power(2, 0) && two_to(1) == crate::independent::power(
        2,
        1,
    ) && two_to(2) == crate::independent::power(2, 2) && two_to(3) == crate::independent::power(2, 3)
        && two_to(4) == crate::independent::power(2, 4) && two_to(5) == crate::independent::power(
        2,
        5,
    ) && two_to(6) == crate::independent::power(2, 6) && two_to(7) == crate::independent::power(
        2,
        7,
    )) by (compute_only);
}

/// SEC 1 §2.3.2, transcribed twice, is one function.
proof fn lemma_octets_to_bits(h: Seq<u8>)
    ensures
        octets_to_bits(h) == crate::independent::octets_to_bits(h),
{
    assert forall|i: int| 0 <= i < 8 * h.len() implies #[trigger] octets_to_bits(h)[i]
        == crate::independent::octets_to_bits(h)[i] by {
        lemma_two_to_is_power((7 - i % 8) as nat);
    }
    assert(octets_to_bits(h) =~= crate::independent::octets_to_bits(h));
}

/// `bits_value` is `bits_to_int`.
proof fn lemma_bits_value(b: Seq<bool>)
    ensures
        crate::independent::bits_value(b) == bits_to_int(b),
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_bits_value(b.drop_last());
    }
}

/// A bit string's value is below `2^len`.
proof fn lemma_bits_value_bound(b: Seq<bool>)
    ensures
        crate::independent::bits_value(b) < crate::independent::power(2, b.len()),
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_bits_value_bound(b.drop_last());
    }
}

/// The value of a concatenation: the left part shifted, plus the right.
proof fn lemma_bits_value_concat(a: Seq<bool>, b: Seq<bool>)
    ensures
        crate::independent::bits_value(a + b) == crate::independent::bits_value(a)
            * crate::independent::power(2, b.len()) + crate::independent::bits_value(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        let va = crate::independent::bits_value(a);
        assert(crate::independent::power(2, b.len()) == 1);
        assert(crate::independent::bits_value(b) == 0);
        vstd::arithmetic::mul::lemma_mul_basics(va as int);
        assert(va * crate::independent::power(2, b.len()) == va);
    } else {
        let b1 = b.drop_last();
        lemma_bits_value_concat(a, b1);
        assert((a + b).drop_last() =~= a + b1);
        assert((a + b).last() == b.last());
        let va = crate::independent::bits_value(a);
        let vb1 = crate::independent::bits_value(b1);
        let pw = crate::independent::power(2, b1.len());
        let bit: nat = if b.last() {
            1
        } else {
            0
        };
        assert(crate::independent::bits_value(a + b) == 2 * crate::independent::bits_value(a + b1)
            + bit);
        assert(crate::independent::bits_value(b) == 2 * vb1 + bit);
        assert(crate::independent::power(2, b.len()) == 2 * pw);
        assert(2 * (va * pw + vb1) + bit == va * (2 * pw) + (2 * vb1 + bit)) by (nonlinear_arith);
        let pb = crate::independent::power(2, b.len());
        assert(va * pb == va * (2 * pw)) by (nonlinear_arith)
            requires
                pb == 2 * pw,
        ;
        assert(crate::independent::bits_value(a + b1) == va * pw + vb1);
        assert(crate::independent::bits_value(a + b) == va * pb + crate::independent::bits_value(b));
    }
}

/// Leading zero bits add nothing.
proof fn lemma_bits_value_zeros(k: nat)
    ensures
        crate::independent::bits_value(Seq::new(k, |i: int| false)) == 0,
    decreases k,
{
    if k > 0 {
        lemma_bits_value_zeros((k - 1) as nat);
        assert(Seq::new(k, |i: int| false).drop_last() =~= Seq::new((k - 1) as nat, |i: int| false));
    }
}

/// The octets cut from a bit string whose length is a multiple of 8.
pub open spec fn cut_octets(b: Seq<bool>, mlen: nat) -> Seq<u8> {
    Seq::new(
        mlen,
        |i: int| (crate::independent::bits_value(b.subrange(8 * i, 8 * i + 8)) % 256) as u8,
    )
}

/// Cutting a bit string of `8 mlen` bits into octets and reading those as an
/// integer gives its value.
proof fn lemma_cut_octets(b: Seq<bool>, mlen: nat)
    requires
        b.len() == 8 * mlen,
    ensures
        os2ip(cut_octets(b, mlen)) == crate::independent::bits_value(b),
    decreases mlen,
{
    if mlen == 0 {
        assert(b =~= Seq::<bool>::empty());
        assert(cut_octets(b, mlen) =~= Seq::<u8>::empty());
    } else {
        let m1 = (mlen - 1) as nat;
        let front = b.subrange(0, 8 * m1 as int);
        let back = b.subrange(8 * m1 as int, 8 * mlen as int);
        lemma_cut_octets(front, m1);
        assert(cut_octets(b, mlen).drop_last() =~= cut_octets(front, m1)) by {
            assert forall|i: int| 0 <= i < m1 implies #[trigger] front.subrange(8 * i, 8 * i + 8)
                =~= b.subrange(8 * i, 8 * i + 8) by {}
        }
        assert(front + back =~= b);
        lemma_bits_value_concat(front, back);
        lemma_bits_value_bound(back);
        assert(crate::independent::power(2, 8) == 256) by (compute_only);
        let vb = crate::independent::bits_value(back);
        assert(cut_octets(b, mlen).last() == (vb % 256) as u8);
        vstd::arithmetic::div_mod::lemma_small_mod(vb, 256);
    }
}

/// SEC 1 §2.3.1 then §2.3.8 is FIPS 186-5 B.2.1: converting a bit string to
/// octets (padded on the left) and those to an integer gives the integer of
/// the bits.
pub proof fn lemma_bits_to_octets_to_integer(b: Seq<bool>)
    ensures
        crate::independent::octets_to_integer(crate::independent::bits_to_octets(b))
            == bits_to_int(b),
{
    let blen = b.len();
    let mlen = (blen + 7) / 8;
    let zeros = Seq::new((8 * mlen - blen) as nat, |i: int| false);
    let padded = zeros + b;
    assert(crate::independent::bits_to_octets(b) =~= cut_octets(padded, mlen));
    lemma_cut_octets(padded, mlen);
    lemma_octets_to_integer(crate::independent::bits_to_octets(b));
    lemma_bits_value_concat(zeros, b);
    lemma_bits_value_zeros((8 * mlen - blen) as nat);
    lemma_bits_value(b);
}

/// Step 3 gives the same integer e.
pub proof fn lemma_derive_e_equal(c: Curve, d: crate::independent::Curve, h: Seq<u8>)
    requires
        c.n == d.n,
    ensures
        derive_e(c, h) == crate::independent::derive_e(d, h),
{
    lemma_octets_to_bits(h);
    let hbits = octets_to_bits(h);
    let l = ceil_log2(c.n);
    assert(l == crate::independent::ceil_log2(d.n)) by {
        lemma_ceil_log2(c.n);
    }
    if l < 8 * h.len() {
        assert(hbits.take(l as int) =~= hbits.subrange(0, l as int));
        lemma_bits_to_octets_to_integer(hbits.subrange(0, l as int));
    } else {
        lemma_bits_to_octets_to_integer(hbits);
    }
}

/// The two `ceil_log2`s are one function.
proof fn lemma_ceil_log2(x: nat)
    ensures
        ceil_log2(x) == crate::independent::ceil_log2(x),
    decreases x,
{
    if x > 1 {
        lemma_ceil_log2((x + 1) / 2);
    }
}

// ---------------------------------------------------------------------
// Congruences modulo p.
// ---------------------------------------------------------------------

/// `u ≡ v (mod p)`.
pub open spec fn cong(p: int, u: int, v: int) -> bool {
    u % p == v % p
}

/// Reducing is congruent, and lands in [0, p).
proof fn lemma_cong_mod(p: int, u: int)
    requires
        p > 0,
    ensures
        cong(p, u % p, u),
        0 <= u % p < p,
{
    vstd::arithmetic::div_mod::lemma_mod_twice(u, p);
    vstd::arithmetic::div_mod::lemma_mod_bound(u, p);
}

/// Sums and differences of congruent terms are congruent.
proof fn lemma_cong_add(p: int, u1: int, v1: int, u2: int, v2: int)
    requires
        p > 0,
        cong(p, u1, v1),
        cong(p, u2, v2),
    ensures
        cong(p, u1 + u2, v1 + v2),
        cong(p, u1 - u2, v1 - v2),
{
    vstd::arithmetic::div_mod::lemma_add_mod_noop(u1, u2, p);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(v1, v2, p);
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(u1, u2, p);
    vstd::arithmetic::div_mod::lemma_sub_mod_noop(v1, v2, p);
}

/// Products of congruent terms are congruent.
proof fn lemma_cong_mul(p: int, u1: int, v1: int, u2: int, v2: int)
    requires
        p > 0,
        cong(p, u1, v1),
        cong(p, u2, v2),
    ensures
        cong(p, u1 * u2, v1 * v2),
{
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(u1, u2, p);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(v1, v2, p);
}

/// A term congruent to 0, times anything, is congruent to 0.
proof fn lemma_cong_zero_mul(p: int, u: int, v: int)
    requires
        p > 0,
        cong(p, u, 0),
    ensures
        cong(p, u * v, 0),
        cong(p, v * u, 0),
{
    lemma_cong_mul(p, u, 0, v, v);
    lemma_cong_mul(p, v, v, u, 0);
}

/// Two residues in [0, p) that are congruent are equal.
proof fn lemma_cong_reduced(p: int, u: int, v: int)
    requires
        p > 0,
        0 <= u < p,
        0 <= v < p,
        cong(p, u, v),
    ensures
        u == v,
{
    vstd::arithmetic::div_mod::lemma_small_mod(u as nat, p as nat);
    vstd::arithmetic::div_mod::lemma_small_mod(v as nat, p as nat);
}

/// `fe_sub` is congruent to the difference, and reduced.
proof fn lemma_cong_fe_sub(m: nat, x: nat, y: nat)
    requires
        m > 0,
    ensures
        cong(m as int, fe_sub(m, x, y) as int, x - y),
        fe_sub(m, x, y) < m,
{
    lemma_fe_sub(m, x, y);
    lemma_cong_mod(m as int, x - y);
}

// ---------------------------------------------------------------------
// Small ring identities, each its own query.
// ---------------------------------------------------------------------

proof fn lemma_cube_diff(x: int, z: int)
    ensures
        x * x * x - z * z * z == (x - z) * (x * x + x * z + z * z),
{
    assert(x * x * x - z * z * z == (x - z) * (x * x + x * z + z * z)) by (nonlinear_arith);
}

proof fn lemma_line_sq(l: int, u: int, y: int)
    ensures
        (l * u + y) * (l * u + y) - y * y == u * (l * l * u + 2 * l * y),
{
    assert((l * u + y) * (l * u + y) - y * y == u * (l * l * u + 2 * l * y)) by (nonlinear_arith);
}

proof fn lemma_lin_diff(a: int, x: int, z: int)
    ensures
        a * x - a * z == (x - z) * a,
{
    assert(a * x - a * z == (x - z) * a) by (nonlinear_arith);
}

proof fn lemma_factor3(u: int, s1: int, s2: int, s3: int)
    ensures
        u * s1 + u * s2 - u * s3 == u * (s1 + s2 - s3),
{
    assert(u * s1 + u * s2 - u * s3 == u * (s1 + s2 - s3)) by (nonlinear_arith);
}

proof fn lemma_mul_zero(a: int, b: int)
    requires
        b == 0,
    ensures
        a * b == 0,
{
}

proof fn lemma_assoc_swap(a: int, b: int, c: int)
    ensures
        (a * b) * c == a * (c * b),
        (c * b) * a == b * (c * a),
{
    assert((a * b) * c == a * (c * b)) by (nonlinear_arith);
    assert((c * b) * a == b * (c * a)) by (nonlinear_arith);
}

proof fn lemma_neg_line(lam: int, x1: int, x3: int, y1: int)
    ensures
        lam * (x1 - x3) - y1 == -(lam * (x3 - x1) + y1),
{
    assert(lam * (x1 - x3) == -(lam * (x3 - x1))) by (nonlinear_arith);
}

proof fn lemma_neg_sq(y: int)
    ensures
        (-y) * (-y) == y * y,
{
    assert((-y) * (-y) == y * y) by (nonlinear_arith);
}

proof fn lemma_three(x: int)
    ensures
        3 * x * x == x * x + x * x + x * x,
{
    assert(3 * x * x == x * x + x * x + x * x) by (nonlinear_arith);
}

proof fn lemma_two_lam_y(lam: int, y1: int, t: int, w: int)
    ensures
        2 * lam * y1 == lam * (2 * y1),
        (t * w) * (2 * y1) == t * (2 * y1 * w),
{
    assert(2 * lam * y1 == lam * (2 * y1)) by (nonlinear_arith);
    assert((t * w) * (2 * y1) == t * (2 * y1 * w)) by (nonlinear_arith);
}

// ---------------------------------------------------------------------
// SEC 1 §2.2.1: the chord and the tangent stay on the curve.
// ---------------------------------------------------------------------

/// `y^2 - (x^3 + a x + b)`: zero modulo p exactly on the curve.
pub open spec fn ce(a: int, b: int, x: int, y: int) -> int {
    y * y - (x * x * x + a * x + b)
}

/// `x^2 + x x1 + x1^2 + a - lam^2 (x - x1) - 2 lam y1`: the curve minus the
/// line of slope `lam` through `(x1, y1)`, divided by `x - x1`
/// ([`lemma_ce_line`]).
pub open spec fn g_line(a: int, lam: int, x1: int, y1: int, x: int) -> int {
    x * x + x * x1 + x1 * x1 + a - lam * lam * (x - x1) - 2 * lam * y1
}

/// The curve polynomial at the point of the line of slope `lam` through
/// `(x1, y1)` above `x`: its value at `(x1, y1)` less `(x - x1) g(x)`.
proof fn lemma_ce_line(a: int, b: int, lam: int, x1: int, y1: int, x: int)
    ensures
        ce(a, b, x, lam * (x - x1) + y1) == ce(a, b, x1, y1) - (x - x1) * g_line(a, lam, x1, y1, x),
{
    let u = x - x1;
    lemma_line_sq(lam, u, y1);
    lemma_cube_diff(x, x1);
    lemma_lin_diff(a, x, x1);
    lemma_factor3(u, x * x + x * x1 + x1 * x1, a, lam * lam * u + 2 * lam * y1);
}

/// `g(x) - g(z) = (x - z)(x + z + x1 - lam^2)`.
proof fn lemma_g_diff(a: int, lam: int, x1: int, y1: int, x: int, z: int)
    ensures
        g_line(a, lam, x1, y1, x) - g_line(a, lam, x1, y1, z) == (x - z) * (x + z + x1 - lam
            * lam),
{
    let l2 = lam * lam;
    assert(l2 * (x - x1) - l2 * (z - x1) == (x - z) * l2) by (nonlinear_arith);
    assert(x * x + x * x1 - (z * z + z * x1) == (x - z) * (x + z + x1)) by (nonlinear_arith);
    assert((x - z) * (x + z + x1) - (x - z) * l2 == (x - z) * (x + z + x1 - l2)) by (nonlinear_arith);
}

/// `ce` does not see the sign of y.
proof fn lemma_ce_neg(a: int, b: int, x: int, y: int)
    ensures
        ce(a, b, x, -y) == ce(a, b, x, y),
{
    lemma_neg_sq(y);
}

/// The curve polynomial respects congruence.
proof fn lemma_ce_cong(p: int, a: int, b: int, x: int, y: int, x2: int, y2: int)
    requires
        p > 0,
        cong(p, x, x2),
        cong(p, y, y2),
    ensures
        cong(p, ce(a, b, x, y), ce(a, b, x2, y2)),
{
    lemma_cong_mul(p, y, y2, y, y2);
    lemma_cong_mul(p, x, x2, x, x2);
    lemma_cong_mul(p, x * x, x2 * x2, x, x2);
    lemma_cong_mul(p, a, a, x, x2);
    lemma_cong_add(p, x * x * x, x2 * x2 * x2, a * x, a * x2);
    lemma_cong_add(p, x * x * x + a * x, x2 * x2 * x2 + a * x2, b, b);
    lemma_cong_add(p, y * y, y2 * y2, x * x * x + a * x + b, x2 * x2 * x2 + a * x2 + b);
}

/// SEC 1 §2.2.1 rule 4 (the chord) gives a point on the curve: if `(x1,
/// y1)` and `(x2, y2)` are on it, `w` is an inverse of `x2 - x1` and `lam ≡
/// (y2 - y1) w`, then `(lam^2 - x1 - x2, lam (x1 - x3) - y1)` is on it.
proof fn lemma_chord_on_curve(
    p: int,
    a: int,
    b: int,
    x1: int,
    y1: int,
    x2: int,
    y2: int,
    w: int,
    lam: int,
)
    requires
        p > 0,
        cong(p, ce(a, b, x1, y1), 0),
        cong(p, ce(a, b, x2, y2), 0),
        cong(p, (x2 - x1) * w, 1),
        cong(p, lam, (y2 - y1) * w),
    ensures
        ({
            let x3 = lam * lam - x1 - x2;
            cong(p, ce(a, b, x3, lam * (x1 - x3) - y1), 0)
        }),
{
    let x3 = lam * lam - x1 - x2;
    let v = x2 - x1;
    let e1 = ce(a, b, x1, y1);
    // The line meets x = x2 at y2 (mod p): lam v ≡ (y2 - y1) w v ≡ y2 - y1.
    lemma_cong_mul(p, lam, (y2 - y1) * w, v, v);
    lemma_assoc_swap(y2 - y1, w, v);
    lemma_cong_mul(p, y2 - y1, y2 - y1, v * w, 1);
    assert(cong(p, lam * v, y2 - y1));
    lemma_cong_add(p, lam * v, y2 - y1, y1, y1);
    assert(cong(p, lam * v + y1, y2));
    lemma_ce_cong(p, a, b, x2, lam * v + y1, x2, y2);
    // So v g(x2) ≡ 0, and g(x2) ≡ w v g(x2) ≡ 0.
    lemma_ce_line(a, b, lam, x1, y1, x2);
    let g2 = g_line(a, lam, x1, y1, x2);
    lemma_cong_add(p, e1, 0, ce(a, b, x2, lam * v + y1), 0);
    assert(cong(p, v * g2, 0));
    lemma_cong_zero_mul(p, v * g2, w);
    lemma_assoc_swap(g2, w, v);
    lemma_cong_mul(p, v * w, 1, g2, g2);
    assert(cong(p, g2, 0));
    // g(x3) = g(x2), since x3 + x2 + x1 = lam^2.
    lemma_g_diff(a, lam, x1, y1, x3, x2);
    lemma_mul_zero(x3 - x2, x3 + x2 + x1 - lam * lam);
    let g3 = g_line(a, lam, x1, y1, x3);
    assert(g3 == g2);
    // So the curve at (x3, -y3) is e1 - (x3 - x1) g3 ≡ 0.
    lemma_ce_line(a, b, lam, x1, y1, x3);
    lemma_cong_zero_mul(p, g3, x3 - x1);
    lemma_cong_add(p, e1, 0, (x3 - x1) * g3, 0);
    lemma_neg_line(lam, x1, x3, y1);
    lemma_ce_neg(a, b, x3, lam * (x3 - x1) + y1);
}

/// SEC 1 §2.2.1 rule 5 (the tangent) gives a point on the curve: if `(x1,
/// y1)` is on it, `w` is an inverse of `2 y1` and `lam ≡ (3 x1^2 + a) w`,
/// then `(lam^2 - 2 x1, lam (x1 - x3) - y1)` is on it.
proof fn lemma_tangent_on_curve(p: int, a: int, b: int, x1: int, y1: int, w: int, lam: int)
    requires
        p > 0,
        cong(p, ce(a, b, x1, y1), 0),
        cong(p, 2 * y1 * w, 1),
        cong(p, lam, (3 * x1 * x1 + a) * w),
    ensures
        ({
            let x3 = lam * lam - 2 * x1;
            cong(p, ce(a, b, x3, lam * (x1 - x3) - y1), 0)
        }),
{
    let x3 = lam * lam - 2 * x1;
    let e1 = ce(a, b, x1, y1);
    let t = 3 * x1 * x1 + a;
    // g(x1) = 3 x1^2 + a - 2 lam y1 ≡ 0, since 2 lam y1 ≡ t w 2 y1 ≡ t.
    lemma_mul_zero(lam * lam, x1 - x1);
    lemma_three(x1);
    let g1 = g_line(a, lam, x1, y1, x1);
    assert(g1 == t - 2 * lam * y1);
    lemma_two_lam_y(lam, y1, t, w);
    lemma_cong_mul(p, lam, t * w, 2 * y1, 2 * y1);
    lemma_cong_mul(p, t, t, 2 * y1 * w, 1);
    assert(cong(p, 2 * lam * y1, t));
    lemma_cong_add(p, t, t, 2 * lam * y1, t);
    assert(cong(p, g1, 0));
    // g(x3) = g(x1), since x3 + 2 x1 = lam^2.
    lemma_g_diff(a, lam, x1, y1, x3, x1);
    lemma_mul_zero(x3 - x1, x3 + x1 + x1 - lam * lam);
    let g3 = g_line(a, lam, x1, y1, x3);
    assert(g3 == g1);
    lemma_ce_line(a, b, lam, x1, y1, x3);
    lemma_cong_zero_mul(p, g3, x3 - x1);
    lemma_cong_add(p, e1, 0, (x3 - x1) * g3, 0);
    lemma_neg_line(lam, x1, x3, y1);
    lemma_ce_neg(a, b, x3, lam * (x3 - x1) + y1);
}

/// On the curve, as a congruence.
proof fn lemma_on_curve_cong(c: Curve, x: nat, y: nat)
    requires
        c.p > 0,
    ensures
        satisfies_equation(c, x, y) == cong(
            c.p as int,
            ce(c.a as int, c.b as int, x as int, y as int),
            0,
        ),
{
    vstd::arithmetic::div_mod::lemma_mod_equivalence(
        (y * y) as int,
        (x * x * x + c.a * x + c.b) as int,
        c.p as int,
    );
}

// ---------------------------------------------------------------------
// SEC 1 §2.2.1: the two group laws.
// ---------------------------------------------------------------------

/// A point the verification can reach: O, or `(x, y)` with both
/// coordinates in [0, p-1] and on the curve.
pub open spec fn good(c: Curve, q: Point) -> bool {
    match q {
        Point::Infinity => true,
        Point::Affine { x, y } => x < c.p && y < c.p && satisfies_equation(c, x, y),
    }
}

/// Euclid's lemma for `p`: if p divides a product, it divides a factor.
/// True exactly for prime `p` (and 1); P-384's is [`crate::primality`]'s.
pub open spec fn euclid(p: nat) -> bool {
    forall|u: int, v: int|
        #[trigger] ((u * v) % (p as int)) == 0 ==> u % (p as int) == 0 || v % (p as int) == 0
}

/// Euclid's lemma, used once.
proof fn lemma_euclid_use(p: nat, u: int, v: int)
    requires
        euclid(p),
        (u * v) % (p as int) == 0,
    ensures
        u % (p as int) == 0 || v % (p as int) == 0,
{
}

/// What the two group laws need of the field to agree: p is an odd prime
/// (Euclid's lemma stands for primality).
pub open spec fn field_ok(c: Curve) -> bool {
    c.p > 2 && c.p % 2 == 1 && euclid(c.p)
}

/// SEC 1 §2.2.1 rule 3, as the two texts read it, for two points on the
/// curve with the same x: `y1 + y2 ≡ 0` exactly when "the points are either
/// distinct or have y-coordinate 0". Both coordinates are in [0, p-1].
pub proof fn lemma_rule3(c: Curve, x: nat, y1: nat, y2: nat)
    requires
        field_ok(c),
        y1 < c.p,
        y2 < c.p,
        satisfies_equation(c, x, y1),
        satisfies_equation(c, x, y2),
    ensures
        ((y1 + y2) % c.p == 0) == (y1 != y2 || y1 == 0),
{
    let p = c.p as int;
    if y1 == y2 {
        vstd::arithmetic::div_mod::lemma_small_mod(0, c.p);
        if y1 != 0 {
            // 0 < 2 y1 < 2p and p is odd, so 2 y1 is not 0 or p.
            if y1 + y2 < c.p {
                vstd::arithmetic::div_mod::lemma_small_mod((y1 + y2) as nat, c.p);
            } else {
                assert(y1 + y2 != c.p);
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                    (y1 + y2) as int,
                    p,
                    1,
                    (y1 + y2) - p,
                );
            }
            assert((y1 + y2) % c.p != 0);
        }
    } else {
        // y1^2 ≡ y2^2, so p | (y1 - y2)(y1 + y2), and p ∤ (y1 - y2).
        assert(y1 * y1 % c.p == y2 * y2 % c.p);
        vstd::arithmetic::div_mod::lemma_mod_equivalence((y1 * y1) as int, (y2 * y2) as int, p);
        assert((y1 - y2) * (y1 + y2) == y1 * y1 - y2 * y2) by (nonlinear_arith);
        assert(((y1 - y2) * (y1 + y2)) % p == 0);
        lemma_euclid_use(c.p, y1 - y2, (y1 + y2) as int);
        vstd::arithmetic::div_mod::lemma_mod_equivalence(y1 as int, y2 as int, p);
        vstd::arithmetic::div_mod::lemma_small_mod(y1, c.p);
        vstd::arithmetic::div_mod::lemma_small_mod(y2, c.p);
        assert((y1 - y2) % p != 0);
    }
}

/// From `inv(m, a) == Some(w)`: `a w ≡ 1`.
proof fn lemma_inv_some(m: nat, a: nat)
    requires
        m > 1,
        a < m,
        inv(m, a) is Some,
    ensures
        cong(m as int, (a * inv(m, a)->Some_0) as int, 1),
{
    vstd::arithmetic::div_mod::lemma_small_mod(a, m);
    vstd::arithmetic::div_mod::lemma_small_mod(1, m);
}

/// Rule 4, the chord (`x1 ≠ x2`): the same point, on the curve.
proof fn lemma_add_chord(
    c: Curve,
    d: crate::independent::Curve,
    x1: nat,
    y1: nat,
    x2: nat,
    y2: nat,
)
    requires
        corresponds(c, d),
        c.p > 1,
        x1 != x2,
        good(c, Point::Affine { x: x1, y: y1 }),
        good(c, Point::Affine { x: x2, y: y2 }),
    ensures
        ec_add(c, Point::Affine { x: x1, y: y1 }, Point::Affine { x: x2, y: y2 }) == opt_pt(
            crate::independent::add(
                d,
                crate::independent::EcPoint::Aff { x: x1, y: y1 },
                crate::independent::EcPoint::Aff { x: x2, y: y2 },
            ),
        ),
        match ec_add(c, Point::Affine { x: x1, y: y1 }, Point::Affine { x: x2, y: y2 }) {
            Some(r) => good(c, r),
            None => true,
        },
{
    let p = c.p;
    let pi = p as int;
    let dx = fe_sub(p, x2, x1);
    let dy = fe_sub(p, y2, y1);
    lemma_cong_fe_sub(p, x2, x1);
    lemma_cong_fe_sub(p, y2, y1);
    lemma_fe_sub(p, x2, x1);
    lemma_fe_sub(p, y2, y1);
    lemma_inv(p, dx);
    if inv(p, dx) is Some {
        let w = inv(p, dx)->Some_0;
        let lam = dy * w % p;
        let f1 = fe_sub(p, lam * lam % p, x1);
        let x3 = fe_sub(p, f1, x2);
        let fx = fe_sub(p, x1, x3);
        let y3 = fe_sub(p, lam * fx % p, y1);
        // The coordinates are equal.
        lemma_cong_mod(pi, (lam * lam) as int);
        lemma_cong_fe_sub(p, lam * lam % p, x1);
        lemma_cong_fe_sub(p, f1, x2);
        let xx3 = (lam * lam) as int - x1 - x2;
        lemma_cong_add(pi, (lam * lam % p) as int, (lam * lam) as int, x1 as int, x1 as int);
        lemma_cong_add(pi, f1 as int, (lam * lam) as int - x1, x2 as int, x2 as int);
        assert(cong(pi, x3 as int, xx3));
        lemma_cong_mod(pi, xx3);
        lemma_cong_reduced(pi, x3 as int, crate::independent::fmod(xx3, p) as int);
        assert(x3 == crate::independent::fmod(xx3, p));
        lemma_cong_fe_sub(p, x1, x3);
        lemma_cong_mul(pi, lam as int, lam as int, fx as int, x1 - x3);
        lemma_cong_mod(pi, (lam * fx) as int);
        lemma_cong_fe_sub(p, lam * fx % p, y1);
        let yy3 = lam * (x1 - x3) - y1;
        lemma_cong_add(pi, (lam * fx % p) as int, lam * (x1 - x3), y1 as int, y1 as int);
        assert(cong(pi, y3 as int, yy3));
        lemma_cong_mod(pi, yy3);
        lemma_cong_reduced(pi, y3 as int, crate::independent::fmod(yy3, p) as int);
        // The new point is on the curve (lemma_chord_on_curve).
        lemma_inv_some(p, dx);
        lemma_cong_mul(pi, dx as int, x2 - x1, w as int, w as int);
        assert(cong(pi, (x2 - x1) * w, 1));
        lemma_cong_mod(pi, (dy * w) as int);
        lemma_cong_mul(pi, dy as int, y2 - y1, w as int, w as int);
        assert(cong(pi, lam as int, (y2 - y1) * w));
        lemma_on_curve_cong(c, x1, y1);
        lemma_on_curve_cong(c, x2, y2);
        lemma_chord_on_curve(
            pi,
            c.a as int,
            c.b as int,
            x1 as int,
            y1 as int,
            x2 as int,
            y2 as int,
            w as int,
            lam as int,
        );
        let ex3 = lam * lam - x1 - x2;
        let ey3 = lam * (x1 - ex3) - y1;
        assert(ex3 == xx3);
        lemma_cong_add(pi, x1 as int, x1 as int, x3 as int, ex3);
        lemma_cong_mul(pi, lam as int, lam as int, x1 - x3, x1 - ex3);
        lemma_cong_add(pi, lam * (x1 - x3), lam * (x1 - ex3), y1 as int, y1 as int);
        assert(cong(pi, y3 as int, ey3));
        lemma_ce_cong(pi, c.a as int, c.b as int, x3 as int, y3 as int, ex3, ey3);
        lemma_on_curve_cong(c, x3, y3);
    }
}

/// Rule 5, the tangent (`x1 = x2`, and not rule 3): the double of the
/// first point, the same in both, on the curve.
proof fn lemma_add_tangent(
    c: Curve,
    d: crate::independent::Curve,
    x1: nat,
    y1: nat,
    y2: nat,
)
    requires
        corresponds(c, d),
        field_ok(c),
        good(c, Point::Affine { x: x1, y: y1 }),
        good(c, Point::Affine { x: x1, y: y2 }),
        !((y1 + y2) % c.p == 0),
    ensures
        ec_add(c, Point::Affine { x: x1, y: y1 }, Point::Affine { x: x1, y: y2 }) == opt_pt(
            crate::independent::add(
                d,
                crate::independent::EcPoint::Aff { x: x1, y: y1 },
                crate::independent::EcPoint::Aff { x: x1, y: y2 },
            ),
        ),
        match ec_add(c, Point::Affine { x: x1, y: y1 }, Point::Affine { x: x1, y: y2 }) {
            Some(r) => good(c, r),
            None => true,
        },
{
    let p = c.p;
    let pi = p as int;
    lemma_rule3(c, x1, y1, y2);
    let dy = 2 * y1 % p;
    lemma_inv(p, dy);
    lemma_cong_mod(pi, (2 * y1) as int);
    if inv(p, dy) is Some {
        let w = inv(p, dy)->Some_0;
        let t = 3 * x1 * x1 + c.a;
        let lam = t % p * w % p;
        vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(t as int, w as int, pi);
        assert(lam == (t * w) % p);
        let x3 = fe_sub(p, lam * lam % p, 2 * x1 % p);
        let fx = fe_sub(p, x1, x3);
        let y3 = fe_sub(p, lam * fx % p, y1);
        // The coordinates are equal.
        lemma_cong_mod(pi, (lam * lam) as int);
        lemma_cong_mod(pi, (2 * x1) as int);
        lemma_cong_fe_sub(p, lam * lam % p, 2 * x1 % p);
        let xx3 = (lam * lam) as int - 2 * x1;
        lemma_cong_add(pi, (lam * lam % p) as int, (lam * lam) as int, (2 * x1 % p) as int, (2 * x1) as int);
        assert(cong(pi, x3 as int, xx3));
        lemma_cong_mod(pi, xx3);
        lemma_cong_reduced(pi, x3 as int, crate::independent::fmod(xx3, p) as int);
        lemma_cong_fe_sub(p, x1, x3);
        lemma_cong_mul(pi, lam as int, lam as int, fx as int, x1 - x3);
        lemma_cong_mod(pi, (lam * fx) as int);
        lemma_cong_fe_sub(p, lam * fx % p, y1);
        let yy3 = lam * (x1 - x3) - y1;
        lemma_cong_add(pi, (lam * fx % p) as int, lam * (x1 - x3), y1 as int, y1 as int);
        assert(cong(pi, y3 as int, yy3));
        lemma_cong_mod(pi, yy3);
        lemma_cong_reduced(pi, y3 as int, crate::independent::fmod(yy3, p) as int);
        // The new point is on the curve (lemma_tangent_on_curve).
        lemma_inv_some(p, dy);
        lemma_cong_mul(pi, dy as int, (2 * y1) as int, w as int, w as int);
        assert(cong(pi, (2 * y1 * w) as int, 1));
        lemma_cong_mod(pi, (t * w) as int);
        assert(cong(pi, lam as int, ((3 * x1 * x1 + c.a) * w) as int));
        lemma_on_curve_cong(c, x1, y1);
        lemma_tangent_on_curve(pi, c.a as int, c.b as int, x1 as int, y1 as int, w as int, lam as int);
        let ex3 = lam * lam - 2 * x1;
        let ey3 = lam * (x1 - ex3) - y1;
        lemma_cong_add(pi, x1 as int, x1 as int, x3 as int, ex3);
        lemma_cong_mul(pi, lam as int, lam as int, x1 - x3, x1 - ex3);
        lemma_cong_add(pi, lam * (x1 - x3), lam * (x1 - ex3), y1 as int, y1 as int);
        assert(cong(pi, y3 as int, ey3));
        lemma_ce_cong(pi, c.a as int, c.b as int, x3 as int, y3 as int, ex3, ey3);
        lemma_on_curve_cong(c, x3, y3);
    }
}

/// SEC 1 §2.2.1, as the two texts transcribe it, gives the same sum of two
/// reachable points, and the sum is reachable.
pub proof fn lemma_add(
    c: Curve,
    d: crate::independent::Curve,
    q1: crate::independent::EcPoint,
    q2: crate::independent::EcPoint,
)
    requires
        corresponds(c, d),
        field_ok(c),
        good(c, pt(q1)),
        good(c, pt(q2)),
    ensures
        ec_add(c, pt(q1), pt(q2)) == opt_pt(crate::independent::add(d, q1, q2)),
        match ec_add(c, pt(q1), pt(q2)) {
            Some(r) => good(c, r),
            None => true,
        },
{
    match (q1, q2) {
        (
            crate::independent::EcPoint::Aff { x: x1, y: y1 },
            crate::independent::EcPoint::Aff { x: x2, y: y2 },
        ) => {
            if x1 != x2 {
                lemma_add_chord(c, d, x1, y1, x2, y2);
            } else {
                lemma_rule3(c, x1, y1, y2);
                if !((y1 + y2) % c.p == 0) {
                    lemma_add_tangent(c, d, x1, y1, y2);
                }
            }
        },
        _ => {},
    }
}

/// SEC 1 §2.2.1's `kP`, by the shared MSB-first double-and-add over the two
/// group laws, is the same product, and reachable.
pub proof fn lemma_scalar_mul(
    c: Curve,
    d: crate::independent::Curve,
    k: nat,
    q: crate::independent::EcPoint,
)
    requires
        corresponds(c, d),
        field_ok(c),
        good(c, pt(q)),
    ensures
        scalar_mul(c, k, pt(q)) == opt_pt(crate::independent::scalar_mul(d, k, q)),
        match scalar_mul(c, k, pt(q)) {
            Some(r) => good(c, r),
            None => true,
        },
    decreases k,
{
    if k > 0 {
        lemma_scalar_mul(c, d, k / 2, q);
        match crate::independent::scalar_mul(d, k / 2, q) {
            None => {},
            Some(a) => {
                lemma_add(c, d, a, a);
                match crate::independent::add(d, a, a) {
                    None => {},
                    Some(dd) => {
                        if k % 2 == 1 {
                            lemma_add(c, d, dd, q);
                        }
                    },
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// FIPS 186-5 §6.4.2 and SEC 1 §4.1.4.
// ---------------------------------------------------------------------

/// The two verifications agree on every input, for any two corresponding
/// curves over an odd prime field ([`field_ok`]) whose `n` exceeds 1 and
/// whose base point is on the curve.
pub proof fn lemma_verify_equal(
    c: Curve,
    d: crate::independent::Curve,
    h: Seq<u8>,
    r: nat,
    s: nat,
    q: Seq<u8>,
)
    requires
        corresponds(c, d),
        field_ok(c),
        c.n > 1,
        good(c, base_point(c)),
    ensures
        crate::independent::ecdsa_verify(d, h, r, s, q) == ecdsa_verify(c, h, r, s, q),
{
    lemma_decode_public_key(c, d, q);
    match crate::independent::decode_public_key(d, q) {
        None => {},
        Some(qu) => {
            if 1 <= r && r <= c.n - 1 && 1 <= s && s <= c.n - 1 {
                lemma_derive_e_equal(c, d, h);
                lemma_inv(c.n, s);
                if inv(c.n, s) is Some {
                    let w = inv(c.n, s)->Some_0;
                    let e = derive_e(c, h);
                    let u1 = e * w % c.n;
                    let u2 = r * w % c.n;
                    let g = crate::independent::EcPoint::Aff { x: d.gx, y: d.gy };
                    assert(pt(g) == base_point(c));
                    lemma_scalar_mul(c, d, u1, g);
                    lemma_scalar_mul(c, d, u2, qu);
                    match (
                        crate::independent::scalar_mul(d, u1, g),
                        crate::independent::scalar_mul(d, u2, qu),
                    ) {
                        (Some(a), Some(b)) => {
                            lemma_add(c, d, a, b);
                        },
                        _ => {},
                    }
                }
            }
        },
    }
}

/// The two P-384 records correspond, and P-384 meets the other conditions
/// of [`lemma_verify_equal`] but Euclid's lemma.
pub proof fn lemma_p384_corresponds()
    ensures
        corresponds(p384(), crate::independent::p384()),
        p384().p > 2,
        p384().p % 2 == 1,
        p384().n > 1,
        good(p384(), base_point(p384())),
{
    assert(crate::independent::field_octets(crate::independent::p384()) == 48) by (compute_only);
    assert(p384().p > 2 && p384().p % 2 == 1 && p384().n > 1) by (compute_only);
    assert(good(p384(), base_point(p384()))) by (compute_only);
}

} // verus!
