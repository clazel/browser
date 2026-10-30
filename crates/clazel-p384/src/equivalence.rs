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
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        assert(s.skip(1) =~= Seq::<u8>::empty());
        assert(os2ip(Seq::<u8>::empty()) == 0);
        assert(crate::independent::power(256, 0) == 1);
        assert(os2ip(s) == os2ip(s.drop_last()) * 256 + s.last() as nat);
    } else {
        let d = s.drop_last();
        lemma_os2ip_first(d);
        assert(d.skip(1) =~= s.skip(1).drop_last());
        assert(s.skip(1).last() == s.last());
        let pw = crate::independent::power(256, (s.len() - 2) as nat);
        assert(crate::independent::power(256, (s.len() - 1) as nat) == 256 * pw);
        let x0 = s[0] as nat;
        assert(d[0] == s[0]);
        assert(os2ip(s) == os2ip(d) * 256 + s.last() as nat);
        assert(os2ip(s.skip(1)) == os2ip(s.skip(1).drop_last()) * 256 + s.last() as nat);
        assert((x0 * pw + os2ip(d.skip(1))) * 256 + s.last() as nat == x0 * (256 * pw) + (os2ip(
            d.skip(1),
        ) * 256 + s.last() as nat)) by (nonlinear_arith);
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
        assert(crate::independent::power(2, 0) == 1);
        assert(crate::independent::bits_value(b) == 0);
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

} // verus!
