//! Facts the point, scalar and verify code is proven from: about octet
//! strings, the curve constants and the modular arithmetic of the group law.
//! Everything here is proven, none is assumed.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


// ---------------------------------------------------------------------
// Octet strings.
// ---------------------------------------------------------------------

/// An all-zero octet string is the integer 0.
pub proof fn lemma_os2ip_zeros(s: Seq<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] == 0,
    ensures
        os2ip(s) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies d[i] == 0 by {
            assert(d[i] == s[i]);
        }
        lemma_os2ip_zeros(d);
    }
}

/// An octet string whose last octet is `b` and the rest all zero is the
/// integer `b`.
pub proof fn lemma_os2ip_last(s: Seq<u8>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() - 1 ==> s[i] == 0,
    ensures
        os2ip(s) == s.last() as nat,
{
    let d = s.drop_last();
    assert forall|i: int| 0 <= i < d.len() implies d[i] == 0 by {
        assert(d[i] == s[i]);
    }
    lemma_os2ip_zeros(d);
}

/// Both moduli exceed 256, so a byte (and 256) is a residue.
pub proof fn lemma_modulus_gt_256(w: crate::field::spec::Which)
    ensures
        crate::field::spec::modulus(w) > 256,
{
    match w {
        crate::field::spec::Which::P => {
            assert(p384().p > 256) by (compute_only);
        },
        crate::field::spec::Which::N => {
            assert(p384().n > 256) by (compute_only);
        },
    }
}

/// Horner's step modulo `m`: reducing before multiplying by 256 and adding
/// the octet `b` gives the residue of the whole.
pub proof fn lemma_horner_mod(x: nat, b: nat, m: nat)
    requires
        m > 0,
        b < m,
    ensures
        (((x % m) * 256) % m + b) % m == (x * 256 + b) % m,
{
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(x as int, 256int, m as int);
    vstd::arithmetic::div_mod::lemma_small_mod(b, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((x * 256) as int, b as int, m as int);
}

/// A product with a residue reduced first is the residue of the product.
pub proof fn lemma_mul_reduced(x: nat, w: nat, m: nat)
    requires
        m > 0,
    ensures
        ((x % m) * w) % m == (x * w) % m,
{
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(x as int, w as int, m as int);
}

// ---------------------------------------------------------------------
// The curve constants.
// ---------------------------------------------------------------------

/// The coefficient `a` is `p - 3` (SP 800-186 §3.2.1: a = -3).
pub proof fn lemma_curve_a()
    ensures
        p384().a == p384().p - 3,
        p384().a < p384().p,
        p384().b < p384().p,
        p384().gx < p384().p,
        p384().gy < p384().p,
{
    assert(p384().a == p384().p - 3 && p384().a < p384().p && p384().b < p384().p && p384().gx
        < p384().p && p384().gy < p384().p) by (compute_only);
}

// ---------------------------------------------------------------------
// The curve constants as octet strings (SP 800-186 §3.2.1.4).
// ---------------------------------------------------------------------

/// The 48 big-endian octets of the curve constant `b`.
pub open spec fn b_octets() -> Seq<u8> {
    seq![0xb3, 0x31, 0x2f, 0xa7, 0xe2, 0x3e, 0xe7, 0xe4, 0x98, 0x8e, 0x05, 0x6b, 0xe3, 0xf8, 0x2d, 0x19, 0x18, 0x1d, 0x9c, 0x6e, 0xfe, 0x81, 0x41, 0x12, 0x03, 0x14, 0x08, 0x8f, 0x50, 0x13, 0x87, 0x5a, 0xc6, 0x56, 0x39, 0x8d, 0x8a, 0x2e, 0xd1, 0x9d, 0x2a, 0x85, 0xc8, 0xed, 0xd3, 0xec, 0x2a, 0xef]
}

/// `b_octets` is 48 octets and is `b`.
pub proof fn lemma_b_octets()
    ensures
        b_octets().len() == 48,
        os2ip(b_octets()) == p384().b,
{
    assert(b_octets().len() == 48 && os2ip(b_octets()) == p384().b) by (compute_only);
}

/// The 48 big-endian octets of the curve constant `gx`.
pub open spec fn gx_octets() -> Seq<u8> {
    seq![0xaa, 0x87, 0xca, 0x22, 0xbe, 0x8b, 0x05, 0x37, 0x8e, 0xb1, 0xc7, 0x1e, 0xf3, 0x20, 0xad, 0x74, 0x6e, 0x1d, 0x3b, 0x62, 0x8b, 0xa7, 0x9b, 0x98, 0x59, 0xf7, 0x41, 0xe0, 0x82, 0x54, 0x2a, 0x38, 0x55, 0x02, 0xf2, 0x5d, 0xbf, 0x55, 0x29, 0x6c, 0x3a, 0x54, 0x5e, 0x38, 0x72, 0x76, 0x0a, 0xb7]
}

/// `gx_octets` is 48 octets and is `gx`.
pub proof fn lemma_gx_octets()
    ensures
        gx_octets().len() == 48,
        os2ip(gx_octets()) == p384().gx,
{
    assert(gx_octets().len() == 48 && os2ip(gx_octets()) == p384().gx) by (compute_only);
}

/// The 48 big-endian octets of the curve constant `gy`.
pub open spec fn gy_octets() -> Seq<u8> {
    seq![0x36, 0x17, 0xde, 0x4a, 0x96, 0x26, 0x2c, 0x6f, 0x5d, 0x9e, 0x98, 0xbf, 0x92, 0x92, 0xdc, 0x29, 0xf8, 0xf4, 0x1d, 0xbd, 0x28, 0x9a, 0x14, 0x7c, 0xe9, 0xda, 0x31, 0x13, 0xb5, 0xf0, 0xb8, 0xc0, 0x0a, 0x60, 0xb1, 0xce, 0x1d, 0x7e, 0x81, 0x9d, 0x7a, 0x43, 0x1d, 0x7c, 0x90, 0xea, 0x0e, 0x5f]
}

/// `gy_octets` is 48 octets and is `gy`.
pub proof fn lemma_gy_octets()
    ensures
        gy_octets().len() == 48,
        os2ip(gy_octets()) == p384().gy,
{
    assert(gy_octets().len() == 48 && os2ip(gy_octets()) == p384().gy) by (compute_only);
}

// ---------------------------------------------------------------------
// The doubling's slope numerator, 3 x^2 + a.
// ---------------------------------------------------------------------

/// What the code computes for `3 x1^2 + a`: three copies of `x1 x1 mod m`
/// added modulo `m`, then `a`.
pub proof fn lemma_dbl_num(m: nat, x: nat, a: nat)
    requires
        m > 0,
        x < m,
        a < m,
    ensures
        ({
            let xx = x * x % m;
            let t2 = (xx + xx) % m;
            let t3 = (t2 + xx) % m;
            (t3 + a) % m == (3 * x * x + a) % m
        }),
{
    let xx = x * x % m;
    vstd::arithmetic::div_mod::lemma_small_mod(xx, m) ;
    // xx < m here since it is a remainder.
    assert(xx < m) by {
        vstd::arithmetic::div_mod::lemma_mod_bound((x * x) as int, m as int);
    }
    vstd::arithmetic::div_mod::lemma_small_mod(xx, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(xx as int, xx as int, m as int);
    let t2 = (xx + xx) % m;
    vstd::arithmetic::div_mod::lemma_add_mod_noop(t2 as int, xx as int, m as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((xx + xx) as int, xx as int, m as int);
    // t3 = (3 xx) mod m.
    let t3 = (t2 + xx) % m;
    assert(t3 == (xx + xx + xx) % m);
    vstd::arithmetic::div_mod::lemma_small_mod(a, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((xx + xx + xx) as int, a as int, m as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(t3 as int, a as int, m as int);
    // (3 xx + a) = (3 x x + a) mod m since xx = x x mod m.
    assert(3 * x * x == 3 * (x * x)) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_right(3int, (x * x) as int, m as int);
    assert((xx + xx + xx) == 3 * xx) by (nonlinear_arith)
        requires
            true,
    ;
    vstd::arithmetic::div_mod::lemma_add_mod_noop((3 * xx) as int, a as int, m as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((3 * (x * x)) as int, a as int, m as int);
}

// ---------------------------------------------------------------------
// The curve equation's right-hand side, x^3 + a x + b.
// ---------------------------------------------------------------------

/// What the code computes for `x^3 + a x + b`.
pub proof fn lemma_rhs(m: nat, x: nat, a: nat, b: nat)
    requires
        m > 0,
        b < m,
    ensures
        ({
            let x2 = x * x % m;
            let x3 = x2 * x % m;
            let ax = a * x % m;
            ((x3 + ax) % m + b) % m == (x * x * x + a * x + b) % m
        }),
{
    let x2 = x * x % m;
    let x3 = x2 * x % m;
    let ax = a * x % m;
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_left((x * x) as int, x as int, m as int);
    assert(x * x * x == (x * x) * x);
    // x3 = (x x x) mod m
    vstd::arithmetic::div_mod::lemma_add_mod_noop((x * x * x) as int, (a * x) as int, m as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(x3 as int, ax as int, m as int);
    vstd::arithmetic::div_mod::lemma_small_mod(b, m);
    vstd::arithmetic::div_mod::lemma_add_mod_noop((x * x * x + a * x) as int, b as int, m as int);
    vstd::arithmetic::div_mod::lemma_add_mod_noop(((x3 + ax) % m) as int, b as int, m as int);
}

// ---------------------------------------------------------------------
// FIPS 186-5 step 3: the digest as bits, and as an integer.
// ---------------------------------------------------------------------

/// `two_to` at the eight shifts of one octet.
proof fn lemma_two_to_small()
    ensures
        two_to(0) == 1,
        two_to(1) == 2,
        two_to(2) == 4,
        two_to(3) == 8,
        two_to(4) == 16,
        two_to(5) == 32,
        two_to(6) == 64,
        two_to(7) == 128,
{
    assert(two_to(0) == 1 && two_to(1) == 2 && two_to(2) == 4 && two_to(3) == 8 && two_to(4) == 16
        && two_to(5) == 32 && two_to(6) == 64 && two_to(7) == 128) by (compute_only);
}

/// The eight binary digits of an octet add up to it.
proof fn lemma_octet_digits(b: u32)
    requires
        b < 256,
    ensures
        ((b / 128) % 2) * 128 + ((b / 64) % 2) * 64 + ((b / 32) % 2) * 32 + ((b / 16) % 2) * 16
            + ((b / 8) % 2) * 8 + ((b / 4) % 2) * 4 + ((b / 2) % 2) * 2 + b % 2 == b,
{
    assert(((b / 128) % 2) * 128 + ((b / 64) % 2) * 64 + ((b / 32) % 2) * 32 + ((b / 16) % 2) * 16
        + ((b / 8) % 2) * 8 + ((b / 4) % 2) * 4 + ((b / 2) % 2) * 2 + b % 2 == b) by (bit_vector)
        requires
            b < 256,
    ;
}

/// One more bit is Horner's step.
proof fn lemma_bits_take_step(h: Seq<bool>, n: int)
    requires
        0 < n <= h.len(),
    ensures
        bits_to_int(h.take(n)) == bits_to_int(h.take(n - 1)) * 2 + (if h[n - 1] {
            1nat
        } else {
            0nat
        }),
{
    assert(h.take(n).drop_last() =~= h.take(n - 1));
    assert(h.take(n).last() == h[n - 1]);
}

/// Appending one octet `b` to `g` appends its eight bits, most significant
/// first, and `bits_to_int` is Horner's rule over them: the integer of the
/// bits of `g` times 256, plus `b`.
proof fn lemma_bits_push_octet(g: Seq<u8>, b: u8)
    ensures
        bits_to_int(octets_to_bits(g.push(b))) == bits_to_int(octets_to_bits(g)) * 256 + b as nat,
{
    lemma_two_to_small();
    let hh = octets_to_bits(g.push(b));
    let l: int = 8 * g.len() as int;
    assert(hh.len() == l + 8);
    assert(hh.take(l) =~= octets_to_bits(g)) by {
        assert forall|i: int| #![auto] 0 <= i < l implies hh.take(l)[i] == octets_to_bits(g)[i] by {
            assert(g.push(b)[i / 8] == g[i / 8]);
        }
    }
    lemma_bits_take_step(hh, l + 1);
    lemma_bits_take_step(hh, l + 2);
    lemma_bits_take_step(hh, l + 3);
    lemma_bits_take_step(hh, l + 4);
    lemma_bits_take_step(hh, l + 5);
    lemma_bits_take_step(hh, l + 6);
    lemma_bits_take_step(hh, l + 7);
    lemma_bits_take_step(hh, l + 8);
    assert(hh.take(l + 8) =~= hh);
    // The eight bits are those of b.
    assert(g.push(b)[g.len() as int] == b);
    assert((l + 0) / 8 == g.len() && (l + 0) % 8 == 0);
    assert((l + 1) / 8 == g.len() && (l + 1) % 8 == 1);
    assert((l + 2) / 8 == g.len() && (l + 2) % 8 == 2);
    assert((l + 3) / 8 == g.len() && (l + 3) % 8 == 3);
    assert((l + 4) / 8 == g.len() && (l + 4) % 8 == 4);
    assert((l + 5) / 8 == g.len() && (l + 5) % 8 == 5);
    assert((l + 6) / 8 == g.len() && (l + 6) % 8 == 6);
    assert((l + 7) / 8 == g.len() && (l + 7) % 8 == 7);
    let x = bits_to_int(octets_to_bits(g));
    let bb = b as nat;
    let d0 = if hh[l] { 1nat } else { 0nat };
    let d1 = if hh[l + 1] { 1nat } else { 0nat };
    let d2 = if hh[l + 2] { 1nat } else { 0nat };
    let d3 = if hh[l + 3] { 1nat } else { 0nat };
    let d4 = if hh[l + 4] { 1nat } else { 0nat };
    let d5 = if hh[l + 5] { 1nat } else { 0nat };
    let d6 = if hh[l + 6] { 1nat } else { 0nat };
    let d7 = if hh[l + 7] { 1nat } else { 0nat };
    assert(d0 == (bb / 128) % 2);
    assert(d1 == (bb / 64) % 2);
    assert(d2 == (bb / 32) % 2);
    assert(d3 == (bb / 16) % 2);
    assert(d4 == (bb / 8) % 2);
    assert(d5 == (bb / 4) % 2);
    assert(d6 == (bb / 2) % 2);
    assert(bb / two_to(0) == bb) by (nonlinear_arith)
        requires
            two_to(0) == 1,
    ;
    assert(d7 == bb % 2);
    lemma_octet_digits(b as u32);
    assert(d0 * 128 + d1 * 64 + d2 * 32 + d3 * 16 + d4 * 8 + d5 * 4 + d6 * 2 + d7 == bb);
    assert(bits_to_int(hh.take(l)) == x);
    assert(bits_to_int(hh) == x * 256 + bb);
}

/// The bits of an octet string, read as an integer, are its `os2ip`
/// (SEC 1 §2.3.2 followed by FIPS 186-5 B.2.1 is SEC 1 §2.3.8).
pub proof fn lemma_bits_os2ip(h: Seq<u8>)
    ensures
        bits_to_int(octets_to_bits(h)) == os2ip(h),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(octets_to_bits(h) =~= Seq::<bool>::empty());
    } else {
        let g = h.drop_last();
        lemma_bits_os2ip(g);
        lemma_bits_push_octet(g, h.last());
        assert(g.push(h.last()) =~= h);
    }
}

/// FIPS 186-5 §6.4.2 step 3 for P-384: `derive_e` keeps the first
/// `min(|h|, 48)` octets of the digest and reads them as an integer, which
/// is below 2^384, so it fits in 48 octets. (`⌈log2 n⌉ = 384`.)
pub proof fn lemma_derive_e(h: Seq<u8>)
    ensures
        derive_e(p384(), h) == os2ip(h.subrange(0, if h.len() <= 48 {
            h.len() as int
        } else {
            48int
        })),
{
    assert(ceil_log2(p384().n) == 384) by (compute_only);
    let hbits = octets_to_bits(h);
    assert(hbits.len() == 8 * h.len());
    if h.len() <= 48 {
        assert(h.subrange(0, h.len() as int) =~= h);
        lemma_bits_os2ip(h);
    } else {
        let h48 = h.subrange(0, 48);
        assert(hbits.take(384) =~= octets_to_bits(h48)) by {
            assert forall|i: int| #![auto] 0 <= i < 384 implies hbits.take(384)[i] == octets_to_bits(h48)[i] by {
                assert(h48[i / 8] == h[i / 8]);
            }
        }
        lemma_bits_os2ip(h48);
    }
}

} // verus!
