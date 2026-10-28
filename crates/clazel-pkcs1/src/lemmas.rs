//! Facts proven about the spec itself. The first group is what the
//! executable code needs (Horner form of OS2IP, bounds, the modulus
//! range); the second states what RFC 8017 claims (I2OSP inverts OS2IP,
//! a validly produced signature verifies, a representative at least `n` is
//! rejected, the `DigestInfo` prefixes have the lengths §9.2 says). They
//! are evidence that the transcription is right (docs/SPEC-STYLE.md), not
//! part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Powers of 256.
// ---------------------------------------------------------------------

/// `pow256` is `vstd`'s `pow(256, m)`.
pub proof fn lemma_pow256_is_pow(m: nat)
    ensures
        pow256(m) == vstd::arithmetic::power::pow(256, m) as nat,
    decreases m,
{
    use vstd::arithmetic::power::*;
    if m == 0 {
        lemma_pow0(256);
    } else if m % 2 == 0 {
        lemma_pow256_is_pow(m / 2);
        lemma_pow_adds(256, m / 2, m / 2);
        lemma_pow_positive(256, m / 2);
        lemma_pow_positive(256, m);
        assert(m == m / 2 + m / 2);
    } else {
        lemma_pow256_is_pow((m - 1) as nat);
        lemma_pow_adds(256, (m - 1) as nat, 1);
        lemma_pow1(256);
        lemma_pow_positive(256, (m - 1) as nat);
        lemma_pow_positive(256, m);
    }
}

/// `two_to` is `vstd`'s `pow2`.
pub proof fn lemma_two_to_is_pow2(m: nat)
    ensures
        two_to(m) == vstd::arithmetic::power2::pow2(m),
    decreases m,
{
    use vstd::arithmetic::power2::*;
    lemma2_to64();
    if m == 0 {
    } else if m % 2 == 0 {
        lemma_two_to_is_pow2(m / 2);
        lemma_pow2_adds(m / 2, m / 2);
        assert(m == m / 2 + m / 2);
    } else {
        lemma_two_to_is_pow2((m - 1) as nat);
        lemma_pow2_unfold(m);
    }
}

/// `2^(m + 1) = 2 * 2^m`.
pub proof fn lemma_two_to_succ(m: nat)
    ensures
        two_to(m + 1) == 2 * two_to(m),
{
    lemma_two_to_is_pow2(m);
    lemma_two_to_is_pow2(m + 1);
    vstd::arithmetic::power2::lemma_pow2_unfold(m + 1);
}

/// `2^m > 0`.
pub proof fn lemma_two_to_pos(m: nat)
    ensures
        two_to(m) > 0,
{
    lemma_two_to_is_pow2(m);
    vstd::arithmetic::power2::lemma_pow2_pos(m);
}

/// `2^64`.
pub proof fn lemma_two_to_64()
    ensures
        two_to(64) == 0x1_0000_0000_0000_0000nat,
{
    lemma_two_to_is_pow2(64);
    vstd::arithmetic::power2::lemma2_to64();
}

/// `256^(m + 1) = 256 * 256^m`.
pub proof fn lemma_pow256_succ(m: nat)
    ensures
        pow256(m + 1) == 256 * pow256(m),
{
    lemma_pow256_is_pow(m);
    lemma_pow256_is_pow(m + 1);
    vstd::arithmetic::power::lemma_pow_adds(256, m, 1);
    vstd::arithmetic::power::lemma_pow1(256);
    vstd::arithmetic::power::lemma_pow_positive(256, m);
    vstd::arithmetic::power::lemma_pow_positive(256, m + 1);
}

/// `256^0 = 1`.
pub proof fn lemma_pow256_zero()
    ensures
        pow256(0) == 1,
{
}

/// `256^m > 0`.
pub proof fn lemma_pow256_pos(m: nat)
    ensures
        pow256(m) > 0,
    decreases m,
{
    if m == 0 {
        lemma_pow256_zero();
    } else {
        lemma_pow256_succ((m - 1) as nat);
        lemma_pow256_pos((m - 1) as nat);
    }
}

/// `256^a <= 256^b` for `a <= b`.
pub proof fn lemma_pow256_monotone(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow256(a) <= pow256(b),
    decreases b - a,
{
    if a < b {
        lemma_pow256_monotone(a, (b - 1) as nat);
        lemma_pow256_succ((b - 1) as nat);
        lemma_pow256_pos((b - 1) as nat);
    }
}

/// `256^(8 l) = 2^(64 l)` as `limb_pow(l)`.
pub proof fn lemma_pow256_limb(l: nat)
    ensures
        pow256(8 * l) == crate::bignum::spec::limb_pow(l),
    decreases l,
{
    if l == 0 {
        lemma_pow256_zero();
    } else {
        lemma_pow256_limb((l - 1) as nat);
        // 256^(8 l) = 256^8 * 256^(8 (l-1)), and 256^8 = 2^64.
        let b = (8 * (l - 1)) as nat;
        assert(8 * l == b + 8);
        lemma_pow256_succ(b);
        lemma_pow256_succ(b + 1);
        lemma_pow256_succ(b + 2);
        lemma_pow256_succ(b + 3);
        lemma_pow256_succ(b + 4);
        lemma_pow256_succ(b + 5);
        lemma_pow256_succ(b + 6);
        lemma_pow256_succ(b + 7);
    }
}

/// `256^m = 2^(8 m)`.
pub proof fn lemma_pow256_two_to(m: nat)
    ensures
        pow256(m) == two_to(8 * m),
    decreases m,
{
    if m == 0 {
    } else {
        lemma_pow256_two_to((m - 1) as nat);
        lemma_pow256_succ((m - 1) as nat);
        let b = (8 * (m - 1)) as nat;
        assert(8 * m == b + 8);
        lemma_two_to_succ(b);
        lemma_two_to_succ(b + 1);
        lemma_two_to_succ(b + 2);
        lemma_two_to_succ(b + 3);
        lemma_two_to_succ(b + 4);
        lemma_two_to_succ(b + 5);
        lemma_two_to_succ(b + 6);
        lemma_two_to_succ(b + 7);
    }
}

// ---------------------------------------------------------------------
// OS2IP: Horner form, bounds, injectivity.
// ---------------------------------------------------------------------

/// The partial sums of a sequence and of the sequence with one more octet
/// are related by one factor of 256.
proof fn lemma_os2ip_sum_push(s: Seq<u8>, b: u8, m: nat)
    requires
        m <= s.len(),
    ensures
        os2ip_sum(s.push(b), m) == 256 * os2ip_sum(s, m),
    decreases m,
{
    if m > 0 {
        lemma_os2ip_sum_push(s, b, (m - 1) as nat);
        assert(s.push(b)[(m - 1) as int] == s[(m - 1) as int]);
        // exponent: (len + 1 - m) = (len - m) + 1.
        assert((s.push(b).len() - m) as nat == (s.len() - m) as nat + 1);
        lemma_pow256_succ((s.len() - m) as nat);
        let t = s[(m - 1) as int] as nat;
        let pw = pow256((s.len() - m) as nat);
        assert(t * (256 * pw) == 256 * (t * pw)) by (nonlinear_arith);
    }
}

/// Horner's rule: appending an octet multiplies by 256 and adds it.
pub proof fn lemma_os2ip_push(s: Seq<u8>, b: u8)
    ensures
        os2ip(s.push(b)) == os2ip(s) * 256 + b as nat,
{
    let t = s.push(b);
    assert(t.len() == s.len() + 1);
    lemma_os2ip_sum_push(s, b, s.len());
    // sum(t, len + 1) = sum(t, len) + b * 256^0.
    lemma_pow256_zero();
    assert(t[s.len() as int] == b);
    assert((t.len() - (s.len() + 1)) as nat == 0);
}

/// Horner's rule on the last octet.
pub proof fn lemma_os2ip_last(s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        os2ip(s) == os2ip(s.drop_last()) * 256 + s.last() as nat,
{
    let d = s.drop_last();
    assert(d.push(s.last()) =~= s);
    lemma_os2ip_push(d, s.last());
}

/// `OS2IP(X) < 256^xLen`.
pub proof fn lemma_os2ip_bound(s: Seq<u8>)
    ensures
        os2ip(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() == 0 {
        lemma_pow256_zero();
    } else {
        let d = s.drop_last();
        lemma_os2ip_bound(d);
        lemma_os2ip_last(s);
        lemma_pow256_succ(d.len());
        let pd = pow256(d.len());
        assert(os2ip(s) < 256 * pd) by (nonlinear_arith)
            requires
                os2ip(d) < pd,
                os2ip(s) == os2ip(d) * 256 + s.last() as nat,
                s.last() < 256,
        ;
    }
}

/// The first octet decides the magnitude:
/// `X_1 256^(xLen-1) <= OS2IP(X) < (X_1 + 1) 256^(xLen-1)`.
pub proof fn lemma_os2ip_first(s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        (s[0] as nat) * pow256((s.len() - 1) as nat) <= os2ip(s),
        os2ip(s) < (s[0] as nat + 1) * pow256((s.len() - 1) as nat),
    decreases s.len(),
{
    lemma_pow256_zero();
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        lemma_os2ip_last(s);
        assert(os2ip(Seq::<u8>::empty()) == 0);
        assert((s[0] as nat + 1) * pow256(0) == s[0] as nat + 1) by (nonlinear_arith)
            requires
                pow256(0) == 1,
        ;
        assert((s[0] as nat) * pow256(0) == s[0] as nat) by (nonlinear_arith)
            requires
                pow256(0) == 1,
        ;
    } else {
        let d = s.drop_last();
        assert(d[0] == s[0]);
        lemma_os2ip_first(d);
        lemma_os2ip_last(s);
        lemma_pow256_succ((s.len() - 2) as nat);
        let pd = pow256((s.len() - 2) as nat);
        let a = s[0] as nat;
        let od = os2ip(d);
        assert(a * (256 * pd) <= od * 256) by (nonlinear_arith)
            requires
                a * pd <= od,
        ;
        assert(od * 256 + (s.last() as nat) < (a + 1) * (256 * pd)) by (nonlinear_arith)
            requires
                od < (a + 1) * pd,
                s.last() < 256,
        ;
    }
}

/// Leading zero octets do not change `OS2IP`.
pub proof fn lemma_os2ip_leading_zeros(s: Seq<u8>, z: nat)
    requires
        z <= s.len(),
        forall|i: int| 0 <= i < z ==> s[i] == 0,
    ensures
        os2ip(s) == os2ip(s.skip(z as int)),
    decreases s.len(),
{
    if s.len() == z {
        // All zero: OS2IP is 0 by Horner's rule.
        if s.len() > 0 {
            let d = s.drop_last();
            assert(forall|i: int| 0 <= i < d.len() ==> d[i] == 0);
            lemma_os2ip_leading_zeros(d, d.len());
            lemma_os2ip_last(s);
            assert(s.last() == 0);
            assert(os2ip(d.skip(d.len() as int)) == 0) by {
                assert(d.skip(d.len() as int) =~= Seq::<u8>::empty());
            }
        }
        assert(s.skip(z as int) =~= Seq::<u8>::empty());
    } else {
        let d = s.drop_last();
        assert(forall|i: int| 0 <= i < z ==> d[i] == 0);
        lemma_os2ip_leading_zeros(d, z);
        lemma_os2ip_last(s);
        let rest = s.skip(z as int);
        assert(rest.drop_last() =~= d.skip(z as int));
        lemma_os2ip_last(rest);
        assert(rest.last() == s.last());
    }
}

/// `OS2IP` is injective on strings of the same length.
pub proof fn lemma_os2ip_inj(x: Seq<u8>, y: Seq<u8>)
    requires
        x.len() == y.len(),
        os2ip(x) == os2ip(y),
    ensures
        x == y,
    decreases x.len(),
{
    if x.len() > 0 {
        let dx = x.drop_last();
        let dy = y.drop_last();
        lemma_os2ip_last(x);
        lemma_os2ip_last(y);
        // os2ip(d) * 256 + last, with last < 256: both parts are determined.
        assert(os2ip(x) == 256 * os2ip(dx) + x.last() as nat);
        assert(os2ip(y) == 256 * os2ip(dy) + y.last() as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            os2ip(x) as int,
            256,
            os2ip(dx) as int,
            x.last() as int,
        );
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            os2ip(y) as int,
            256,
            os2ip(dy) as int,
            y.last() as int,
        );
        assert(os2ip(dx) == os2ip(dy));
        lemma_os2ip_inj(dx, dy);
        assert(x.last() == y.last());
        assert(x =~= dx.push(x.last()));
        assert(y =~= dy.push(y.last()));
    } else {
        assert(x =~= y);
    }
}

// ---------------------------------------------------------------------
// octet_len and the modulus range.
// ---------------------------------------------------------------------

/// A string whose first octet is nonzero has `OS2IP` of that many octets.
pub proof fn lemma_octet_len_os2ip(s: Seq<u8>)
    requires
        s.len() > 0,
        s[0] != 0,
    ensures
        octet_len(os2ip(s)) == s.len(),
    decreases s.len(),
{
    lemma_pow256_zero();
    lemma_os2ip_first(s);
    if s.len() == 1 {
        assert((s[0] as nat) * pow256(0) == s[0] as nat) by (nonlinear_arith)
            requires
                pow256(0) == 1,
        ;
        assert((s[0] as nat + 1) * pow256(0) == s[0] as nat + 1) by (nonlinear_arith)
            requires
                pow256(0) == 1,
        ;
        assert(os2ip(s) == s[0] as nat);
        assert(os2ip(s) / 256 == 0);
    } else {
        let d = s.drop_last();
        assert(d[0] == s[0]);
        lemma_octet_len_os2ip(d);
        lemma_os2ip_first(d);
        lemma_pow256_pos((d.len() - 1) as nat);
        assert((s[0] as nat) * pow256((d.len() - 1) as nat) >= 1) by (nonlinear_arith)
            requires
                s[0] >= 1,
                pow256((d.len() - 1) as nat) >= 1,
        ;
        lemma_os2ip_last(s);
        assert(os2ip(s) == 256 * os2ip(d) + s.last() as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            os2ip(s) as int,
            256,
            os2ip(d) as int,
            s.last() as int,
        );
        assert(os2ip(s) / 256 == os2ip(d));
    }
}

/// `256^(k-1) <= n < 256^k` for the `k` that [`octet_len`] gives.
pub proof fn lemma_octet_len_bounds(n: nat)
    requires
        n > 0,
    ensures
        n < pow256(octet_len(n)),
        pow256((octet_len(n) - 1) as nat) <= n,
    decreases n,
{
    lemma_pow256_zero();
    let q = n / 256;
    if q == 0 {
        assert(octet_len(n) == 1);
        lemma_pow256_succ(0);
    } else {
        lemma_octet_len_bounds(q);
        lemma_pow256_succ(octet_len(q));
        lemma_pow256_succ((octet_len(q) - 1) as nat);
        assert(octet_len(n) == 1 + octet_len(q));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n as int, 256);
        assert(n < 256 * pow256(octet_len(q))) by (nonlinear_arith)
            requires
                n < 256 * (q + 1),
                q < pow256(octet_len(q)),
        ;
    }
}

/// The range check the executable code makes on a modulus given as `k`
/// octets, the first of which is `b0` and nonzero.
pub open spec fn range_check(k: nat, b0: u8) -> bool {
    (257 <= k <= 1024) || (k == 256 && b0 >= 0x80)
}

/// `256^(m)` for the bit lengths 2040, 2048 and 8192 and the bound
/// `2^2047 = 128 * 256^255`.
proof fn lemma_range_constants()
    ensures
        pow256(1024) == two_to(8192),
        pow256(256) == two_to(2048),
        two_to(2047) == 128 * pow256(255),
        pow256(256) == 256 * pow256(255),
        pow256(255) >= 1,
{
    lemma_pow256_succ(255);
    lemma_pow256_two_to(1024);
    lemma_pow256_two_to(256);
    lemma_two_to_succ(2047);
    lemma_pow256_pos(255);
}

/// For a modulus of `k` octets whose first octet is `b0 != 0`, the
/// executable range check decides `modulus_in_range`, and `k` is the
/// RFC's modulus length.
pub proof fn lemma_modulus_range(s: Seq<u8>)
    requires
        s.len() > 0,
        s[0] != 0,
    ensures
        modulus_in_range(os2ip(s)) == range_check(s.len(), s[0]),
        octet_len(os2ip(s)) == s.len(),
        os2ip(s) < pow256(s.len()),
{
    lemma_range_constants();
    lemma_octet_len_os2ip(s);
    lemma_os2ip_bound(s);
    lemma_os2ip_first(s);
    let k = s.len();
    let n = os2ip(s);
    let b0 = s[0] as nat;
    let p = pow256((k - 1) as nat);
    lemma_pow256_pos((k - 1) as nat);
    assert(b0 * p >= p) by (nonlinear_arith)
        requires
            b0 >= 1,
            p >= 1,
    ;
    if k >= 1025 {
        lemma_pow256_monotone(1024, (k - 1) as nat);
        assert(n >= two_to(8192));
        assert(!modulus_in_range(n));
        assert(!range_check(k, s[0]));
    } else if k >= 257 {
        lemma_pow256_monotone(256, (k - 1) as nat);
        lemma_pow256_monotone(k, 1024);
        assert(n >= two_to(2048));
        assert(n < two_to(8192));
        assert(two_to(2047) < two_to(2048));
        assert(modulus_in_range(n));
        assert(range_check(k, s[0]));
    } else if k == 256 {
        assert(p == pow256(255));
        assert(n < two_to(8192)) by {
            lemma_pow256_monotone(256, 1024);
        }
        if b0 >= 128 {
            assert(b0 * p >= 128 * p) by (nonlinear_arith)
                requires
                    b0 >= 128,
            ;
            assert(modulus_in_range(n));
            assert(range_check(k, s[0]));
        } else {
            assert((b0 + 1) * p <= 128 * p) by (nonlinear_arith)
                requires
                    b0 <= 127,
            ;
            assert(!modulus_in_range(n));
            assert(!range_check(k, s[0]));
        }
    } else {
        lemma_pow256_monotone(k, 255);
        assert(n < pow256(255));
        assert(pow256(255) < 128 * pow256(255)) by (nonlinear_arith)
            requires
                pow256(255) >= 1,
        ;
        assert(!modulus_in_range(n));
        assert(!range_check(k, s[0]));
    }
}

// ---------------------------------------------------------------------
// I2OSP and OS2IP are inverse (§4.1, §4.2).
// ---------------------------------------------------------------------

/// `I2OSP(x, xLen)` for `x < 256^xLen` is an octet string of length `xLen`
/// whose `OS2IP` is `x`.
pub proof fn lemma_i2osp_os2ip(x: nat, x_len: nat)
    requires
        x < pow256(x_len),
    ensures
        i2osp(x, x_len) is Some,
        i2osp(x, x_len).unwrap().len() == x_len,
        os2ip(i2osp(x, x_len).unwrap()) == x,
    decreases x_len,
{
    lemma_pow256_zero();
    let z = i2osp(x, x_len).unwrap();
    if x_len == 0 {
        assert(z =~= Seq::<u8>::empty());
        assert(x == 0);
    } else {
        let k = x_len;
        let q = x / 256;
        lemma_pow256_succ((k - 1) as nat);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 256);
        assert(q < pow256((k - 1) as nat)) by (nonlinear_arith)
            requires
                x < 256 * pow256((k - 1) as nat),
                x == 256 * q + x % 256,
                x % 256 >= 0,
        ;
        lemma_i2osp_os2ip(q, (k - 1) as nat);
        let z2 = i2osp(q, (k - 1) as nat).unwrap();
        // z without its last octet is z2, and its last octet is x mod 256.
        assert forall|i: int| 0 <= i < k - 1 implies #[trigger] z.drop_last()[i] == z2[i] by {
            let e = (k - 2 - i) as nat;
            lemma_pow256_succ(e);
            assert((k - 1 - i) as nat == e + 1);
            lemma_pow256_pos(e);
            vstd::arithmetic::div_mod::lemma_div_denominator(x as int, 256, pow256(e) as int);
            assert(pow256((k - 1 - i) as nat) == 256 * pow256(e));
        }
        assert(z.drop_last() =~= z2);
        assert(z.last() == (x % 256) as u8) by {
            assert(z.last() == z[(k - 1) as int]);
            assert((k - 1 - (k - 1)) as nat == 0);
            assert(z[(k - 1) as int] == ((x / pow256(0)) % 256) as u8);
            assert(x / 1 == x);
        }
        lemma_os2ip_last(z);
        assert(os2ip(z) == 256 * q + x % 256);
    }
}

/// §4.1 and §4.2: `I2OSP(OS2IP(X), xLen)` is `X`.
pub proof fn lemma_os2ip_i2osp(x: Seq<u8>)
    ensures
        i2osp(os2ip(x), x.len()) == Some(x),
{
    lemma_os2ip_bound(x);
    lemma_i2osp_os2ip(os2ip(x), x.len());
    let z = i2osp(os2ip(x), x.len()).unwrap();
    lemma_os2ip_inj(z, x);
}

// ---------------------------------------------------------------------
// What the executable verify relies on.
// ---------------------------------------------------------------------

/// A modulus in range is greater than 1.
pub proof fn lemma_modulus_gt_one(n: nat)
    requires
        modulus_in_range(n),
    ensures
        n > 1,
{
    lemma_range_constants();
    assert(two_to(2047) >= 128) by (nonlinear_arith)
        requires
            two_to(2047) == 128 * pow256(255),
            pow256(255) >= 1,
    ;
}

/// `s^e mod n` is below `n`.
pub proof fn lemma_modpow_below(s: nat, e: nat, n: nat)
    requires
        n > 0,
    ensures
        modpow(s, e, n) < n,
{
    vstd::arithmetic::div_mod::lemma_mod_bound(vstd::arithmetic::power::pow(s as int, e), n as int);
}

/// When the signature has the modulus's length and its representative is
/// below `n`, and `em` is the encoded message of that length, the whole
/// of RSASSA-PKCS1-V1_5-VERIFY is the comparison `s^e mod n = OS2IP(EM)`.
pub proof fn lemma_verify_final(
    n: nat,
    e: nat,
    digest: Seq<u8>,
    h: HashId,
    sig: Seq<u8>,
    em: Seq<u8>,
)
    requires
        modulus_in_range(n),
        exponent_in_range(e),
        sig.len() == octet_len(n),
        os2ip(sig) < n,
        n < pow256(octet_len(n)),
        emsa_pkcs1_v1_5_encode(digest, octet_len(n), h) == Some(em),
        em.len() == octet_len(n),
    ensures
        rsassa_pkcs1_v1_5_verify(n, e, digest, h, sig) == (modpow(os2ip(sig), e, n) == os2ip(em)),
{
    let k = octet_len(n);
    lemma_modulus_gt_one(n);
    let m = modpow(os2ip(sig), e, n);
    lemma_modpow_below(os2ip(sig), e, n);
    lemma_i2osp_os2ip(m, k);
    let z = i2osp(m, k).unwrap();
    // z = EM' of the RFC. EM = EM' iff m = OS2IP(EM).
    if em == z {
        assert(os2ip(em) == m);
    }
    if os2ip(em) == m {
        lemma_os2ip_i2osp(em);
        assert(z == em);
    }
}

// ---------------------------------------------------------------------
// §9.2 Note 1: the DigestInfo prefixes.
// ---------------------------------------------------------------------

/// The three `DigestInfo` prefixes have the lengths §9.2 implies: the
/// prefix is 19 octets, so `T` is `19 + hLen` octets (51, 67 and 83); the
/// second octet of the prefix (the DER length of the outer SEQUENCE) is
/// `tLen - 2`, and the last (the length of the OCTET STRING) is `hLen`.
pub proof fn lemma_digest_info_prefix_lengths(h: HashId)
    ensures
        digest_info_prefix(h).len() == 19,
        hash_len(h) == 32 || hash_len(h) == 48 || hash_len(h) == 64,
        digest_info_prefix(h)[1] as nat + 2 == digest_info_prefix(h).len() + hash_len(h),
        digest_info_prefix(h)[18] as nat == hash_len(h),
        (digest_info_prefix(h) + Seq::new(hash_len(h), |i: int| 0u8)).len() == match h {
            HashId::Sha256 => 51nat,
            HashId::Sha384 => 67nat,
            HashId::Sha512 => 83nat,
        },
{
}

/// A successful encoding has the requested length, starts `00 01`, and
/// has at least eight `ff` octets of padding (§9.2 step 4's note).
pub proof fn lemma_encode_shape(digest: Seq<u8>, em_len: nat, h: HashId, em: Seq<u8>)
    requires
        emsa_pkcs1_v1_5_encode(digest, em_len, h) == Some(em),
    ensures
        em.len() == em_len,
        em[0] == 0,
        em[1] == 1,
        em_len >= digest_info_prefix(h).len() + hash_len(h) + 11,
        forall|i: int| 2 <= i < 10 ==> em[i] == 0xffu8,
{
    lemma_digest_info_prefix_lengths(h);
    let t = digest_info_prefix(h) + digest;
    let ps = Seq::new((em_len - t.len() - 3) as nat, |i: int| 0xffu8);
    assert(em == seq![0x00u8, 0x01u8] + ps + seq![0x00u8] + t);
    assert(em.len() == 2 + ps.len() + 1 + t.len());
    assert forall|i: int| 2 <= i < 10 implies em[i] == 0xffu8 by {
        assert(em[i] == ps[i - 2]);
    }
}

// ---------------------------------------------------------------------
// §8.2.2 rejects out-of-range representatives.
// ---------------------------------------------------------------------

/// A signature whose representative is at least `n` is rejected
/// (RSAVP1 step 1, §8.2.2 step 2.(c)).
pub proof fn lemma_signature_out_of_range_rejected(
    n: nat,
    e: nat,
    digest: Seq<u8>,
    h: HashId,
    signature: Seq<u8>,
)
    requires
        os2ip(signature) >= n,
    ensures
        !rsassa_pkcs1_v1_5_verify(n, e, digest, h, signature),
{
}

/// A signature of the wrong length is rejected (§8.2.2 step 1).
pub proof fn lemma_wrong_length_rejected(
    n: nat,
    e: nat,
    digest: Seq<u8>,
    h: HashId,
    signature: Seq<u8>,
)
    requires
        signature.len() != octet_len(n),
    ensures
        !rsassa_pkcs1_v1_5_verify(n, e, digest, h, signature),
{
}

// ---------------------------------------------------------------------
// The RFC's correctness claim: what the textbook signer produces verifies.
// ---------------------------------------------------------------------

/// RFC 8017 §8.2.1 RSASSA-PKCS1-V1_5-SIGN with the textbook RSASP1
/// (§5.2.1, `s = m^d mod n`), as a specification only (this crate never
/// signs): encode, convert, exponentiate, convert back.
pub open spec fn rsassa_pkcs1_v1_5_sign(n: nat, d: nat, digest: Seq<u8>, h: HashId) -> Option<Seq<u8>> {
    let k = octet_len(n);
    match emsa_pkcs1_v1_5_encode(digest, k, h) {
        None => None,
        Some(em) => {
            let m = os2ip(em);
            if m >= n {
                None
            } else {
                i2osp(modpow(m, d, n), k)
            }
        },
    }
}

/// `x^(1 + t lam) mod n = x mod n`, given `x^(lam + 1) mod n = x mod n`.
proof fn lemma_carmichael_power(x: nat, lam: nat, n: nat, t: nat)
    requires
        n > 0,
        vstd::arithmetic::power::pow(x as int, lam + 1) % (n as int) == (x as int) % (n as int),
    ensures
        vstd::arithmetic::power::pow(x as int, 1 + t * lam) % (n as int) == (x as int) % (n as int),
    decreases t,
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::power::*;
    if t == 0 {
        lemma_pow1(x as int);
    } else {
        let t1 = (t - 1) as nat;
        lemma_carmichael_power(x, lam, n, t1);
        assert(1 + t * lam == (1 + t1 * lam) + lam) by (nonlinear_arith)
            requires
                t == t1 + 1,
        ;
        lemma_pow_adds(x as int, 1 + t1 * lam, lam);
        lemma_pow_adds(x as int, 1, lam);
        lemma_pow1(x as int);
        let a = pow(x as int, 1 + t1 * lam);
        let b = pow(x as int, lam);
        // (a b) mod n = ((a mod n) b) mod n = ((x mod n) b) mod n = (x b)
        // mod n = x^(lam + 1) mod n = x mod n.
        lemma_mul_mod_noop_left(a, b, n as int);
        lemma_mul_mod_noop_left(x as int, b, n as int);
    }
}

/// RFC 8017's correctness claim for a signature the textbook signer
/// produces: if `n` is in range, `e d = 1 + t lam` where `lam` is a
/// Carmichael exponent of `n` (`x^(lam + 1) = x mod n` for every `x`, which
/// holds for `lam = lcm(p - 1, q - 1)` when `n = p q` for distinct primes
/// `p`, `q`, by Fermat's little theorem; this is a hypothesis here, not a
/// theorem), then the signature of `digest` verifies. This is the RFC's
/// correctness claim, not a security claim.
pub proof fn lemma_sign_verify(
    n: nat,
    e: nat,
    d: nat,
    lam: nat,
    t: nat,
    digest: Seq<u8>,
    h: HashId,
    sig: Seq<u8>,
)
    requires
        modulus_in_range(n),
        exponent_in_range(e),
        // e d = 1 + t lam: e d is congruent to 1 modulo lam.
        e * d == 1 + t * lam,
        // lam is a Carmichael exponent of n.
        forall|x: nat|
            #[trigger] vstd::arithmetic::power::pow(x as int, lam + 1) % (n as int) == (x as int) % (
            n as int),
        rsassa_pkcs1_v1_5_sign(n, d, digest, h) == Some(sig),
    ensures
        rsassa_pkcs1_v1_5_verify(n, e, digest, h, sig),
{
    use vstd::arithmetic::power::*;
    let k = octet_len(n);
    lemma_modulus_gt_one(n);
    lemma_octet_len_bounds(n);
    let em = emsa_pkcs1_v1_5_encode(digest, k, h).unwrap();
    lemma_encode_shape(digest, k, h, em);
    let m = os2ip(em);
    let s = modpow(m, d, n);
    lemma_modpow_below(m, d, n);
    lemma_i2osp_os2ip(s, k);
    // sig = I2OSP(s, k), so OS2IP(sig) = s < n.
    assert(n < pow256(k));
    assert(os2ip(sig) == s);
    assert(sig.len() == k);
    // (m^d mod n)^e mod n = m^(d e) mod n = m mod n = m.
    lemma_pow_mod_noop(pow(m as int, d), e, n as int);
    lemma_pow_multiplies(m as int, d, e);
    assert(d * e == 1 + t * lam) by (nonlinear_arith)
        requires
            e * d == 1 + t * lam,
    ;
    assert(vstd::arithmetic::power::pow(m as int, lam + 1) % (n as int) == (m as int) % (
    n as int));
    lemma_carmichael_power(m, lam, n, t);
    vstd::arithmetic::div_mod::lemma_small_mod(m, n);
    lemma_verify_final(n, e, digest, h, sig, em);
}

} // verus!
