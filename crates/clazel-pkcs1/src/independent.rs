//! An independent transcription of PKCS #1 v1.5 signature verification
//! from a different document than [`super::spec`]: RFC 2313, "PKCS #1: RSA
//! Encryption Version 1.5" (B. Kaliski, RSA Laboratories, March 1998), the
//! original text of the padding and of verification, with the exponentiation
//! taken from Menezes, van Oorschot and Vanstone, *Handbook of Applied
//! Cryptography* (CRC Press, 1996), Algorithm 14.79 (left-to-right binary
//! exponentiation). It was written before this author re-read `spec.rs`
//! (docs/VERIFICATION.md, "Trust without reviewers", item 2). The same
//! agent wrote both files, so the two are independent in source document
//! and in order of writing only. The multiple-precision arithmetic's
//! counterpart is `bignum/independent.rs`.
//!
//! What RFC 2313 says that RFC 8017 does not, and the structural
//! difference this file exists to check:
//! - RFC 2313 *parses* the decrypted block (§8.1 formats and §9.4 parses an
//!   encryption block `EB = 00 || BT || PS || 00 || D`, with `BT = 01` and
//!   `PS` all `0xff` for a signature), takes `D` out, and compares `D` with
//!   the expected `DigestInfo` (§10.2). RFC 8017 §8.2.2 *builds* the
//!   expected block and compares the two blocks whole. [`eb_parse`] and
//!   [`lemma_parse_iff_format`] prove that, for a block of `k` octets, "the
//!   parse succeeds and yields `T`" is exactly "the block is the formatted
//!   block for `T`". This is where a lenient parser (accepting garbage
//!   after `D`, or a short or odd `PS`) would differ.
//! - RFC 2313 defines `k` by `256^(k-1) <= n < 256^k` (§6, key generation:
//!   "the length in octets of the modulus"), not by a function; and the
//!   conversions of §8.2 and §8.4 by sums over the octets with the first
//!   octet most significant.
//!
//! Modelling choices of this file (each stated, none an RFC 2313 step):
//! - The domain restrictions (2048 to 8192 bit modulus, `3 <= e < 2^64`,
//!   the digest has the hash's length, the three SHA-2 hashes) are restated
//!   from the task, not from RFC 2313, which predates them and knows only
//!   MD2 and MD5.
//! - RFC 2313 has no SHA-2 identifiers. The `DigestInfo` octet strings are
//!   re-entered here from RFC 3447 (PKCS #1 v2.1) §9.2 note 1, whose text
//!   RFC 8017 repeats; this file does not derive them from an encoding
//!   (that is item 3.5f's lemma with 3.5a's encoder).
//! - The RSA public operation (§9.2 with the public exponent: "RSA
//!   computation") requires its input to be below `n`; a representative
//!   that is not is a failed verification.
//! - §10.2 compares message digests: the digest is an input here, and
//!   "the digest in `D` equals the digest of the message" is `D = T`, the
//!   whole `DigestInfo` DER, compared as octets.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §8.2 octet-string-to-integer and §8.4 integer-to-octet-string.
// ---------------------------------------------------------------------

/// `256^m` by its recursive definition.
pub open spec fn p256(m: nat) -> nat
    decreases m,
{
    if m == 0 {
        1
    } else {
        256 * p256((m - 1) as nat)
    }
}

/// `2^m` by its recursive definition.
pub open spec fn p2(m: nat) -> nat
    decreases m,
{
    if m == 0 {
        1
    } else {
        2 * p2((m - 1) as nat)
    }
}

/// §8.2 (and §9.1): "x = sum over i of 2^(8 (k - i)) x_i", the first octet
/// the most significant. Written by peeling the first octet.
pub open spec fn os_to_int(x: Seq<u8>) -> nat
    decreases x.len(),
{
    if x.len() == 0 {
        0
    } else {
        (x[0] as nat) * p256((x.len() - 1) as nat) + os_to_int(x.skip(1))
    }
}

/// §8.4 (and §9.3): the `k`-octet string `Y` with
/// `y = sum over i of 2^(8 (k - i)) y_i`. Written by peeling the last
/// octet, which is `y mod 256`.
pub open spec fn int_to_os(y: nat, k: nat) -> Seq<u8>
    decreases k,
{
    if k == 0 {
        Seq::empty()
    } else {
        int_to_os(y / 256, (k - 1) as nat).push((y % 256) as u8)
    }
}

// ---------------------------------------------------------------------
// §8.1 encryption-block formatting and §9.4 parsing, block type 01.
// ---------------------------------------------------------------------

/// `n` octets of value 0xff (the padding string PS for block type 01).
pub open spec fn ff_run(n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        ff_run((n - 1) as nat).push(0xff)
    }
}

/// §8.1: "EB = 00 || BT || PS || 00 || D", `BT = 01`, with PS of
/// `k - 3 - len(D)` octets of 0xff. "The length of the data D shall not
/// be more than k - 11 octets" (so PS is at least eight octets).
pub open spec fn eb_format(k: nat, d: Seq<u8>) -> Option<Seq<u8>> {
    if d.len() + 11 > k {
        None
    } else {
        Some(seq![0x00u8, 0x01u8] + ff_run((k - 3 - d.len()) as nat) + seq![0x00u8] + d)
    }
}

/// The position of the first 0x00 octet of `eb` at or after `from`, or
/// `eb.len()` if there is none.
pub open spec fn first_zero(eb: Seq<u8>, from: nat) -> nat
    decreases eb.len() - from,
{
    if from >= eb.len() {
        eb.len()
    } else if eb[from as int] == 0 {
        from
    } else {
        first_zero(eb, from + 1)
    }
}

/// §9.4 encryption-block parsing, for a signature (block type 01): the
/// block is `00 || 01 || PS || 00 || D`; PS is the octets up to the first
/// 0x00 after the block type, all 0xff and at least eight; `D` is what
/// follows that 0x00. `None` is "decryption error".
pub open spec fn eb_parse(eb: Seq<u8>) -> Option<Seq<u8>> {
    if eb.len() < 11 || eb[0] != 0 || eb[1] != 1 {
        None
    } else {
        let j = first_zero(eb, 2);
        if j >= eb.len() || j < 2 + 8 || exists|i: int| 2 <= i < j && eb[i] != 0xffu8 {
            None
        } else {
            Some(eb.skip(j as int + 1))
        }
    }
}

// ---------------------------------------------------------------------
// HAC Algorithm 14.79 (left-to-right binary exponentiation).
// ---------------------------------------------------------------------

/// Algorithm 14.79, "INPUT: g in G and a positive integer e = (e_t e_(t-1)
/// ... e_1 e_0)_2 with e_t = 1. OUTPUT: g^e. 1. A <- 1. 2. For i from t
/// down to 0 do: 2.1 A <- A.A. 2.2 If e_i = 1, then A <- A.g. 3. Return
/// (A)." in the group of integers modulo `n` (every product reduced).
/// The loop over the bits from the most significant is the recursion on
/// `e / 2`: it reaches the leading bit first and the last step handles
/// `e_0`.
pub open spec fn hac_14_79(g: nat, e: nat, n: nat) -> nat
    decreases e,
{
    if e == 0 {
        // Zero bits: A = 1.
        1nat % n
    } else {
        // The steps for the higher bits, then 2.1 and 2.2 for e_0.
        let a = hac_14_79(g, e / 2, n);
        let squared = (a * a) % n;
        if e % 2 == 1 {
            (squared * g) % n
        } else {
            squared
        }
    }
}

// ---------------------------------------------------------------------
// The verification of §10.2, as RFC 2313 states it.
// ---------------------------------------------------------------------

/// The number of octets of the digest for each hash.
pub open spec fn digest_len(h: HashId) -> nat {
    match h {
        HashId::Sha256 => 32,
        HashId::Sha384 => 48,
        HashId::Sha512 => 64,
    }
}

/// The DER `DigestInfo` encoding of `digest` for `h` (RFC 3447 §9.2 note
/// 1; see the header).
pub open spec fn digest_info(h: HashId, digest: Seq<u8>) -> Seq<u8> {
    match h {
        HashId::Sha256 => seq![
            0x30u8, 0x31u8, 0x30u8, 0x0du8, 0x06u8, 0x09u8, 0x60u8, 0x86u8, 0x48u8, 0x01u8, 0x65u8,
            0x03u8, 0x04u8, 0x02u8, 0x01u8, 0x05u8, 0x00u8, 0x04u8, 0x20u8,
        ] + digest,
        HashId::Sha384 => seq![
            0x30u8, 0x41u8, 0x30u8, 0x0du8, 0x06u8, 0x09u8, 0x60u8, 0x86u8, 0x48u8, 0x01u8, 0x65u8,
            0x03u8, 0x04u8, 0x02u8, 0x02u8, 0x05u8, 0x00u8, 0x04u8, 0x30u8,
        ] + digest,
        HashId::Sha512 => seq![
            0x30u8, 0x51u8, 0x30u8, 0x0du8, 0x06u8, 0x09u8, 0x60u8, 0x86u8, 0x48u8, 0x01u8, 0x65u8,
            0x03u8, 0x04u8, 0x02u8, 0x03u8, 0x05u8, 0x00u8, 0x04u8, 0x40u8,
        ] + digest,
    }
}

/// §6: `k` is the length in octets of the modulus, `256^(k-1) <= n < 256^k`.
pub open spec fn modulus_len(n: nat) -> nat {
    choose|k: nat| k >= 1 && p256((k - 1) as nat) <= n && n < #[trigger] p256(k)
}

/// §10.2 verification of a signature `sig` of the (digest of the) message
/// under the public key `(n, e)`: "bit-string-to-octet-string conversion,
/// RSA decryption, data decoding, and message digesting and comparison".
pub open spec fn verify_rfc2313(n: nat, e: nat, digest: Seq<u8>, h: HashId, sig: Seq<u8>) -> bool {
    // The domain restrictions of the task (header).
    if !(p2(2047) <= n && n < p2(8192)) || !(3 <= e && e < p2(64)) || digest.len() != digest_len(h) {
        false
    } else {
        let k = modulus_len(n);
        // Bit-string to octet string: the signature must be k octets.
        if sig.len() != k {
            false
        } else {
            // §9.1 octet-string-to-integer, §9.2 RSA computation (the
            // integer must be below n).
            let s = os_to_int(sig);
            if s >= n {
                false
            } else {
                let m = hac_14_79(s, e, n);
                // §9.3 integer-to-octet-string.
                let eb = int_to_os(m, k);
                // §9.4 encryption-block parsing, then §10.2's comparison of
                // the parsed data D with the DigestInfo of the digest.
                match eb_parse(eb) {
                    None => false,
                    Some(d) => d == digest_info(h, digest),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// Lemmas: this file equals `spec.rs`.
// ---------------------------------------------------------------------

/// `p256` is `256^m`.
pub proof fn lemma_p256_is_pow256(m: nat)
    ensures
        p256(m) == pow256(m),
    decreases m,
{
    if m == 0 {
        crate::lemmas::lemma_pow256_zero();
    } else {
        lemma_p256_is_pow256((m - 1) as nat);
        crate::lemmas::lemma_pow256_succ((m - 1) as nat);
    }
}

/// `p2` is `2^m`.
pub proof fn lemma_p2_is_two_to(m: nat)
    ensures
        p2(m) == two_to(m),
    decreases m,
{
    if m == 0 {
    } else {
        lemma_p2_is_two_to((m - 1) as nat);
        crate::lemmas::lemma_two_to_succ((m - 1) as nat);
    }
}

/// Horner's rule for the first-octet form: appending an octet.
proof fn lemma_os_to_int_push(s: Seq<u8>, b: u8)
    ensures
        os_to_int(s.push(b)) == os_to_int(s) * 256 + b as nat,
    decreases s.len(),
{
    let t = s.push(b);
    if s.len() == 0 {
        assert(t.len() == 1);
        assert(t.skip(1) =~= Seq::<u8>::empty());
        assert(t[0] == b);
        assert(p256(0) == 1);
        assert(s =~= Seq::<u8>::empty());
        assert(os_to_int(s) == 0);
        assert(os_to_int(t) == (t[0] as nat) * p256(0) + os_to_int(t.skip(1)));
        assert((b as nat) * p256(0) == b as nat) by (nonlinear_arith)
            requires
                p256(0) == 1,
        ;
    } else {
        assert(t.skip(1) =~= s.skip(1).push(b));
        lemma_os_to_int_push(s.skip(1), b);
        assert(t[0] == s[0]);
        assert(t.len() - 1 == s.len());
        let w = (s[0] as nat);
        // p256(len) = 256 p256(len - 1).
        assert(p256(s.len()) == 256 * p256((s.len() - 1) as nat));
        assert(os_to_int(t) == (t[0] as nat) * p256((t.len() - 1) as nat) + os_to_int(t.skip(1)));
        assert(os_to_int(s) == (s[0] as nat) * p256((s.len() - 1) as nat) + os_to_int(s.skip(1)));
        assert(w * p256(s.len()) + (os_to_int(s.skip(1)) * 256 + b as nat) == (w * p256((s.len() - 1) as nat)
            + os_to_int(s.skip(1))) * 256 + b as nat) by (nonlinear_arith)
            requires
                p256(s.len()) == 256 * p256((s.len() - 1) as nat),
        ;
    }
}

/// §8.2 equals RFC 8017 §4.2: both read the first octet as the most
/// significant.
pub proof fn lemma_os_to_int_is_os2ip(x: Seq<u8>)
    ensures
        os_to_int(x) == os2ip(x),
    decreases x.len(),
{
    if x.len() > 0 {
        let d = x.drop_last();
        lemma_os_to_int_is_os2ip(d);
        assert(d.push(x.last()) =~= x);
        lemma_os_to_int_push(d, x.last());
        crate::lemmas::lemma_os2ip_last(x);
    }
}

/// §8.4's `Y` for `y < 256^k` has `OS2IP(Y) = y`.
proof fn lemma_int_to_os_value(y: nat, k: nat)
    requires
        y < p256(k),
    ensures
        int_to_os(y, k).len() == k,
        os_to_int(int_to_os(y, k)) == y,
    decreases k,
{
    if k > 0 {
        let q = y / 256;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y as int, 256);
        assert(q < p256((k - 1) as nat)) by (nonlinear_arith)
            requires
                y < 256 * p256((k - 1) as nat),
                y == 256 * q + y % 256,
        ;
        lemma_int_to_os_value(q, (k - 1) as nat);
        lemma_os_to_int_push(int_to_os(q, (k - 1) as nat), (y % 256) as u8);
    } else {
        assert(y == 0);
    }
}

/// §8.4's conversion equals RFC 8017's I2OSP where both are defined.
pub proof fn lemma_int_to_os_is_i2osp(y: nat, k: nat)
    requires
        y < pow256(k),
    ensures
        i2osp(y, k) == Some(int_to_os(y, k)),
{
    lemma_p256_is_pow256(k);
    lemma_int_to_os_value(y, k);
    crate::lemmas::lemma_i2osp_os2ip(y, k);
    let z = i2osp(y, k).unwrap();
    lemma_os_to_int_is_os2ip(int_to_os(y, k));
    crate::lemmas::lemma_os2ip_inj(z, int_to_os(y, k));
}

/// Algorithm 14.79 computes `g^e mod n`.
pub proof fn lemma_hac_14_79_is_modpow(g: nat, e: nat, n: nat)
    requires
        n > 0,
    ensures
        hac_14_79(g, e, n) == modpow(g, e, n),
    decreases e,
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::mul::*;
    use vstd::arithmetic::power::*;
    if e == 0 {
        lemma_pow0(g as int);
        assert(modpow(g, 0, n) == 1nat % n);
    } else {
        let m = e / 2;
        lemma_hac_14_79_is_modpow(g, m, n);
        let a = hac_14_79(g, m, n);
        // a = g^m mod n. e = 2 m + bit; g^e = (g^m)^2 g^bit.
        lemma_pow_adds(g as int, 2 * m, (e % 2) as nat);
        lemma_pow_multiplies(g as int, m, 2);
        lemma_square_is_pow2(pow(g as int, m));
        lemma_pow_multiplies(g as int, 2, m);
        let gm = pow(g as int, m);
        assert(pow(g as int, 2 * m) == gm * gm) by {
            assert(2 * m == m * 2);
        }
        // (a a) mod n = (g^m g^m) mod n.
        lemma_mul_mod_noop(gm, gm, n as int);
        assert(a == gm % (n as int));
        assert((a * a) % n == (gm * gm) % (n as int));
        if e % 2 == 1 {
            lemma_pow1(g as int);
            assert(pow(g as int, e) == gm * gm * g);
            lemma_mul_mod_noop_left(gm * gm, g as int, n as int);
            lemma_mul_mod_noop_left((a * a) as int, g as int, n as int);
            lemma_mod_twice((gm * gm) as int, n as int);
        } else {
            lemma_pow0(g as int);
            assert(pow(g as int, e) == gm * gm);
        }
    }
}

/// The octets of `n`'s length: `modulus_len` is the RFC 8017 `k`.
pub proof fn lemma_modulus_len_is_octet_len(n: nat)
    requires
        n > 0,
    ensures
        modulus_len(n) == octet_len(n),
{
    crate::lemmas::lemma_octet_len_bounds(n);
    let k = octet_len(n);
    lemma_p256_is_pow256(k);
    lemma_p256_is_pow256((k - 1) as nat);
    assert(k >= 1) by {
        if k == 0 {
            assert(n < pow256(0));
            crate::lemmas::lemma_pow256_zero();
        }
    }
    // k witnesses the `choose`; any other witness k2 has the same bounds,
    // and 256^m is strictly increasing, so k2 = k.
    let k2 = modulus_len(n);
    assert(k2 >= 1 && p256((k2 - 1) as nat) <= n && n < p256(k2));
    lemma_p256_is_pow256(k2);
    lemma_p256_is_pow256((k2 - 1) as nat);
    if k2 < k {
        crate::lemmas::lemma_pow256_monotone(k2, (k - 1) as nat);
    }
    if k < k2 {
        crate::lemmas::lemma_pow256_monotone(k, (k2 - 1) as nat);
    }
}

/// `ff_run` is the RFC 8017 padding string.
proof fn lemma_ff_run_is_seq_new(n: nat)
    ensures
        ff_run(n) =~= Seq::new(n, |i: int| 0xffu8),
    decreases n,
{
    if n > 0 {
        lemma_ff_run_is_seq_new((n - 1) as nat);
        assert(Seq::new(n, |i: int| 0xffu8) =~= Seq::new((n - 1) as nat, |i: int| 0xffu8).push(0xffu8));
    }
}

/// `first_zero` finds a zero, and nothing before it is zero.
proof fn lemma_first_zero_props(eb: Seq<u8>, from: nat)
    ensures
        from <= first_zero(eb, from) || from >= eb.len(),
        first_zero(eb, from) <= eb.len() || from >= eb.len(),
        forall|i: int| from <= i < first_zero(eb, from) ==> eb[i] != 0,
        first_zero(eb, from) < eb.len() ==> eb[first_zero(eb, from) as int] == 0,
    decreases eb.len() - from,
{
    if from < eb.len() && eb[from as int] != 0 {
        lemma_first_zero_props(eb, from + 1);
    }
}

/// The formatted block has the stated shape; this is §8.1 as a sequence.
proof fn lemma_eb_format_shape(k: nat, d: Seq<u8>, eb: Seq<u8>)
    requires
        eb_format(k, d) == Some(eb),
    ensures
        eb.len() == k,
        eb[0] == 0,
        eb[1] == 1,
        forall|i: int| 2 <= i < k - 1 - d.len() ==> eb[i] == 0xffu8,
        eb[(k - 1 - d.len()) as int] == 0,
        eb.skip((k - d.len()) as int) =~= d,
{
    lemma_ff_run_is_seq_new((k - 3 - d.len()) as nat);
    let ps = ff_run((k - 3 - d.len()) as nat);
    assert(eb == seq![0x00u8, 0x01u8] + ps + seq![0x00u8] + d);
    assert(eb.len() == 2 + ps.len() + 1 + d.len());
    assert forall|i: int| 2 <= i < k - 1 - d.len() implies eb[i] == 0xffu8 by {
        assert(eb[i] == ps[i - 2]);
    }
}

/// §9.4 parsing a block of `k` octets succeeds with `T` exactly when the
/// block is §8.1's formatting of `T` for `k`.
pub proof fn lemma_parse_iff_format(eb: Seq<u8>, k: nat, t: Seq<u8>)
    requires
        eb.len() == k,
    ensures
        (eb_parse(eb) == Some(t)) == (eb_format(k, t) == Some(eb)),
{
    lemma_first_zero_props(eb, 2);
    if eb_format(k, t) == Some(eb) {
        // The formatted block parses back to t.
        lemma_eb_format_shape(k, t, eb);
        let j = (k - 1 - t.len()) as nat;
        // Positions 2..j are 0xff (nonzero) and position j is 0: the first
        // zero at or after 2 is j.
        assert(k >= 11);
        assert(first_zero(eb, 2) == j) by {
            lemma_first_zero_is(eb, 2, j);
        }
        assert(eb_parse(eb) == Some(t));
    }
    if eb_parse(eb) == Some(t) {
        // Parsing succeeded: eb = 00 01 ff.. 00 t.
        let j = first_zero(eb, 2);
        assert(eb.len() >= 11 && eb[0] == 0 && eb[1] == 1);
        assert(j < eb.len() && j >= 10);
        assert(forall|i: int| 2 <= i < j ==> eb[i] == 0xffu8);
        assert(eb.skip(j as int + 1) == t);
        assert(t.len() == k - j - 1);
        assert(k >= t.len() + 11);
        assert(eb_format(k, t) is Some);
        lemma_eb_format_shape(k, t, eb_format(k, t).unwrap());
        let f = eb_format(k, t).unwrap();
        assert(j == k - 1 - t.len());
        assert(f =~= eb) by {
            assert forall|i: int| 0 <= i < k implies f[i] == eb[i] by {
                if i >= j as int + 1 {
                    assert(f.skip(j as int + 1)[i - j as int - 1] == t[i - j as int - 1]);
                    assert(eb.skip(j as int + 1)[i - j as int - 1] == t[i - j as int - 1]);
                }
            }
        }
    }
}

/// Helper: `first_zero` is `j` when everything in `from..j` is nonzero and
/// position `j` is zero.
proof fn lemma_first_zero_is(eb: Seq<u8>, from: nat, j: nat)
    requires
        from <= j < eb.len(),
        forall|i: int| from <= i < j ==> eb[i] != 0,
        eb[j as int] == 0,
    ensures
        first_zero(eb, from) == j,
    decreases j - from,
{
    if from < j {
        lemma_first_zero_is(eb, from + 1, j);
    }
}

/// `eb_format` equals RFC 8017 §9.2: for `T = DigestInfo`, the block that
/// the formatting gives is the encoded message `EM`, and it exists
/// exactly when the encoding does.
pub proof fn lemma_format_is_emsa(digest: Seq<u8>, k: nat, h: HashId)
    requires
        digest.len() == hash_len(h),
    ensures
        eb_format(k, digest_info(h, digest)) == emsa_pkcs1_v1_5_encode(digest, k, h),
{
    let t = digest_info(h, digest);
    assert(t == digest_info_prefix(h) + digest) by {
        match h {
            HashId::Sha256 => {},
            HashId::Sha384 => {},
            HashId::Sha512 => {},
        }
    }
    if k >= t.len() + 11 {
        lemma_ff_run_is_seq_new((k - 3 - t.len()) as nat);
        assert(eb_format(k, t) =~= emsa_pkcs1_v1_5_encode(digest, k, h));
    }
}

/// The three `digest_len`s equal `hash_len`.
proof fn lemma_digest_len_is_hash_len(h: HashId)
    ensures
        digest_len(h) == hash_len(h),
{
}

/// **This file equals `spec.rs`**: RFC 2313's parse-and-compare
/// verification, with HAC 14.79 for the exponentiation, accepts exactly
/// what RFC 8017's encode-and-compare verification accepts, on every
/// input in the domain.
pub proof fn lemma_independent_equals_spec(
    n: nat,
    e: nat,
    digest: Seq<u8>,
    h: HashId,
    sig: Seq<u8>,
)
    ensures
        verify_rfc2313(n, e, digest, h, sig) == rsassa_pkcs1_v1_5_verify(n, e, digest, h, sig),
{
    lemma_p2_is_two_to(2047);
    lemma_p2_is_two_to(8192);
    lemma_p2_is_two_to(64);
    lemma_digest_len_is_hash_len(h);
    assert(exponent_in_range(e) == (3 <= e && e < p2(64))) by {
        crate::lemmas::lemma_two_to_64();
    }
    if modulus_in_range(n) && exponent_in_range(e) && digest.len() == hash_len(h) {
        crate::lemmas::lemma_modulus_gt_one(n);
        lemma_modulus_len_is_octet_len(n);
        if sig.len() == octet_len(n) {
            lemma_os_to_int_is_os2ip(sig);
            if os2ip(sig) < n {
                lemma_equal_for_representative(n, e, digest, h, sig);
            }
        }
    }
}

/// [`lemma_independent_equals_spec`] where both texts reach their final
/// comparison: the key and digest are in range, the signature has the
/// modulus's length, and its representative is below the modulus. A
/// helper of its own so that each proof stays within Verus's default
/// resource limit on Linux CI, as `clazel-base64`'s encoder does.
proof fn lemma_equal_for_representative(n: nat, e: nat, digest: Seq<u8>, h: HashId, sig: Seq<u8>)
    requires
        modulus_in_range(n),
        exponent_in_range(e),
        digest.len() == hash_len(h),
        sig.len() == octet_len(n),
        os2ip(sig) < n,
    ensures
        verify_rfc2313(n, e, digest, h, sig) == rsassa_pkcs1_v1_5_verify(n, e, digest, h, sig),
{
    lemma_p2_is_two_to(2047);
    lemma_p2_is_two_to(8192);
    lemma_p2_is_two_to(64);
    lemma_digest_len_is_hash_len(h);
    assert(exponent_in_range(e) == (3 <= e && e < p2(64))) by {
        crate::lemmas::lemma_two_to_64();
    }
    crate::lemmas::lemma_modulus_gt_one(n);
    lemma_modulus_len_is_octet_len(n);
    let k = octet_len(n);
    lemma_os_to_int_is_os2ip(sig);
    let s = os2ip(sig);
    lemma_hac_14_79_is_modpow(s, e, n);
    let m = modpow(s, e, n);
    crate::lemmas::lemma_modpow_below(s, e, n);
    crate::lemmas::lemma_octet_len_bounds(n);
    lemma_p256_is_pow256(k);
    lemma_int_to_os_is_i2osp(m, k);
    let eb = int_to_os(m, k);
    lemma_int_to_os_value(m, k);
    lemma_parse_iff_format(eb, k, digest_info(h, digest));
    lemma_format_is_emsa(digest, k, h);
}

} // verus!
