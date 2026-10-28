//! Executable-style specification of RSA PKCS#1 v1.5 signature
//! verification, transcribed from RFC 8017, "PKCS #1: RSA Cryptography
//! Specifications Version 2.2" (K. Moriarty, B. Kaliski, J. Jonsson, A.
//! Rusch, November 2016, <https://www.rfc-editor.org/rfc/rfc8017>):
//! §4.1 I2OSP, §4.2 OS2IP, §5.2.2 RSAVP1, §8.2.2 RSASSA-PKCS1-V1_5-VERIFY
//! and §9.2 EMSA-PKCS1-v1_5-ENCODE with its Note 1. Nothing here runs; it
//! defines what "correct" means. Each `// N.` comment is the step number
//! of the algorithm being transcribed.
//!
//! This is public-key verification. The key, the message digest and the
//! signature are all public, so nothing here has a constant-time or
//! side-channel requirement, and none is claimed.
//!
//! Modelling choices (each one is a deliberate, listed deviation in form
//! or in domain):
//! - Integers are `nat`, octet strings are `Seq<u8>`. A failed step ("output
//!   'invalid signature' and stop", "integer too large", ...) is `None` or
//!   `false`.
//! - The modulus `n` is a `nat`. The RFC's `k`, "the length in octets of
//!   the RSA modulus n" (§8.2.2 step 1), is [`octet_len`], the length of
//!   `n` written without leading zero octets. Callers that hold `n` as an
//!   octet string (DER gives a sign octet) pass `os2ip` of it.
//! - The modulus must have 2048 to 8192 bits ([`modulus_in_range`]):
//!   anything else is "invalid signature". RFC 8017 allows other sizes
//!   (§3.1 only needs `n = p q`); this is a domain restriction of this
//!   verifier, not a step of the RFC.
//! - The public exponent `e` must satisfy `3 <= e <= 2^64 - 1`
//!   ([`exponent_in_range`]), else "invalid signature". RFC 8017 §3.1
//!   allows any `e` between 3 and `n - 1` with `gcd(e, lambda(n)) = 1`; the
//!   cap at 64 bits is a domain restriction (the executable code
//!   keeps `e` in a `u64`).
//! - §9.2 step 1 applies the hash function to the message. The digest is
//!   an input here (libcrux computes it, docs/phases/phase-3.md item 3.5f),
//!   so step 1 is "the digest has `hLen` octets": a digest of any other
//!   length is a caller error and gives "invalid signature". The step's
//!   "message too long" outcome belongs to the hash function and cannot
//!   occur.
//! - §9.2 step 2's DER encoding of `DigestInfo` is the fixed octet strings
//!   of Note 1, followed by the digest. They are written as literals; that
//!   they equal a DER encoding is item 3.5f's lemma, with 3.5a's encoder.
//! - §8.2.2 step 4 compares the two encoded messages as octet strings,
//!   with plain equality of sequences. Both are public, so no constant-time
//!   comparison is needed. It is the comparison of the *whole* encoded
//!   message, which is what makes a signature with garbage after the digest
//!   (Bleichenbacher's 2006 attack on lenient parsers) invalid.
//! - §8.2.2 does steps 1, 2 and 3 in this order; the result does not depend
//!   on the order, and the executable code is free to encode first.
//! - "Hash function" is the closed set SHA-256, SHA-384 and SHA-512
//!   ([`HashId`]); the other `DigestInfo` strings of Note 1 are not used.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `256^m`, by repeated squaring (so that evaluating it takes
/// `O(log m)` steps, which `examples.rs` needs for 2048-bit moduli).
/// `lemmas::lemma_pow256_is_pow` proves it equals `vstd`'s `pow(256, m)`.
pub open spec fn pow256(m: nat) -> nat
    decreases m,
{
    if m == 0 {
        1
    } else if m % 2 == 0 {
        pow256(m / 2) * pow256(m / 2)
    } else {
        256 * pow256((m - 1) as nat)
    }
}

/// `2^m`, by repeated squaring; `lemmas::lemma_two_to_is_pow2` proves it
/// equals `vstd`'s `pow2`.
pub open spec fn two_to(m: nat) -> nat
    decreases m,
{
    if m == 0 {
        1
    } else if m % 2 == 0 {
        two_to(m / 2) * two_to(m / 2)
    } else {
        2 * two_to((m - 1) as nat)
    }
}

// ---------------------------------------------------------------------
// The hash functions (§9.2, Note 1).
// ---------------------------------------------------------------------

/// The hash functions this verifier accepts (§9.2 Note 1 lists more).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HashId {
    /// SHA-256 (`hLen` = 32).
    Sha256,
    /// SHA-384 (`hLen` = 48).
    Sha384,
    /// SHA-512 (`hLen` = 64).
    Sha512,
}

/// `hLen`, the length in octets of the hash function's output.
pub open spec fn hash_len(h: HashId) -> nat {
    match h {
        HashId::Sha256 => 32,
        HashId::Sha384 => 48,
        HashId::Sha512 => 64,
    }
}

/// §9.2 Note 1, the DER encoding of the `DigestInfo` value without its
/// final octet string contents: "the first octets of T", to which the
/// digest `H` is appended.
///
/// ```text
/// SHA-256: (0x)30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20 || H
/// SHA-384: (0x)30 41 30 0d 06 09 60 86 48 01 65 03 04 02 02 05 00 04 30 || H
/// SHA-512: (0x)30 51 30 0d 06 09 60 86 48 01 65 03 04 02 03 05 00 04 40 || H
/// ```
pub open spec fn digest_info_prefix(h: HashId) -> Seq<u8> {
    match h {
        HashId::Sha256 => seq![
            0x30u8, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x01, 0x05, 0x00, 0x04, 0x20,
        ],
        HashId::Sha384 => seq![
            0x30u8, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x02, 0x05, 0x00, 0x04, 0x30,
        ],
        HashId::Sha512 => seq![
            0x30u8, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
            0x03, 0x05, 0x00, 0x04, 0x40,
        ],
    }
}

// ---------------------------------------------------------------------
// §4.2 OS2IP and §4.1 I2OSP.
// ---------------------------------------------------------------------

/// The partial sum `X_1 256^(xLen-1) + ... + X_m 256^(xLen-m)` of §4.2's
/// formula, over the first `m` octets of `x` (octet `X_i` is `x[i - 1]`).
pub open spec fn os2ip_sum(x: Seq<u8>, m: nat) -> nat
    decreases m,
{
    if m == 0 {
        0
    } else {
        os2ip_sum(x, (m - 1) as nat) + (x[(m - 1) as int] as nat) * pow256((x.len() - m) as nat)
    }
}

/// §4.2 OS2IP: "Convert an octet string to a nonnegative integer."
///
/// 1. "Let X_1 X_2 ... X_xLen be the octets of X from first to last, and
///    let x_(xLen-i) be the integer value of the octet X_i for
///    1 <= i <= xLen."
/// 2. "Let x = x_(xLen-1) 256^(xLen-1) + x_(xLen-2) 256^(xLen-2) + ... +
///    x_1 256 + x_0."
/// 3. "Output x."
pub open spec fn os2ip(x: Seq<u8>) -> nat {
    // 1.-3.
    os2ip_sum(x, x.len())
}

/// §4.1 I2OSP: "Convert a nonnegative integer to an octet string of a
/// specified length." `None` is "integer too large".
///
/// 1. "If x >= 256^xLen, output 'integer too large' and stop."
/// 2. "Write the integer x in its unique xLen-digit representation in base
///    256: x = x_(xLen-1) 256^(xLen-1) + ... + x_1 256 + x_0, where
///    0 <= x_i < 256 (note that one or more leading digits will be zero if
///    x is less than 256^(xLen-1))."
/// 3. "Let the octet X_i have the integer value x_(xLen-i) for
///    1 <= i <= xLen. Output the octet string X = X_1 X_2 ... X_xLen."
///
/// Octet `X_i` is `result[i - 1]`; digit `x_j` is `(x / 256^j) % 256`.
pub open spec fn i2osp(x: nat, x_len: nat) -> Option<Seq<u8>> {
    // 1.
    if x >= pow256(x_len) {
        None
    } else {
        // 2.-3.
        Some(
            Seq::new(
                x_len,
                |i: int| ((x / pow256((x_len - 1 - i) as nat)) % 256) as u8,
            ),
        )
    }
}

/// The length in octets of the shortest octet string that holds `x` (zero
/// octets for 0): the RFC's `k` for a modulus `x`.
pub open spec fn octet_len(x: nat) -> nat
    decreases x,
{
    if x == 0 {
        0
    } else {
        1 + octet_len(x / 256)
    }
}

// ---------------------------------------------------------------------
// §5.2.2 RSAVP1.
// ---------------------------------------------------------------------

/// `s^e mod n` as a `nat`, with `vstd`'s `pow`.
pub open spec fn modpow(s: nat, e: nat, n: nat) -> nat {
    (vstd::arithmetic::power::pow(s as int, e) % (n as int)) as nat
}

/// §5.2.2 RSAVP1: "RSA verification primitive." `None` is "signature
/// representative out of range".
///
/// 1. "If the signature representative s is not between 0 and n - 1,
///    output 'signature representative out of range' and stop."
/// 2. "Let m = s^e mod n."
/// 3. "Output m."
pub open spec fn rsavp1(n: nat, e: nat, s: nat) -> Option<nat> {
    // 1. (s is a nat, so "between 0 and n - 1" is "below n".)
    if s >= n {
        None
    } else {
        // 2.-3.
        Some(modpow(s, e, n))
    }
}

// ---------------------------------------------------------------------
// §9.2 EMSA-PKCS1-v1_5-ENCODE.
// ---------------------------------------------------------------------

/// §9.2 EMSA-PKCS1-v1_5-ENCODE, with the digest of the message as input.
/// `None` is "intended encoded message length too short" (or a digest that
/// is not `hLen` octets, see the header).
///
/// 1. "Apply the hash function to the message M to produce a hash value H"
///    (the digest is the input; modelling choice).
/// 2. "Encode the algorithm ID for the hash function and the hash value
///    into an ASN.1 value of type DigestInfo ... Let T be the DER encoding
///    of the DigestInfo value" (Note 1's prefix, then H).
/// 3. "If emLen < tLen + 11, output 'intended encoded message length too
///    short' and stop."
/// 4. "Generate an octet string PS consisting of emLen - tLen - 3 octets
///    with hexadecimal value 0xff. The length of PS will be at least 8
///    octets."
/// 5. "Concatenate PS, the DER encoding T, and other padding to form the
///    encoded message EM as EM = 0x00 || 0x01 || PS || 0x00 || T."
/// 6. "Output EM."
pub open spec fn emsa_pkcs1_v1_5_encode(digest: Seq<u8>, em_len: nat, h: HashId) -> Option<Seq<u8>> {
    // 1. (modelling choice: the digest is `hLen` octets)
    if digest.len() != hash_len(h) {
        None
    } else {
        // 2.
        let t = digest_info_prefix(h) + digest;
        let t_len = t.len();
        // 3.
        if em_len < t_len + 11 {
            None
        } else {
            // 4.
            let ps = Seq::new((em_len - t_len - 3) as nat, |i: int| 0xffu8);
            // 5.-6.
            Some(seq![0x00u8, 0x01u8] + ps + seq![0x00u8] + t)
        }
    }
}

// ---------------------------------------------------------------------
// §8.2.2 RSASSA-PKCS1-V1_5-VERIFY.
// ---------------------------------------------------------------------

/// Domain restriction (header): the modulus has 2048 to 8192 bits.
pub open spec fn modulus_in_range(n: nat) -> bool {
    two_to(2047) <= n < two_to(8192)
}

/// Domain restriction (header): `3 <= e <= 2^64 - 1`.
pub open spec fn exponent_in_range(e: nat) -> bool {
    3 <= e <= 0xFFFF_FFFF_FFFF_FFFFnat
}

/// §8.2.2 RSASSA-PKCS1-V1_5-VERIFY ((n, e), M, S): `true` is "valid
/// signature". `digest` is the hash of M (header); `n` is the modulus and
/// `e` the public exponent; `signature` is the octet string S. The
/// domain restrictions of the header, then the steps of the RFC
/// ([`rsassa_pkcs1_v1_5_verify_steps`]).
pub open spec fn rsassa_pkcs1_v1_5_verify(
    n: nat,
    e: nat,
    digest: Seq<u8>,
    h: HashId,
    signature: Seq<u8>,
) -> bool {
    // Domain restrictions (header): anything else is "invalid signature".
    if !modulus_in_range(n) || !exponent_in_range(e) {
        false
    } else {
        rsassa_pkcs1_v1_5_verify_steps(n, e, digest, h, signature)
    }
}

/// The steps of §8.2.2, for any modulus and exponent (the restrictions
/// of the header are in [`rsassa_pkcs1_v1_5_verify`]). Separate so that
/// each step can be exercised on a small key in the evaluated examples
/// (`examples.rs`).
pub open spec fn rsassa_pkcs1_v1_5_verify_steps(
    n: nat,
    e: nat,
    digest: Seq<u8>,
    h: HashId,
    signature: Seq<u8>,
) -> bool {
    // k is the length in octets of the RSA modulus n.
    let k = octet_len(n);
    // 1. "If the length of the signature S is not k octets, output
    //    'invalid signature' and stop."
    if signature.len() != k {
        false
    } else {
        // 2.(a) "Convert the signature S to an integer signature
        //        representative s: s = OS2IP (S)."
        let s = os2ip(signature);
        // 2.(b) "Apply the RSAVP1 verification primitive to the RSA
        //        public key (n, e) and the signature representative s
        //        to produce an integer message representative m:
        //        m = RSAVP1 ((n, e), s)."
        // 2.(c) "If RSAVP1 outputs 'signature representative out of
        //        range', output 'invalid signature' and stop."
        match rsavp1(n, e, s) {
            None => false,
            Some(m) => {
                // 2.(d) "Convert the message representative m to an
                //        encoded message EM' of length k octets:
                //        EM' = I2OSP (m, k)." "If I2OSP outputs
                //        'integer too large', output 'invalid
                //        signature' and stop."
                match i2osp(m, k) {
                    None => false,
                    Some(em_prime) => {
                        // 3. "Apply the EMSA-PKCS1-v1_5 encoding
                        //    operation to the message M to produce a
                        //    second encoded message EM of length k
                        //    octets: EM = EMSA-PKCS1-V1_5-ENCODE (M, k).
                        //    If the encoding operation outputs
                        //    'message too long' or 'intended encoded
                        //    message length too short', output
                        //    'invalid signature' and stop."
                        match emsa_pkcs1_v1_5_encode(digest, k, h) {
                            None => false,
                            // 4. "Compare the encoded message EM and
                            //    the second encoded message EM'. If
                            //    they are the same, output 'valid
                            //    signature'; otherwise, output
                            //    'invalid signature'."
                            Some(em) => em == em_prime,
                        }
                    },
                }
            },
        }
    }
}

} // verus!
