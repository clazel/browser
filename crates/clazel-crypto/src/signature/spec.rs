//! RFC 8446 §4.4.3: verify a CertificateVerify signature with the
//! end-entity key, for the signature schemes this client offers (§4.2.3).
//!
//! Sources, by step:
//! - RFC 8446 §4.2.3, SignatureScheme: ecdsa_secp256r1_sha256 (0x0403),
//!   rsa_pss_rsae_sha256/384/512 (0x0804-0x0806) and ed25519 (0x0807).
//!   <https://www.rfc-editor.org/rfc/rfc8446#section-4.2.3>
//! - RFC 5480 §2.1.1 (id-ecPublicKey, namedCurve secp256r1) and §2.2 (the
//!   ECPoint), <https://www.rfc-editor.org/rfc/rfc5480#section-2>; RFC 3279
//!   §2.2.3 (Ecdsa-Sig-Value), <https://www.rfc-editor.org/rfc/rfc3279#section-2.2.3>.
//! - RFC 3279 §2.3.1 and RFC 8017 Appendix A.1.1 (rsaEncryption keys), via
//!   `clazel_x509::spki`; RFC 8017 §8.1.2 RSASSA-PSS-VERIFY, with RFC 8446
//!   §4.2.3's MGF1 over the same hash and a salt as long as the digest.
//! - RFC 8410 §3 and §4 (id-Ed25519 keys); RFC 8032 §5.1.2 (point
//!   encoding) and §5.1.7 (verification). The small-order points are those
//!   of Chalkias, Garillot and Nikolaenko, "Taming the many EdDSAs" (2020),
//!   <https://eprint.iacr.org/2020/1244>.
//!
//! Modelling choices:
//! - `key` is the end-entity certificate's complete DER
//!   SubjectPublicKeyInfo, the value chain validation hands to the signature
//!   check. It is parsed with `clazel_x509::spki`, our own decoder.
//! - ECDSA: only id-ecPublicKey with the namedCurve secp256r1 parameter
//!   (RFC 5480 §2.1.1.1; explicit curve parameters are refused) and only the
//!   uncompressed point 0x04 || X || Y (RFC 5480 §2.2 requires support for
//!   it; the compressed form is optional and refused). Since the key
//!   classification moved into `clazel_x509::spki` (so that certificate
//!   path validation and CertificateVerify share one key decoder),
//!   `p256_point` reads the `EcP256` class that `parse_subject_public_key_info`
//!   returns. `p256_point_direct` is the earlier definition, straight from
//!   the key's fields; it is not used by `verify`, and
//!   `lemmas::lemma_p256_point_unchanged` proves `p256_point` equal to it on
//!   every parsed key, so the meaning of `verify` is unchanged. The signature is one
//!   DER Ecdsa-Sig-Value with nothing after it; r and s are non-negative
//!   DER INTEGERs of at most 32 magnitude octets, left-padded to 32. Their
//!   range 1..n-1 and the point's validity are checked by libcrux.
//! - RSA-PSS (rsae): only rsaEncryption keys, as RFC 8446 §4.2.3 requires
//!   for the rsae schemes. The public exponent must be 65537, the only one
//!   libcrux-rsa 0.0.9 verifies with, and the modulus must be exactly 2048,
//!   3072, 4096, 6144 or 8192 bits (its first octet has the top bit set),
//!   the only sizes it accepts. The signature is as long as the modulus.
//!   Keys outside this profile are refused, never verified with another
//!   exponent.
//! - rsa_pss_pss_* (0x0809-0x080b) are neither offered nor verified (see
//!   `clazel_tls::hello::client_spec`).
//! - Ed25519: id-Ed25519 with absent parameters (RFC 8410 §3), a 32-octet
//!   key in a BIT STRING with no unused bits, and a 64-octet signature.
//!   A key of small order is refused, which RFC 8032 §5.1.7 does not
//!   require: under the identity key, R = identity and S = 0 verify for
//!   every message. Small order means the key's y-coordinate (its low 255
//!   bits, RFC 8032 §5.1.2) is one of the five that edwards25519's eight
//!   points of order dividing 8 have, or p or p + 1, which libcrux refuses
//!   as non-canonical but which are refused here too. Mixed-order keys
//!   (a large-order point plus a small-order one) are not refused: they do
//!   not let one signature verify every message.
//! - Any other scheme, key type or malformed input is `false`.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The SHA-2 function an RSA-PSS scheme uses for its digest and for MGF1.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Hash {
    /// SHA-256 (rsa_pss_rsae_sha256).
    Sha256,
    /// SHA-384 (rsa_pss_rsae_sha384).
    Sha384,
    /// SHA-512 (rsa_pss_rsae_sha512).
    Sha512,
}

/// The digest length of `hash`, which RFC 8446 §4.2.3 also makes the salt length.
pub open spec fn hash_len(hash: Hash) -> nat {
    match hash {
        Hash::Sha256 => 32,
        Hash::Sha384 => 48,
        Hash::Sha512 => 64,
    }
}

/// ECDSA P-256 with SHA-256 of `message` (FIPS 186-5 §6.4.2): `r` and `s`
/// are 32 octets, `point` is X || Y (64 octets). Uninterpreted: libcrux's.
pub uninterp spec fn ecdsa_p256_sha256_verify(message: Seq<u8>, r: Seq<u8>, s: Seq<u8>,
    point: Seq<u8>) -> bool;

/// RSASSA-PSS-VERIFY (RFC 8017 §8.1.2) with public exponent 65537, MGF1
/// over `hash` and the given salt length. Uninterpreted: libcrux's.
pub uninterp spec fn rsa_pss_verify(hash: Hash, modulus: Seq<u8>, message: Seq<u8>,
    salt_len: nat, signature: Seq<u8>) -> bool;

/// Ed25519 verification (RFC 8032 §5.1.7) of `message` under the 32-octet
/// `key`. Uninterpreted: libcrux's.
pub uninterp spec fn ed25519_verify(message: Seq<u8>, key: Seq<u8>, signature: Seq<u8>) -> bool;

/// id-ecPublicKey, 1.2.840.10045.2.1 (RFC 5480 §2.1.1).
pub open spec fn is_ec_public_key(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat]
}

/// The DER of the namedCurve parameter secp256r1, OBJECT IDENTIFIER
/// 1.2.840.10045.3.1.7 (RFC 5480 §2.1.1.1).
pub open spec fn secp256r1_parameter() -> Seq<u8> {
    seq![0x06u8, 0x08u8, 0x2au8, 0x86u8, 0x48u8, 0xceu8, 0x3du8, 0x03u8, 0x01u8, 0x07u8]
}

/// id-Ed25519, 1.3.101.112 (RFC 8410 §3).
pub open spec fn is_ed25519(oid: Seq<nat>) -> bool {
    oid =~= seq![1nat, 3nat, 101nat, 112nat]
}

/// `m` left-padded with zero octets to 32 octets (`m` is at most 32).
pub open spec fn pad32(m: Seq<u8>) -> Seq<u8> {
    Seq::new((32 - m.len()) as nat, |i: int| 0u8) + m
}

/// RFC 5480 §2.2: the X || Y of a secp256r1 key in uncompressed form, as
/// classified by `clazel_x509::spki` (RFC 5480 §2.1.1, §2.2).
pub open spec fn p256_point(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo) -> Option<Seq<u8>> {
    match spki.public_key {
        clazel_x509::spki::spec::PublicKey::EcP256(point) => Some(point),
        _ => None,
    }
}

/// Lemma-only: `p256_point` as it was before the classification moved into
/// `clazel_x509::spki`, read straight from the key's fields. Not used by
/// `verify`; see `lemmas::lemma_p256_point_unchanged`.
pub open spec fn p256_point_direct(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo) -> Option<Seq<u8>> {
    let bits = spki.subject_public_key_bits;
    if is_ec_public_key(spki.algorithm.oid)
        && spki.algorithm.parameters_der == Some(secp256r1_parameter())
        && spki.subject_public_key_unused_bits == 0
        && bits.len() == 65 && bits[0] == 0x04u8 {
        Some(bits.subrange(1, 65))
    } else {
        None
    }
}

/// RFC 3279 §2.2.3: r and s of exactly one DER Ecdsa-Sig-Value, each a
/// non-negative INTEGER of at most 32 magnitude octets, padded to 32.
pub open spec fn ecdsa_sig_value(signature: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    match clazel_der::spec::expect_sequence(signature, 0, signature.len()) {
        Some((cs, ce)) if ce == signature.len() =>
            match clazel_der::spec::read_integer(signature, cs, ce) {
                Some((r_negative, rs, re, after_r)) if !r_negative && re - rs <= 32 =>
                    match clazel_der::spec::read_integer(signature, after_r, ce) {
                        Some((s_negative, ss, se, after_s)) if !s_negative && se - ss <= 32 && after_s == ce =>
                            Some((pad32(signature.subrange(rs as int, re as int)),
                                pad32(signature.subrange(ss as int, se as int)))),
                        _ => None,
                    },
                _ => None,
            },
        _ => None,
    }
}

/// ecdsa_secp256r1_sha256 (0x0403).
pub open spec fn ecdsa_p256_sha256(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo,
    input: Seq<u8>, signature: Seq<u8>) -> bool {
    match (p256_point(spki), ecdsa_sig_value(signature)) {
        (Some(point), Some((r, s))) => ecdsa_p256_sha256_verify(input, r, s, point),
        _ => false,
    }
}

/// The RSA modulus sizes libcrux-rsa accepts, with the top bit of the
/// first octet set so the bit length is exactly 8 times the octet length.
pub open spec fn modulus_ok(n: Seq<u8>) -> bool {
    (n.len() == 256 || n.len() == 384 || n.len() == 512 || n.len() == 768 || n.len() == 1024)
        && n[0] >= 0x80u8
}

/// rsa_pss_rsae_sha256/384/512 (0x0804-0x0806).
pub open spec fn rsa_pss_rsae(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo, hash: Hash,
    input: Seq<u8>, signature: Seq<u8>) -> bool {
    match spki.public_key {
        clazel_x509::spki::spec::PublicKey::Rsa(key) =>
            key.public_exponent_octets =~= seq![0x01u8, 0x00u8, 0x01u8]
                && modulus_ok(key.modulus_octets)
                && signature.len() == key.modulus_octets.len()
                && rsa_pss_verify(hash, key.modulus_octets, input, hash_len(hash), signature),
        _ => false,
    }
}

/// The y-coordinates, as 32 little-endian octets with the sign bit clear,
/// of edwards25519's points of order 1, 2, 4 and 8, and the two values
/// at or above p that reduce to one of them.
pub open spec fn small_order_y() -> Seq<Seq<u8>> {
    seq![
        // 0: (sqrt(-1), 0) and (-sqrt(-1), 0), order 4
        seq![
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
        ],
        // 1: the identity (0, 1), order 1
        seq![
            0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
            0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
        ],
        // p - 1: (0, -1), order 2
        seq![
            0xecu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x7fu8,
        ],
        // two of the order-8 points
        seq![
            0x26u8, 0xe8u8, 0x95u8, 0x8fu8, 0xc2u8, 0xb2u8, 0x27u8, 0xb0u8,
            0x45u8, 0xc3u8, 0xf4u8, 0x89u8, 0xf2u8, 0xefu8, 0x98u8, 0xf0u8,
            0xd5u8, 0xdfu8, 0xacu8, 0x05u8, 0xd3u8, 0xc6u8, 0x33u8, 0x39u8,
            0xb1u8, 0x38u8, 0x02u8, 0x88u8, 0x6du8, 0x53u8, 0xfcu8, 0x05u8,
        ],
        // the other two order-8 points
        seq![
            0xc7u8, 0x17u8, 0x6au8, 0x70u8, 0x3du8, 0x4du8, 0xd8u8, 0x4fu8,
            0xbau8, 0x3cu8, 0x0bu8, 0x76u8, 0x0du8, 0x10u8, 0x67u8, 0x0fu8,
            0x2au8, 0x20u8, 0x53u8, 0xfau8, 0x2cu8, 0x39u8, 0xccu8, 0xc6u8,
            0x4eu8, 0xc7u8, 0xfdu8, 0x77u8, 0x92u8, 0xacu8, 0x03u8, 0x7au8,
        ],
        // p: a non-canonical encoding of 0
        seq![
            0xedu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x7fu8,
        ],
        // p + 1: a non-canonical encoding of 1
        seq![
            0xeeu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
            0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x7fu8,
        ],
    ]
}

/// Whether the encoded point `key` (RFC 8032 §5.1.2), ignoring its x sign
/// bit (bit 7 of the last octet), has y-coordinate `y`.
pub open spec fn same_y(key: Seq<u8>, y: Seq<u8>) -> bool {
    key.len() == 32 && y.len() == 32
        && key.subrange(0, 31) =~= y.subrange(0, 31)
        && key[31] & 0x7fu8 == y[31]
}

/// Whether `key` encodes a point of small order (see the modelling choices).
pub open spec fn is_small_order(key: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < small_order_y().len() && #[trigger] same_y(key, small_order_y()[i])
}

/// ed25519 (0x0807).
pub open spec fn ed25519(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo, input: Seq<u8>,
    signature: Seq<u8>) -> bool {
    is_ed25519(spki.algorithm.oid)
        && spki.algorithm.parameters_der is None
        && spki.subject_public_key_unused_bits == 0
        && spki.subject_public_key_bits.len() == 32
        && signature.len() == 64
        && !is_small_order(spki.subject_public_key_bits)
        && ed25519_verify(input, spki.subject_public_key_bits, signature)
}

/// RFC 8446 §4.4.3: whether `signature` is a valid `scheme` signature of
/// `input` under the end-entity SubjectPublicKeyInfo `key`.
pub open spec fn verify(key: Seq<u8>, scheme: u16, input: Seq<u8>, signature: Seq<u8>) -> bool {
    match clazel_x509::spki::spec::parse_subject_public_key_info(key) {
        None => false,
        Some(spki) =>
            if scheme == 0x0403 { ecdsa_p256_sha256(spki, input, signature) }
            else if scheme == 0x0804 { rsa_pss_rsae(spki, Hash::Sha256, input, signature) }
            else if scheme == 0x0805 { rsa_pss_rsae(spki, Hash::Sha384, input, signature) }
            else if scheme == 0x0806 { rsa_pss_rsae(spki, Hash::Sha512, input, signature) }
            else if scheme == 0x0807 { ed25519(spki, input, signature) }
            else { false },
    }
}

} // verus!
