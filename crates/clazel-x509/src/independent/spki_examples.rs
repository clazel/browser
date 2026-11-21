//! Sanity examples for `spki.rs`, evaluated by Verus on concrete inputs: a
//! real P-256 key, a real RSA-2048 key and RFC 8410 §4's Ed25519 example are
//! accepted with the classification they should have, and each kind of
//! refusal the RFCs require is shown on an input that differs from an
//! accepted one in the part it tests.
//!
//! The P-256 and RSA-2048 keys were generated with OpenSSL for this file
//! (`openssl ecparam -name prime256v1 -genkey`, `openssl genrsa 2048`) and
//! are built below from parts; the parts put together are byte for byte the
//! DER that `openssl ... -pubout -outform DER` wrote. Not read while writing
//! this file: see the list at the top of `spki.rs`.
//!
//! Every input is a spec fn, never a `let` in a proof: `compute_only` does
//! not substitute a proof's `let`, so the decoder would run on an unknown
//! sequence and never finish.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der::*;
#[cfg(verus_only)]
use super::examples::*;
#[cfg(verus_only)]
use super::spki::*;

verus! {

// ---------------------------------------------------------------------------
// Building blocks. `tlv` and `tlv_any` are `examples.rs`'s.
// ---------------------------------------------------------------------------

/// One encoding with two long-form length octets, for 256 to 65535 octets.
pub open spec fn tlv_long2(tag: u8, contents: Seq<u8>) -> Seq<u8> {
    seq![tag, 0x82u8, (contents.len() / 256) as u8, (contents.len() % 256) as u8] + contents
}

/// An encoding of any contents under 65536 octets.
pub open spec fn tlv_big(tag: u8, contents: Seq<u8>) -> Seq<u8> {
    if contents.len() < 256 {
        tlv_any(tag, contents)
    } else {
        tlv_long2(tag, contents)
    }
}

/// A SubjectPublicKeyInfo from an AlgorithmIdentifier's encoding, the unused
/// bits count and the key octets.
pub open spec fn spki_of(alg: Seq<u8>, unused: u8, key: Seq<u8>) -> Seq<u8> {
    tlv_big(0x30, alg + tlv_big(0x03, seq![unused] + key))
}

/// The contents of `rsaEncryption`, 1.2.840.113549.1.1.1.
pub open spec fn rsa_oid() -> Seq<u8> {
    seq![0x2Au8, 0x86u8, 0x48u8, 0x86u8, 0xF7u8, 0x0Du8, 0x01u8, 0x01u8, 0x01u8]
}

/// The contents of `id-RSASSA-PSS`, 1.2.840.113549.1.1.10.
pub open spec fn rsassa_pss_oid() -> Seq<u8> {
    seq![0x2Au8, 0x86u8, 0x48u8, 0x86u8, 0xF7u8, 0x0Du8, 0x01u8, 0x01u8, 0x0Au8]
}

/// The contents of `id-ecPublicKey`, 1.2.840.10045.2.1.
pub open spec fn ec_oid() -> Seq<u8> {
    seq![0x2Au8, 0x86u8, 0x48u8, 0xCEu8, 0x3Du8, 0x02u8, 0x01u8]
}

/// The contents of `secp256r1`, 1.2.840.10045.3.1.7.
pub open spec fn p256_oid() -> Seq<u8> {
    seq![0x2Au8, 0x86u8, 0x48u8, 0xCEu8, 0x3Du8, 0x03u8, 0x01u8, 0x07u8]
}

/// The contents of `secp256k1`, 1.3.132.0.10: a named curve outside RFC
/// 5480's list.
pub open spec fn secp256k1_oid() -> Seq<u8> {
    seq![0x2Bu8, 0x81u8, 0x04u8, 0x00u8, 0x0Au8]
}

/// The contents of `id-Ed25519`, 1.3.101.112.
pub open spec fn ed25519_oid() -> Seq<u8> {
    seq![0x2Bu8, 0x65u8, 0x70u8]
}

/// AlgorithmIdentifier `rsaEncryption` with these parameter octets.
pub open spec fn rsa_alg(parameters: Seq<u8>) -> Seq<u8> {
    tlv(0x30, tlv(0x06, rsa_oid()) + parameters)
}

/// The NULL value.
pub open spec fn null() -> Seq<u8> {
    seq![0x05u8, 0x00u8]
}

/// AlgorithmIdentifier `id-ecPublicKey` with these parameter octets.
pub open spec fn ec_alg(parameters: Seq<u8>) -> Seq<u8> {
    tlv(0x30, tlv(0x06, ec_oid()) + parameters)
}

/// AlgorithmIdentifier `id-Ed25519` with these parameter octets.
pub open spec fn ed25519_alg(parameters: Seq<u8>) -> Seq<u8> {
    tlv(0x30, tlv(0x06, ed25519_oid()) + parameters)
}

/// x then y of the OpenSSL-generated P-256 key.
pub open spec fn p256_xy() -> Seq<u8> {
    seq![
        0x69u8, 0xC4u8, 0x24u8, 0x46u8, 0xB4u8, 0x53u8, 0x8Bu8, 0x79u8, 0x6Du8, 0xD8u8, 0x95u8,
        0x2Bu8, 0x5Au8, 0x77u8, 0xBAu8, 0x20u8, 0x2Au8, 0x04u8, 0xADu8, 0x90u8, 0x5Cu8, 0xADu8,
        0xE8u8, 0xBEu8, 0x94u8, 0x33u8, 0xE7u8, 0x46u8, 0x9Cu8, 0x35u8, 0xE4u8, 0x7Cu8, 0x30u8,
        0xC7u8, 0x27u8, 0xBCu8, 0x55u8, 0x7Bu8, 0xA5u8, 0x51u8, 0x4Fu8, 0xD6u8, 0xAAu8, 0x58u8,
        0x01u8, 0x0Bu8, 0xFBu8, 0xDEu8, 0x33u8, 0x78u8, 0x05u8, 0xE9u8, 0xB8u8, 0x7Au8, 0xE9u8,
        0xE4u8, 0xD7u8, 0xDAu8, 0xA5u8, 0x5Eu8, 0x4Bu8, 0xD3u8, 0x47u8, 0xB9u8,
    ]
}

/// AlgorithmIdentifier `id-ecPublicKey` with `namedCurve` secp256r1.
pub open spec fn p256_alg() -> Seq<u8> {
    ec_alg(tlv(0x06, p256_oid()))
}

/// The OpenSSL-generated P-256 point, uncompressed.
pub open spec fn p256_point() -> Seq<u8> {
    seq![0x04u8] + p256_xy()
}

/// x of the OpenSSL-generated P-256 key.
pub open spec fn p256_x() -> Seq<u8> {
    p256_xy().subrange(0, 32)
}

/// The OpenSSL-generated P-256 key, uncompressed, as OpenSSL wrote it.
pub open spec fn p256_spki() -> Seq<u8> {
    spki_of(p256_alg(), 0, p256_point())
}

/// The 256 octets of the OpenSSL-generated RSA-2048 modulus, in sixteen
/// parts, which keeps Verus's evaluation of the literal shallow.
pub open spec fn rsa_modulus() -> Seq<u8> {
    seq![
        0xB5u8, 0x9Bu8, 0x5Au8, 0x00u8, 0x8Fu8, 0x0Bu8, 0x78u8, 0xD9u8,
        0x7Cu8, 0x19u8, 0x6Cu8, 0x16u8, 0x42u8, 0x24u8, 0x34u8, 0x20u8,
    ]
    + seq![
        0xEDu8, 0x34u8, 0x83u8, 0x89u8, 0x94u8, 0x07u8, 0x01u8, 0x31u8,
        0x87u8, 0x42u8, 0x24u8, 0x70u8, 0x49u8, 0xB2u8, 0x67u8, 0x0Fu8,
    ]
    + seq![
        0x50u8, 0x5Au8, 0x1Au8, 0xD5u8, 0xF5u8, 0xCFu8, 0xB1u8, 0x3Bu8,
        0x98u8, 0x69u8, 0x6Cu8, 0x40u8, 0xABu8, 0xDEu8, 0x82u8, 0xCAu8,
    ]
    + seq![
        0x6Au8, 0x3Du8, 0xC3u8, 0xF6u8, 0x3Du8, 0x10u8, 0x8Cu8, 0x58u8,
        0xA0u8, 0x0Au8, 0xDDu8, 0x7Au8, 0xACu8, 0x4Eu8, 0xC6u8, 0x62u8,
    ]
    + seq![
        0x49u8, 0x0Du8, 0x93u8, 0x58u8, 0x86u8, 0xFDu8, 0x02u8, 0x91u8,
        0x12u8, 0x8Eu8, 0x7Eu8, 0xEBu8, 0x15u8, 0xEDu8, 0x7Eu8, 0x1Fu8,
    ]
    + seq![
        0x62u8, 0x63u8, 0x6Au8, 0x2Fu8, 0xCBu8, 0x81u8, 0xD8u8, 0x5Cu8,
        0x41u8, 0xCFu8, 0x92u8, 0xB2u8, 0x2Fu8, 0x54u8, 0xEAu8, 0x30u8,
    ]
    + seq![
        0x7Bu8, 0x57u8, 0x70u8, 0xC7u8, 0x97u8, 0x60u8, 0xACu8, 0x39u8,
        0x64u8, 0x8Du8, 0xABu8, 0xD9u8, 0x6Du8, 0xFBu8, 0x06u8, 0x98u8,
    ]
    + seq![
        0xB4u8, 0x66u8, 0x46u8, 0x68u8, 0x25u8, 0x7Fu8, 0x36u8, 0xC1u8,
        0x23u8, 0xF3u8, 0x0Bu8, 0x5Fu8, 0xF0u8, 0xDFu8, 0x90u8, 0xDFu8,
    ]
    + seq![
        0xB3u8, 0x27u8, 0x43u8, 0x5Fu8, 0xB2u8, 0xCFu8, 0xCEu8, 0x2Fu8,
        0x1Eu8, 0xFBu8, 0x53u8, 0x1Eu8, 0x92u8, 0xF3u8, 0x45u8, 0x43u8,
    ]
    + seq![
        0x59u8, 0xC4u8, 0x27u8, 0xABu8, 0xD7u8, 0xD6u8, 0xBBu8, 0xE1u8,
        0x7Eu8, 0x83u8, 0x52u8, 0x0Cu8, 0x23u8, 0x9Au8, 0x7Eu8, 0x54u8,
    ]
    + seq![
        0x0Cu8, 0x4Du8, 0xBDu8, 0x56u8, 0x19u8, 0xF5u8, 0xBBu8, 0x94u8,
        0x05u8, 0xE8u8, 0xAAu8, 0x11u8, 0x8Bu8, 0x4Eu8, 0x6Au8, 0x79u8,
    ]
    + seq![
        0x2Du8, 0x1Cu8, 0x12u8, 0x4Eu8, 0x66u8, 0x0Cu8, 0x83u8, 0x51u8,
        0x49u8, 0x31u8, 0x25u8, 0x0Au8, 0x8Bu8, 0xACu8, 0x6Au8, 0xF9u8,
    ]
    + seq![
        0x1Fu8, 0xF3u8, 0x60u8, 0x63u8, 0x8Bu8, 0x16u8, 0x28u8, 0xE6u8,
        0xC7u8, 0x44u8, 0x14u8, 0x31u8, 0x86u8, 0x00u8, 0x87u8, 0xB9u8,
    ]
    + seq![
        0x7Bu8, 0xC0u8, 0x31u8, 0xD6u8, 0x40u8, 0x0Eu8, 0x6Au8, 0xEAu8,
        0x63u8, 0x96u8, 0xCBu8, 0x5Cu8, 0x65u8, 0x69u8, 0xD6u8, 0xE2u8,
    ]
    + seq![
        0xDDu8, 0xCAu8, 0x54u8, 0xB5u8, 0x20u8, 0x56u8, 0x2Fu8, 0x9Fu8,
        0xA1u8, 0x79u8, 0xFBu8, 0x5Bu8, 0xD7u8, 0xBBu8, 0x2Eu8, 0x11u8,
    ]
    + seq![
        0x73u8, 0xDDu8, 0xAFu8, 0xF6u8, 0x01u8, 0x1Bu8, 0x7Eu8, 0x61u8,
        0x4Au8, 0x99u8, 0x25u8, 0x8Fu8, 0x40u8, 0xD7u8, 0x55u8, 0xB1u8,
    ]
}

/// An RSAPublicKey from the contents of its two INTEGERs.
pub open spec fn rsa_public_key(modulus: Seq<u8>, exponent: Seq<u8>) -> Seq<u8> {
    tlv_big(0x30, tlv_big(0x02, modulus) + tlv(0x02, exponent))
}

/// e = 65537.
pub open spec fn f4() -> Seq<u8> {
    seq![0x01u8, 0x00u8, 0x01u8]
}

/// The OpenSSL-generated RSAPublicKey: the modulus takes a leading 00,
/// since its first octet has bit 8 set.
pub open spec fn rsa_2048_key() -> Seq<u8> {
    rsa_public_key(seq![0x00u8] + rsa_modulus(), f4())
}

/// The OpenSSL-generated RSA-2048 key, as OpenSSL wrote it.
pub open spec fn rsa_spki() -> Seq<u8> {
    spki_of(rsa_alg(null()), 0, rsa_2048_key())
}

/// An `rsaEncryption` key with n = 0x7F (127) and this exponent.
pub open spec fn toy_rsa(exponent: Seq<u8>) -> Seq<u8> {
    spki_of(rsa_alg(null()), 0, rsa_public_key(seq![0x7Fu8], exponent))
}

/// RFC 8410 §4's key with its last octet's low bit cleared, in a bit string
/// that declares that bit unused.
pub open spec fn ed25519_unused_bit() -> Seq<u8> {
    spki_of(ed25519_alg(Seq::<u8>::empty()), 1, ed25519_key().update(31, 0xE0u8))
}

/// The P-256 key with a NULL after `subjectPublicKey`.
pub open spec fn p256_extra_component() -> Seq<u8> {
    tlv(0x30, p256_alg() + tlv(0x03, seq![0x00u8] + p256_point()) + null())
}

/// RFC 8410 §4's example key.
pub open spec fn ed25519_key() -> Seq<u8> {
    seq![
        0x19u8, 0xBFu8, 0x44u8, 0x09u8, 0x69u8, 0x84u8, 0xCDu8, 0xFEu8, 0x85u8, 0x41u8, 0xBAu8,
        0xC1u8, 0x67u8, 0xDCu8, 0x3Bu8, 0x96u8, 0xC8u8, 0x50u8, 0x86u8, 0xAAu8, 0x30u8, 0xB6u8,
        0xB6u8, 0xCBu8, 0x0Cu8, 0x5Cu8, 0x38u8, 0xADu8, 0x70u8, 0x31u8, 0x66u8, 0xE1u8,
    ]
}

/// RFC 8410 §4's example, `MCowBQYDK2VwAyEAGb9ECWmEzf6FQbrBZ9w7lshQhqowtrbLDFw4rXAxZuE=`.
pub open spec fn ed25519_spki() -> Seq<u8> {
    spki_of(ed25519_alg(Seq::<u8>::empty()), 0, ed25519_key())
}

/// `r` is an RSA key with this modulus and exponent.
pub open spec fn is_rsa(r: Option<PublicKey>, n: int, e: int) -> bool {
    match r {
        Some(PublicKey::Rsa { modulus, public_exponent, .. }) => modulus == n && public_exponent == e,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Accepted keys
// ---------------------------------------------------------------------------

/// The P-256 key, byte for byte, and its classification.
proof fn example_p256() {
    assert(p256_spki() == seq![
        0x30u8, 0x59u8, 0x30u8, 0x13u8, 0x06u8, 0x07u8, 0x2Au8, 0x86u8, 0x48u8, 0xCEu8, 0x3Du8,
        0x02u8, 0x01u8, 0x06u8, 0x08u8, 0x2Au8, 0x86u8, 0x48u8, 0xCEu8, 0x3Du8, 0x03u8, 0x01u8,
        0x07u8, 0x03u8, 0x42u8, 0x00u8, 0x04u8,
    ] + p256_xy()) by (compute_only);
    assert(subject_public_key(p256_spki()) == Some(
        PublicKey::Ec {
            curve: NamedCurve::P256,
            form: PointForm::Uncompressed,
            point: seq![0x04u8] + p256_xy(),
        },
    )) by (compute_only);
    assert(valid_subject_public_key(p256_spki()) == subject_public_key(p256_spki()))
        by (compute_only);
}

/// The same point compressed: RFC 5480 §2.2 "MAY support the compressed
/// form". (Whether 03 is y's right parity is not checked: see `spki.rs`.)
proof fn example_p256_compressed() {
    assert(subject_public_key(spki_of(p256_alg(), 0, seq![0x03u8] + p256_x())) == Some(
        PublicKey::Ec {
            curve: NamedCurve::P256,
            form: PointForm::Compressed,
            point: seq![0x03u8] + p256_x(),
        },
    )) by (compute_only);
}

/// The RSA-2048 key, its header octets as OpenSSL wrote them, and its
/// modulus and exponent.
proof fn example_rsa_2048() {
    assert(rsa_spki().subrange(0, 34) == seq![
        0x30u8, 0x82u8, 0x01u8, 0x22u8, 0x30u8, 0x0Du8, 0x06u8, 0x09u8, 0x2Au8, 0x86u8, 0x48u8,
        0x86u8, 0xF7u8, 0x0Du8, 0x01u8, 0x01u8, 0x01u8, 0x05u8, 0x00u8, 0x03u8, 0x82u8, 0x01u8,
        0x0Fu8, 0x00u8, 0x30u8, 0x82u8, 0x01u8, 0x0Au8, 0x02u8, 0x82u8, 0x01u8, 0x01u8, 0x00u8,
        0xB5u8,
    ]) by (compute_only);
    assert(rsa_spki().len() == 294) by (compute_only);
    assert(is_rsa(subject_public_key(rsa_spki()), magnitude(rsa_modulus(), 256) as int, 65537))
        by (compute_only);
    assert(is_rsa(valid_subject_public_key(rsa_spki()), magnitude(rsa_modulus(), 256) as int, 65537))
        by (compute_only);
}

/// RFC 8410 §4's Ed25519 example.
proof fn example_ed25519() {
    assert(ed25519_spki() == seq![
        0x30u8, 0x2Au8, 0x30u8, 0x05u8, 0x06u8, 0x03u8, 0x2Bu8, 0x65u8, 0x70u8, 0x03u8, 0x21u8,
        0x00u8,
    ] + ed25519_key()) by (compute_only);
    assert(subject_public_key(ed25519_spki()) == Some(PublicKey::Ed25519 { key: ed25519_key() }))
        by (compute_only);
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

/// RFC 3279 §2.3.1 "The parameters field MUST have ASN.1 type NULL": a NULL
/// with a contents octet (X.690 8.8.2), an absent field, and a field of
/// another type are each refused.
proof fn example_rsa_parameters() {
    assert(subject_public_key(spki_of(rsa_alg(seq![0x05u8, 0x01u8, 0x00u8]), 0, rsa_2048_key()))
        .is_none()) by (compute_only);
    assert(subject_public_key(spki_of(rsa_alg(Seq::<u8>::empty()), 0, rsa_2048_key())).is_none())
        by (compute_only);
    assert(subject_public_key(spki_of(rsa_alg(tlv(0x06, p256_oid())), 0, rsa_2048_key()))
        .is_none()) by (compute_only);
}

/// RSAPublicKey: a modulus without its leading 00 is negative (RFC 8017
/// §3.1: "a positive integer"), one with an unneeded 00 is not DER (X.690
/// 8.3.2), and a third component is not an RSAPublicKey.
proof fn example_rsa_integers() {
    assert(subject_public_key(spki_of(rsa_alg(null()), 0, rsa_public_key(rsa_modulus(), f4())))
        .is_none()) by (compute_only);
    assert(subject_public_key(spki_of(rsa_alg(null()), 0, rsa_public_key(seq![0x00u8, 0x7Fu8], f4())))
        .is_none()) by (compute_only);
    assert(subject_public_key(
        spki_of(
            rsa_alg(null()),
            0,
            tlv(0x30, tlv(0x02, seq![0x7Fu8]) + tlv(0x02, f4()) + tlv(0x02, f4())),
        ),
    ).is_none()) by (compute_only);
}

/// RFC 8017 §3.1, a valid key: n = 0x7F (odd, 127) with e = 65537 > n - 1
/// decodes, and is refused only by the requirements; e = 3 meets them.
proof fn example_rsa_requirements() {
    assert(is_rsa(subject_public_key(toy_rsa(f4())), 127, 65537)) by (compute_only);
    assert(valid_subject_public_key(toy_rsa(f4())).is_none()) by (compute_only);
    assert(is_rsa(valid_subject_public_key(toy_rsa(seq![0x03u8])), 127, 3)) by (compute_only);
}

/// RFC 4055 §3.1's id-RSASSA-PSS, out of scope, is refused even with the
/// parameters absent, which that section allows.
proof fn example_rsassa_pss() {
    assert(subject_public_key(spki_of(tlv(0x30, tlv(0x06, rsassa_pss_oid())), 0, rsa_2048_key()))
        .is_none()) by (compute_only);
}

/// RFC 5480 §2.1.1.1: secp256k1 is not among the curves in scope; and
/// §2.1.1's `ECParameters` must be present and a `namedCurve`.
proof fn example_ec_parameters() {
    assert(subject_public_key(spki_of(ec_alg(tlv(0x06, secp256k1_oid())), 0, p256_point()))
        .is_none()) by (compute_only);
    // Absent.
    assert(subject_public_key(spki_of(ec_alg(Seq::<u8>::empty()), 0, p256_point())).is_none())
        by (compute_only);
    // implicitCurve NULL.
    assert(subject_public_key(spki_of(ec_alg(null()), 0, p256_point())).is_none())
        by (compute_only);
}

/// RFC 5480 §2.2: a hybrid first octet 06, the point at infinity's 00, and a
/// point one octet short are each refused.
proof fn example_ec_points() {
    assert(subject_public_key(spki_of(p256_alg(), 0, seq![0x06u8] + p256_xy())).is_none())
        by (compute_only);
    assert(subject_public_key(spki_of(p256_alg(), 0, seq![0x00u8])).is_none()) by (compute_only);
    assert(subject_public_key(spki_of(p256_alg(), 0, seq![0x04u8] + p256_xy().subrange(0, 63)))
        .is_none()) by (compute_only);
}

/// RFC 5280 §4.1: the input is one SubjectPublicKeyInfo and nothing after
/// it; and the 1988 syntax has no third component.
proof fn example_trailing_bytes() {
    assert(subject_public_key(p256_spki() + seq![0x00u8]).is_none()) by (compute_only);
    assert(subject_public_key(p256_extra_component()).is_none()) by (compute_only);
}

/// Unused bits: the bit string below is valid DER (its one unused bit is 0,
/// X.690 11.2.1), but RFC 8410 §4 keys are "an exact multiple of 8 bits".
proof fn example_unused_bits() {
    assert(decode_spki(ed25519_unused_bit()) is Some) by (compute_only);
    assert(subject_public_key(ed25519_unused_bit()).is_none()) by (compute_only);
}

/// RFC 8410 §3 "the parameters MUST be absent", even a NULL; and a key one
/// octet short of RFC 8032's 32 is refused.
proof fn example_ed25519_refusals() {
    assert(subject_public_key(spki_of(ed25519_alg(null()), 0, ed25519_key())).is_none())
        by (compute_only);
    assert(subject_public_key(spki_of(ed25519_alg(Seq::<u8>::empty()), 0, ed25519_key().subrange(0, 31)))
        .is_none()) by (compute_only);
}

} // verus!
