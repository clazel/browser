//! Hosts for certified RFC 5280 SubjectPublicKeyInfo mutation witnesses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A mutation that omits the required rsaEncryption NULL parameters accepts this SPKI.
pub proof fn lemma_reject_rsa_without_null_parameters()
    ensures parse_subject_public_key_info(seq![
        0x30u8, 0x18, 0x30, 0x0B, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x03, 0x09, 0x00, 0x30, 0x06,
        0x02, 0x01, 0x03, 0x02, 0x01, 0x03,
    ]).is_none()
{
    assert(parse_subject_public_key_info(seq![
        0x30u8, 0x18, 0x30, 0x0B, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x03, 0x09, 0x00, 0x30, 0x06,
        0x02, 0x01, 0x03, 0x02, 0x01, 0x03,
    ]).is_none()) by (compute_only);
}

/// A mutation that drops the positive/nonzero modulus requirement accepts zero.
pub proof fn lemma_reject_zero_rsa_modulus()
    ensures parse_subject_public_key_info(seq![
        0x30u8, 0x1A, 0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x09, 0x00,
        0x30, 0x06, 0x02, 0x01, 0x00, 0x02, 0x01, 0x03,
    ]).is_none()
{
    assert(parse_subject_public_key_info(seq![
        0x30u8, 0x1A, 0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x09, 0x00,
        0x30, 0x06, 0x02, 0x01, 0x00, 0x02, 0x01, 0x03,
    ]).is_none()) by (compute_only);
}

/// A mutation that permits bytes after the outer SPKI SEQUENCE accepts this input.
pub proof fn lemma_reject_trailing_spki_input()
    ensures parse_subject_public_key_info(seq![
        0x30u8, 0x1A, 0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x09, 0x00,
        0x30, 0x06, 0x02, 0x01, 0x03, 0x02, 0x01, 0x03, 0x00,
    ]).is_none()
{
    assert(parse_subject_public_key_info(seq![
        0x30u8, 0x1A, 0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x09, 0x00,
        0x30, 0x06, 0x02, 0x01, 0x03, 0x02, 0x01, 0x03, 0x00,
    ]).is_none()) by (compute_only);
}

/// A key algorithm identifier: id-ecPublicKey with the given parameters TLV.
pub open spec fn ex_ec_alg(parameters_der: Option<Seq<u8>>) -> crate::certificate::spec::AlgorithmIdentifier {
    crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat],
        parameters_der,
    }
}

/// secp256r1 as a namedCurve parameter (RFC 5480 §2.1.1.1), written out
/// from the OBJECT IDENTIFIER 1.2.840.10045.3.1.7.
pub open spec fn ex_p256_params() -> Option<Seq<u8>> {
    Some(seq![0x06u8, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07])
}

/// secp384r1 as a namedCurve parameter, from 1.3.132.0.34.
pub open spec fn ex_p384_params() -> Option<Seq<u8>> {
    Some(seq![0x06u8, 0x05, 0x2B, 0x81, 0x04, 0x00, 0x22])
}

/// secp521r1 (1.3.132.0.35), a named curve that is not classified.
pub open spec fn ex_p521_params() -> Option<Seq<u8>> {
    Some(seq![0x06u8, 0x05, 0x2B, 0x81, 0x04, 0x00, 0x23])
}

/// The 64 octets X || Y: 1, 2, ..., 64.
pub open spec fn ex_xy() -> Seq<u8> {
    Seq::new(64, |i: int| (i + 1) as u8)
}

/// `first` followed by the 64 octets of `ex_xy`: 65 octets.
pub open spec fn ex_bits65(first: u8) -> Seq<u8> {
    seq![first] + ex_xy()
}

/// `first` followed by 96 octets 1, 2, ..., 96: 97 octets.
pub open spec fn ex_bits97(first: u8) -> Seq<u8> {
    seq![first] + Seq::new(96, |i: int| (i + 1) as u8)
}

/// RFC 5480 §2.1.1 and §2.2: secp256r1 with the 65-octet uncompressed point
/// is `EcP256` holding the 64 octets after the 0x04.
pub proof fn lemma_ec_p256_is_classified()
    ensures classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, ex_bits65(0x04u8))
        == PublicKey::EcP256(ex_xy())
{
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, ex_bits65(0x04u8))
        == PublicKey::EcP256(ex_xy())) by (compute_only);
}

/// RFC 5480 §2.1.1 and §2.2: secp384r1 with the 97-octet uncompressed point
/// is `EcP384` holding the whole 97-octet ECPoint.
pub proof fn lemma_ec_p384_is_classified()
    ensures classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits97(0x04u8))
        == PublicKey::EcP384(ex_bits97(0x04u8))
{
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits97(0x04u8))
        == PublicKey::EcP384(ex_bits97(0x04u8))) by (compute_only);
}

/// RFC 5480 §2.2: only the uncompressed form (0x04) and exactly the curve's
/// length are classified. Compressed (0x02, 0x03), hybrid (0x06) and other
/// lengths are Unsupported.
pub proof fn lemma_ec_point_forms_are_refused()
    ensures
        // secp256r1: compressed 0x02 || X, 0x03 || X.
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
            seq![0x02u8] + ex_xy().subrange(0, 32)) == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
            seq![0x03u8] + ex_xy().subrange(0, 32)) == PublicKey::Unsupported,
        // secp256r1: the right length with another leading octet (hybrid, 0x06).
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, ex_bits65(0x06u8))
            == PublicKey::Unsupported,
        // secp256r1: one octet short and one octet long.
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
            ex_bits65(0x04u8).subrange(0, 64)) == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
            ex_bits65(0x04u8) + seq![0x00u8]) == PublicKey::Unsupported,
        // secp384r1: compressed, hybrid, one short and one long.
        classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, seq![0x02u8] + ex_bits97(0x04u8).subrange(1, 49))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits97(0x06u8))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits97(0x04u8).subrange(0, 96))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits97(0x04u8) + seq![0x00u8])
            == PublicKey::Unsupported,
        // The length of one curve under the other's parameters.
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, ex_bits97(0x04u8))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits65(0x04u8))
            == PublicKey::Unsupported,
        // No octets at all.
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, Seq::<u8>::empty())
            == PublicKey::Unsupported,
{
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
        seq![0x02u8] + ex_xy().subrange(0, 32)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
        seq![0x03u8] + ex_xy().subrange(0, 32)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, ex_bits65(0x06u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
        ex_bits65(0x04u8).subrange(0, 64)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0,
        ex_bits65(0x04u8) + seq![0x00u8]) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0,
        seq![0x02u8] + ex_bits97(0x04u8).subrange(1, 49)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits97(0x06u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0,
        ex_bits97(0x04u8).subrange(0, 96)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0,
        ex_bits97(0x04u8) + seq![0x00u8]) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, ex_bits97(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 0, ex_bits65(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 0, Seq::<u8>::empty())
        == PublicKey::Unsupported) by (compute_only);
}

/// RFC 5480 §2.1.1: only namedCurve secp256r1 and secp384r1 are classified.
/// Another named curve (secp521r1), absent parameters, NULL parameters and
/// explicit ECParameters (a SEQUENCE, RFC 3279 §2.3.5) are Unsupported.
pub proof fn lemma_ec_other_parameters_are_refused()
    ensures
        classify_ec_public_key(ex_ec_alg(ex_p521_params()), 0, ex_bits65(0x04u8))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p521_params()), 0, ex_bits97(0x04u8))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(None), 0, ex_bits65(0x04u8)) == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(Some(seq![0x05u8, 0x00u8])), 0, ex_bits65(0x04u8))
            == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(Some(seq![0x30u8, 0x00u8])), 0, ex_bits97(0x04u8))
            == PublicKey::Unsupported,
{
    assert(classify_ec_public_key(ex_ec_alg(ex_p521_params()), 0, ex_bits65(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p521_params()), 0, ex_bits97(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(None), 0, ex_bits65(0x04u8)) == PublicKey::Unsupported)
        by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(Some(seq![0x05u8, 0x00u8])), 0, ex_bits65(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(Some(seq![0x30u8, 0x00u8])), 0, ex_bits97(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
}

/// RFC 5480 §2.2: the BIT STRING of an EC key has no unused bits.
pub proof fn lemma_ec_key_with_unused_bits_is_refused()
    ensures
        classify_ec_public_key(ex_ec_alg(ex_p256_params()), 1, ex_bits65(0x04u8)) == PublicKey::Unsupported,
        classify_ec_public_key(ex_ec_alg(ex_p384_params()), 7, ex_bits97(0x04u8)) == PublicKey::Unsupported,
{
    assert(classify_ec_public_key(ex_ec_alg(ex_p256_params()), 1, ex_bits65(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(ex_ec_alg(ex_p384_params()), 7, ex_bits97(0x04u8))
        == PublicKey::Unsupported) by (compute_only);
}

/// RFC 5480 §2.1.1: only id-ecPublicKey (1.2.840.10045.2.1) names an EC key.
/// id-ecDH (1.3.132.1.12), id-ecMQV (1.3.132.1.13), ecdsa-with-SHA256
/// (1.2.840.10045.4.3.2) and a near miss in the last arc are Unsupported.
pub proof fn lemma_non_ec_key_oids_are_refused()
    ensures
        classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 3nat, 132nat, 1nat, 12nat], parameters_der: ex_p256_params() },
            0, ex_bits65(0x04u8)) == PublicKey::Unsupported,
        classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 3nat, 132nat, 1nat, 13nat], parameters_der: ex_p256_params() },
            0, ex_bits65(0x04u8)) == PublicKey::Unsupported,
        classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], parameters_der: ex_p256_params() },
            0, ex_bits65(0x04u8)) == PublicKey::Unsupported,
        classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 10045nat, 2nat, 2nat], parameters_der: ex_p256_params() },
            0, ex_bits65(0x04u8)) == PublicKey::Unsupported,
{
    assert(classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 3nat, 132nat, 1nat, 12nat], parameters_der: ex_p256_params() },
        0, ex_bits65(0x04u8)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 3nat, 132nat, 1nat, 13nat], parameters_der: ex_p256_params() },
        0, ex_bits65(0x04u8)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat], parameters_der: ex_p256_params() },
        0, ex_bits65(0x04u8)) == PublicKey::Unsupported) by (compute_only);
    assert(classify_ec_public_key(crate::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 10045nat, 2nat, 2nat], parameters_der: ex_p256_params() },
        0, ex_bits65(0x04u8)) == PublicKey::Unsupported) by (compute_only);
}

/// A real secp256r1 SubjectPublicKeyInfo (generated by `openssl ecparam
/// -name prime256v1`, DER by `openssl ec -pubout`).
pub open spec fn ex_p256_spki() -> Seq<u8> {
    seq![
        0x30u8, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02,
        0x01, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07, 0x03,
        0x42, 0x00, 0x04, 0x62, 0x22, 0x14, 0x89, 0x36, 0x1C, 0xBF, 0x69, 0x23,
        0x38, 0xCB, 0x1C, 0x55, 0xF7, 0x70, 0x3E, 0x34, 0x99, 0x18, 0x0E, 0xAD,
        0xC7, 0x68, 0x7D, 0x66, 0x20, 0x33, 0x56, 0x8A, 0x26, 0x7F, 0x67, 0x2A,
        0x38, 0xD6, 0xBA, 0x13, 0x9D, 0x54, 0x85, 0x2D, 0xF1, 0x3B, 0xC5, 0x0A,
        0xEA, 0x51, 0x0A, 0xD4, 0x35, 0xD0, 0xB0, 0x19, 0x23, 0xED, 0x0B, 0xDE,
        0x06, 0x56, 0xB2, 0xC8, 0xD4, 0x84, 0xFF,
    ]
}

/// The X || Y of `ex_p256_spki`, read from `openssl ec -text`'s `pub:`
/// (after the leading 04).
pub open spec fn ex_p256_xy() -> Seq<u8> {
    seq![
        0x62u8, 0x22, 0x14, 0x89, 0x36, 0x1C, 0xBF, 0x69, 0x23, 0x38, 0xCB, 0x1C,
        0x55, 0xF7, 0x70, 0x3E, 0x34, 0x99, 0x18, 0x0E, 0xAD, 0xC7, 0x68, 0x7D,
        0x66, 0x20, 0x33, 0x56, 0x8A, 0x26, 0x7F, 0x67, 0x2A, 0x38, 0xD6, 0xBA,
        0x13, 0x9D, 0x54, 0x85, 0x2D, 0xF1, 0x3B, 0xC5, 0x0A, 0xEA, 0x51, 0x0A,
        0xD4, 0x35, 0xD0, 0xB0, 0x19, 0x23, 0xED, 0x0B, 0xDE, 0x06, 0x56, 0xB2,
        0xC8, 0xD4, 0x84, 0xFF,
    ]
}

/// A real secp384r1 SubjectPublicKeyInfo (`openssl ecparam -name
/// secp384r1`).
pub open spec fn ex_p384_spki() -> Seq<u8> {
    seq![
        0x30u8, 0x76, 0x30, 0x10, 0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02,
        0x01, 0x06, 0x05, 0x2B, 0x81, 0x04, 0x00, 0x22, 0x03, 0x62, 0x00, 0x04,
        0x55, 0xCA, 0xF3, 0xF8, 0x21, 0xD1, 0xEC, 0x7F, 0xA2, 0x30, 0x9D, 0xBA,
        0x54, 0xE7, 0xB0, 0xC0, 0xE3, 0x2A, 0xD8, 0xF9, 0xA1, 0x78, 0x80, 0x7F,
        0x3A, 0x45, 0x13, 0x1C, 0x3D, 0x92, 0x25, 0x59, 0x7D, 0x48, 0x58, 0x5A,
        0xB7, 0x36, 0xD0, 0x86, 0xFE, 0x12, 0x84, 0x3D, 0x19, 0x1B, 0x16, 0x21,
        0xCF, 0x50, 0x36, 0x72, 0x2C, 0xCB, 0xBD, 0x03, 0x4B, 0xFE, 0x9B, 0x92,
        0xDA, 0xBE, 0xF2, 0x5B, 0x6E, 0x26, 0xDE, 0xF9, 0x34, 0x5C, 0x9E, 0x8F,
        0x3F, 0x67, 0xE2, 0x2F, 0xBF, 0xD3, 0xB9, 0x1C, 0x21, 0xB9, 0x00, 0x2C,
        0x2D, 0x45, 0x0F, 0x68, 0xB8, 0x86, 0xC7, 0xC2, 0xBF, 0xD6, 0xC7, 0x68,
    ]
}

/// The 97-octet ECPoint of `ex_p384_spki`, `04 || X || Y`.
pub open spec fn ex_p384_point() -> Seq<u8> {
    seq![
        0x04u8, 0x55, 0xCA, 0xF3, 0xF8, 0x21, 0xD1, 0xEC, 0x7F, 0xA2, 0x30, 0x9D,
        0xBA, 0x54, 0xE7, 0xB0, 0xC0, 0xE3, 0x2A, 0xD8, 0xF9, 0xA1, 0x78, 0x80,
        0x7F, 0x3A, 0x45, 0x13, 0x1C, 0x3D, 0x92, 0x25, 0x59, 0x7D, 0x48, 0x58,
        0x5A, 0xB7, 0x36, 0xD0, 0x86, 0xFE, 0x12, 0x84, 0x3D, 0x19, 0x1B, 0x16,
        0x21, 0xCF, 0x50, 0x36, 0x72, 0x2C, 0xCB, 0xBD, 0x03, 0x4B, 0xFE, 0x9B,
        0x92, 0xDA, 0xBE, 0xF2, 0x5B, 0x6E, 0x26, 0xDE, 0xF9, 0x34, 0x5C, 0x9E,
        0x8F, 0x3F, 0x67, 0xE2, 0x2F, 0xBF, 0xD3, 0xB9, 0x1C, 0x21, 0xB9, 0x00,
        0x2C, 0x2D, 0x45, 0x0F, 0x68, 0xB8, 0x86, 0xC7, 0xC2, 0xBF, 0xD6, 0xC7,
        0x68,
    ]
}

/// An id-ecPublicKey SubjectPublicKeyInfo on secp521r1 with a one-octet
/// uncompressed-looking BIT STRING `04`: well framed, not classified.
pub open spec fn ex_p521_like_spki() -> Seq<u8> {
    seq![
        0x30u8, 0x17, 0x30, 0x10, 0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02,
        0x01, 0x06, 0x05, 0x2B, 0x81, 0x04, 0x00, 0x23, 0x03, 0x03, 0x00, 0x04,
        0x01,
    ]
}

/// A whole DER secp256r1 SubjectPublicKeyInfo parses to `EcP256` with the
/// X || Y that OpenSSL prints.
pub proof fn lemma_parse_p256_spki()
    ensures
        parse_subject_public_key_info(ex_p256_spki()) is Some,
        parse_subject_public_key_info(ex_p256_spki()).unwrap().public_key
            == PublicKey::EcP256(ex_p256_xy()),
{
    assert(parse_subject_public_key_info(ex_p256_spki()) is Some) by (compute_only);
    assert(parse_subject_public_key_info(ex_p256_spki()).unwrap().public_key
        == PublicKey::EcP256(ex_p256_xy())) by (compute_only);
}

/// A whole DER secp384r1 SubjectPublicKeyInfo parses to `EcP384` holding the
/// 97-octet ECPoint that OpenSSL prints.
pub proof fn lemma_parse_p384_spki()
    ensures
        parse_subject_public_key_info(ex_p384_spki()) is Some,
        parse_subject_public_key_info(ex_p384_spki()).unwrap().public_key
            == PublicKey::EcP384(ex_p384_point()),
{
    assert(parse_subject_public_key_info(ex_p384_spki()) is Some) by (compute_only);
    assert(parse_subject_public_key_info(ex_p384_spki()).unwrap().public_key
        == PublicKey::EcP384(ex_p384_point())) by (compute_only);
}

/// An unclassified EC key still parses (the set of inputs that parse is
/// unchanged by the EC classes); it is Unsupported.
pub proof fn lemma_parse_unclassified_ec_spki_is_unsupported()
    ensures
        parse_subject_public_key_info(ex_p521_like_spki()) is Some,
        parse_subject_public_key_info(ex_p521_like_spki()).unwrap().public_key
            == PublicKey::Unsupported,
{
    assert(parse_subject_public_key_info(ex_p521_like_spki()) is Some) by (compute_only);
    assert(parse_subject_public_key_info(ex_p521_like_spki()).unwrap().public_key
        == PublicKey::Unsupported) by (compute_only);
}

/// RSA keys stay RSA: the EC classification applies only to other OIDs.
pub proof fn lemma_rsa_spki_is_still_rsa()
    ensures
        parse_subject_public_key_info(seq![
            0x30u8, 0x1A, 0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
            0xF7, 0x0D, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x09, 0x00,
            0x30, 0x06, 0x02, 0x01, 0x03, 0x02, 0x01, 0x03,
        ]).unwrap().public_key is Rsa,
{
    assert(parse_subject_public_key_info(seq![
        0x30u8, 0x1A, 0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86,
        0xF7, 0x0D, 0x01, 0x01, 0x01, 0x05, 0x00, 0x03, 0x09, 0x00,
        0x30, 0x06, 0x02, 0x01, 0x03, 0x02, 0x01, 0x03,
    ]).unwrap().public_key is Rsa) by (compute_only);
}

} // verus!
