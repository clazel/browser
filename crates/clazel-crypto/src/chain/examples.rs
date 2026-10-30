//! Known answers, evaluated: the link profile's guards and refusals on
//! small inputs, with results written out from the RFCs and the browsers'
//! rules cited in [`super::spec`], proven by evaluating the spec
//! (`by (compute_only)`). They are facts about the spec itself and the
//! theorems the mutation certificates in `mutations.json` contradict.
//!
//! The verifications themselves are uninterpreted (libcrux) or too large to
//! evaluate here (RSA 2048, `clazel-pkcs1`'s own examples cover it), so an
//! accepted link is never evaluated; the dispatch to them is covered by the
//! exec proof, `lemmas::lemma_thm_production_links_verify` and
//! tests/chain.rs (their mutations are `killed-incidentally`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An AlgorithmIdentifier with no parameters.
pub open spec fn ex_alg(oid: Seq<nat>) -> clazel_x509::certificate::spec::AlgorithmIdentifier {
    clazel_x509::certificate::spec::AlgorithmIdentifier { oid, parameters_der: None }
}

/// sha256WithRSAEncryption, 1.2.840.113549.1.1.11 (RFC 4055 §5).
pub open spec fn ex_sha256_rsa() -> clazel_x509::certificate::spec::AlgorithmIdentifier {
    ex_alg(seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 11nat])
}

/// ecdsa-with-SHA256, 1.2.840.10045.4.3.2 (RFC 5758 §3.2).
pub open spec fn ex_ecdsa_sha256() -> clazel_x509::certificate::spec::AlgorithmIdentifier {
    ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat])
}

/// ecdsa-with-SHA384, 1.2.840.10045.4.3.3 (RFC 5758 §3.2).
pub open spec fn ex_ecdsa_sha384() -> clazel_x509::certificate::spec::AlgorithmIdentifier {
    ex_alg(seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 3nat])
}

/// A P-256 key (`crate::signature::examples`).
pub open spec fn ex_p256() -> clazel_x509::spki::spec::SubjectPublicKeyInfo {
    crate::signature::examples::ex_p256_spki(0x04u8, crate::signature::examples::ex_point())
}

/// A P-384 key: id-ecPublicKey, namedCurve secp384r1, 0x04 then 96 octets.
pub open spec fn ex_p384() -> clazel_x509::spki::spec::SubjectPublicKeyInfo {
    crate::signature::examples::ex_spki(seq![1nat, 2nat, 840nat, 10045nat, 2nat, 1nat],
        Some(seq![0x06u8, 0x05u8, 0x2bu8, 0x81u8, 0x04u8, 0x00u8, 0x22u8]), 0,
        seq![0x04u8] + Seq::new(96, |i: int| (i + 1) as u8))
}

/// An rsaEncryption key with a 2048-bit modulus of 0xff octets and the
/// exponent `e` (RFC 3279 §2.3.1); the fields links do not read are empty.
pub open spec fn ex_rsa(e: Seq<u8>) -> clazel_x509::spki::spec::SubjectPublicKeyInfo {
    clazel_x509::spki::spec::SubjectPublicKeyInfo {
        algorithm: clazel_x509::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 113549nat, 1nat, 1nat, 1nat],
            parameters_der: Some(seq![0x05u8, 0x00u8]),
        },
        public_key: clazel_x509::spki::spec::PublicKey::Rsa(clazel_x509::spki::spec::RsaPublicKey {
            encoded_der: Seq::empty(),
            modulus_der: Seq::empty(),
            modulus_octets: crate::signature::examples::ex_ones(256),
            public_exponent_der: Seq::empty(),
            public_exponent_octets: e,
        }),
        subject_public_key_unused_bits: 0,
        subject_public_key_bits: Seq::empty(),
        subject_public_key_tlv: Seq::empty(),
        spki_der: Seq::empty(),
    }
}

/// BoringSSL's exponent rule: odd, at most 33 bits.
pub proof fn lemma_exponent_profile_examples()
    ensures
        exponent_profile(3),
        exponent_profile(65537),
        exponent_profile(0x1_ffff_ffffnat),
        !exponent_profile(65536),
        !exponent_profile(0x2_0000_0001nat),
{
    assert(exponent_profile(3)) by (compute_only);
    assert(exponent_profile(65537)) by (compute_only);
    assert(exponent_profile(0x1_ffff_ffffnat)) by (compute_only);
    assert(!exponent_profile(65536)) by (compute_only);
    assert(!exponent_profile(0x2_0000_0001nat)) by (compute_only);
}

/// RFC 4055 §5 and RFC 8017 §9.2 Note 1: each sha*WithRSAEncryption puts
/// its own hash in DigestInfo, whose OID ends in 1 (id-sha256), 2
/// (id-sha384) or 3 (id-sha512) at octet 14.
pub proof fn lemma_pkcs1_hash_examples()
    ensures
        clazel_pkcs1::spec::digest_info_prefix(pkcs1_hash(
            clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha256))[14] == 0x01u8,
        clazel_pkcs1::spec::digest_info_prefix(pkcs1_hash(
            clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha384))[14] == 0x02u8,
        clazel_pkcs1::spec::digest_info_prefix(pkcs1_hash(
            clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha512))[14] == 0x03u8,
{
    assert(clazel_pkcs1::spec::digest_info_prefix(pkcs1_hash(
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha256))[14] == 0x01u8) by (compute_only);
    assert(clazel_pkcs1::spec::digest_info_prefix(pkcs1_hash(
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha384))[14] == 0x02u8) by (compute_only);
    assert(clazel_pkcs1::spec::digest_info_prefix(pkcs1_hash(
        clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha512))[14] == 0x03u8) by (compute_only);
}

/// The refusals of the header, each on a key and algorithm that do not fit.
pub proof fn lemma_link_refusals()
    ensures
        // An RSA signature under an EC key.
        !link_with_key(ex_p256(), ex_sha256_rsa(), seq![], seq![]),
        // An ECDSA signature under an RSA key.
        !link_with_key(ex_rsa(seq![0x01u8, 0x00u8, 0x01u8]), ex_ecdsa_sha256(), seq![], seq![]),
        // A P-384 issuer key, under either hash (until P17).
        !link_with_key(ex_p384(), ex_ecdsa_sha256(), seq![], seq![]),
        !link_with_key(ex_p384(), ex_ecdsa_sha384(), seq![], seq![]),
        // Ed25519 (RFC 8410 §3): Unsupported.
        !link_with_key(ex_p256(), ex_alg(seq![1nat, 3nat, 101nat, 112nat]), seq![], seq![]),
        // ecdsa-with-SHA256 with NULL parameters (RFC 5758 §3.2): malformed.
        !link_with_key(ex_p256(), clazel_x509::certificate::spec::AlgorithmIdentifier {
            oid: seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat],
            parameters_der: Some(seq![0x05u8, 0x00u8]) }, seq![], seq![]),
        // An even exponent.
        !link_with_key(ex_rsa(seq![0x01u8, 0x00u8, 0x00u8]), ex_sha256_rsa(), seq![], seq![]),
{
    assert(!link_with_key(ex_p256(), ex_sha256_rsa(), seq![], seq![])) by (compute_only);
    assert(!link_with_key(ex_rsa(seq![0x01u8, 0x00u8, 0x01u8]), ex_ecdsa_sha256(), seq![], seq![]))
        by (compute_only);
    assert(!link_with_key(ex_p384(), ex_ecdsa_sha256(), seq![], seq![])) by (compute_only);
    assert(!link_with_key(ex_p384(), ex_ecdsa_sha384(), seq![], seq![])) by (compute_only);
    assert(!link_with_key(ex_p256(), ex_alg(seq![1nat, 3nat, 101nat, 112nat]), seq![], seq![]))
        by (compute_only);
    assert(!link_with_key(ex_p256(), clazel_x509::certificate::spec::AlgorithmIdentifier {
        oid: seq![1nat, 2nat, 840nat, 10045nat, 4nat, 3nat, 2nat],
        parameters_der: Some(seq![0x05u8, 0x00u8]) }, seq![], seq![])) by (compute_only);
    assert(!link_with_key(ex_rsa(seq![0x01u8, 0x00u8, 0x00u8]), ex_sha256_rsa(), seq![], seq![]))
        by (compute_only);
}

} // verus!
