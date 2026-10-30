//! Path-validation design §3.5, "after the join": `thm_links_verify`
//! (proven in `clazel_x509::path::lemmas` for every `LinkFn`) composed with
//! the production instance [`super::spec::production_link`]. Every link of
//! a path §6.1 accepts is then one of the accepted forms, written out in
//! [`verified_link`] as a disjunction rather than as the instance's
//! `match`: an RSA PKCS#1 v1.5 verification under `clazel_pkcs1`'s spec of
//! the libcrux SHA-2 digest of the certificate's exact TBS octets, or
//! libcrux's ECDSA P-256 predicate on those octets. No other algorithm and
//! no other key class (P-384 included) can occur.
//!
//! The TBS octets are `cert.signature.tbs_der`, which `path::parsed`
//! builds with `prepare_signature` from the certificate envelope's
//! `tbs_certificate_der`, the exact DER TLV of TBSCertificate (RFC 5280
//! §4.1.1.3: the signature is "computed upon the ASN.1 DER encoded
//! tbsCertificate").

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An RSA PKCS#1 v1.5 link: an rsaEncryption key, the exponent profile, and
/// RFC 8017 §8.2.2 over the `hash` digest of `tbs`.
pub open spec fn rsa_verified(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo,
    hash: clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash, tbs: Seq<u8>, signature: Seq<u8>) -> bool
{
    &&& spki.public_key is Rsa
    &&& exponent_profile(clazel_pkcs1::spec::os2ip(spki.public_key->Rsa_0.public_exponent_octets))
    &&& clazel_pkcs1::spec::rsassa_pkcs1_v1_5_verify(
            clazel_pkcs1::spec::os2ip(spki.public_key->Rsa_0.modulus_octets),
            clazel_pkcs1::spec::os2ip(spki.public_key->Rsa_0.public_exponent_octets),
            rsa_digest(hash, tbs), pkcs1_hash(hash), signature)
}

/// An ECDSA P-256 link: a secp256r1 key, one Ecdsa-Sig-Value, and
/// libcrux's verification of `tbs` with SHA-256 (`sha384` false) or SHA-384.
pub open spec fn p256_verified(spki: clazel_x509::spki::spec::SubjectPublicKeyInfo, sha384: bool,
    tbs: Seq<u8>, signature: Seq<u8>) -> bool
{
    &&& spki.public_key is EcP256
    &&& crate::signature::spec::ecdsa_sig_value(signature) is Some
    &&& {
        let point = spki.public_key->EcP256_0;
        let (r, s) = crate::signature::spec::ecdsa_sig_value(signature)->Some_0;
        if sha384 { crate::signature::spec::ecdsa_p256_sha384_verify(tbs, r, s, point) }
        else { crate::signature::spec::ecdsa_p256_sha256_verify(tbs, r, s, point) }
    }
}

/// The link from the key `issuer_spki` to `cert` is a verification of one
/// of the accepted forms, on `cert`'s exact TBS octets.
pub open spec fn verified_link(issuer_spki: Seq<u8>, cert: clazel_x509::path::parsed::spec::PathCert) -> bool {
    let tbs = cert.signature.tbs_der;
    let signature = cert.signature.signature_bits;
    let class = clazel_x509::signature_algorithm::spec::classify(cert.signature.tbs_algorithm);
    &&& clazel_x509::spki::spec::parse_subject_public_key_info(issuer_spki) is Some
    &&& {
        let spki = clazel_x509::spki::spec::parse_subject_public_key_info(issuer_spki)->Some_0;
        ||| class == Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Supported(
                clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha256))
            && rsa_verified(spki, clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha256, tbs, signature)
        ||| class == Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Supported(
                clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha384))
            && rsa_verified(spki, clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha384, tbs, signature)
        ||| class == Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Supported(
                clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha512))
            && rsa_verified(spki, clazel_x509::signature_algorithm::spec::RsaPkcs1v15Hash::Sha512, tbs, signature)
        ||| class == Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Ecdsa(
                clazel_x509::signature_algorithm::spec::EcdsaHash::Sha256))
            && p256_verified(spki, false, tbs, signature)
        ||| class == Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Ecdsa(
                clazel_x509::signature_algorithm::spec::EcdsaHash::Sha384))
            && p256_verified(spki, true, tbs, signature)
    }
}

/// The instance holds of a link only in one of the accepted forms.
pub proof fn lemma_link_verified(issuer_spki: Seq<u8>, cert: clazel_x509::path::parsed::spec::PathCert)
    requires (production_link())(clazel_x509::path::spec::signed_data(issuer_spki, cert)),
    ensures verified_link(issuer_spki, cert),
{
    let d = clazel_x509::path::spec::signed_data(issuer_spki, cert);
    assert(link(d));
    let spki = clazel_x509::spki::spec::parse_subject_public_key_info(issuer_spki)->Some_0;
    match clazel_x509::signature_algorithm::spec::classify(cert.signature.tbs_algorithm) {
        Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Supported(hash)) => {
            assert(rsa_verified(spki, hash, d.tbs_der, d.signature));
        },
        Some(clazel_x509::signature_algorithm::spec::AlgorithmClass::Ecdsa(hash)) => {
            assert(p256_verified(spki, hash == clazel_x509::signature_algorithm::spec::EcdsaHash::Sha384,
                d.tbs_der, d.signature));
        },
        _ => {},
    }
}

/// `thm_links_verify` for the production instance: if §6.1 accepts a path
/// under [`production_link`], certificate 1's signature verifies under the
/// anchor's key and certificate i+1's under certificate i's, each in one
/// of the accepted forms of [`verified_link`].
pub open spec fn thm_production_links_verify(
    revoked: clazel_x509::path::spec::RevokedFn, anchor: clazel_x509::path::parsed::spec::Anchor,
    certs: Seq<clazel_x509::path::parsed::spec::PathCert>, now: clazel_x509::time::spec::CertificateTime,
) -> bool {
    clazel_x509::path::spec::process(production_link(), revoked, anchor, certs, now) is Ok ==> {
        &&& verified_link(anchor.spki_der, certs[0])
        &&& forall|i: int| 0 < i < certs.len() ==>
            #[trigger] verified_link(certs[i - 1].tbs.subject_public_key_info_der, certs[i])
    }
}

/// [`thm_production_links_verify`] holds for every path.
pub proof fn lemma_thm_production_links_verify(
    revoked: clazel_x509::path::spec::RevokedFn, anchor: clazel_x509::path::parsed::spec::Anchor,
    certs: Seq<clazel_x509::path::parsed::spec::PathCert>, now: clazel_x509::time::spec::CertificateTime,
)
    ensures thm_production_links_verify(revoked, anchor, certs, now),
{
    clazel_x509::path::lemmas::lemma_thm_links_verify(production_link(), revoked, anchor, certs, now);
    if clazel_x509::path::spec::process(production_link(), revoked, anchor, certs, now) is Ok {
        lemma_link_verified(anchor.spki_der, certs[0]);
        assert forall|i: int| 0 < i < certs.len() implies
            #[trigger] verified_link(certs[i - 1].tbs.subject_public_key_info_der, certs[i]) by {
            assert((production_link())(clazel_x509::path::spec::signed_data(
                certs[i - 1].tbs.subject_public_key_info_der, certs[i])));
            lemma_link_verified(certs[i - 1].tbs.subject_public_key_info_der, certs[i]);
        }
    }
}

/// The same for a candidate accepted by the verdict on one candidate
/// (`path::verifier::candidate_verdict`, which runs §6.1 last), with the
/// production instance as the environment's `link`.
pub proof fn lemma_candidate_links_verify(
    environment: clazel_x509::path::verifier::Environment,
    anchors: Seq<clazel_x509::path::parsed::spec::Anchor>,
    pool: Seq<Option<clazel_x509::path::parsed::spec::PathCert>>,
    leaf: clazel_x509::path::parsed::spec::PathCert, candidate: clazel_x509::path::verifier::Candidate,
    reference: clazel_x509::spec::ReferenceIdentity, now: clazel_x509::time::spec::CertificateTime,
)
    requires
        environment.link == production_link(),
        clazel_x509::path::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
    ensures
        thm_production_links_verify(environment.revoked, anchors[candidate.anchor as int],
            clazel_x509::path::verifier::candidate_certificates(pool, leaf, candidate), now),
        clazel_x509::path::spec::process(production_link(), environment.revoked,
            anchors[candidate.anchor as int],
            clazel_x509::path::verifier::candidate_certificates(pool, leaf, candidate), now) is Ok,
{
    lemma_thm_production_links_verify(environment.revoked, anchors[candidate.anchor as int],
        clazel_x509::path::verifier::candidate_certificates(pool, leaf, candidate), now);
}

} // verus!
