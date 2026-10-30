//! Known answers for [`super::spec`], evaluated (`by (compute_only)`): the
//! error-to-alert mapping, the reference identity, the certificate order,
//! the production environment's parameters, the outcome, the anchor step
//! and the refusal of a body that is not a Certificate. They are the
//! theorems the mutation certificates in `mutations.json` contradict.
//!
//! A whole chain is not evaluated here: a DER certificate is beyond
//! `compute_only`'s recursion limit and the link signatures are
//! uninterpreted (libcrux). Accepted chains are covered by the proofs
//! (`lemmas`) and by tests/join.rs.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 8446 §6.2: the alert each refusal sends ([`certificate_error`]).
pub proof fn lemma_error_alerts()
    ensures
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Expired)) == 45,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::AnchorExpired)) == 45,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::UnsupportedAlgorithm)) == 43,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::UnknownIssuer)) == 48,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::BadSignature)) == 48,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::NameChaining)) == 48,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Distrusted)) == 48,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Revoked)) == 48,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::BuildBudgetExhausted)) == 48,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Leaf)) == 42,
        clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Malformed)) == 42,
{
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Expired)) == 45) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::AnchorExpired)) == 45) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::UnsupportedAlgorithm)) == 43) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::UnknownIssuer)) == 48) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::BadSignature)) == 48) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::NameChaining)) == 48) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Distrusted)) == 48) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Revoked)) == 48) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::BuildBudgetExhausted)) == 48) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Leaf)) == 42) by (compute_only);
    assert(clazel_tls::auth::spec::certificate_alert(certificate_error(clazel_x509::path::spec::PathError::Malformed)) == 42) by (compute_only);
}

/// Design Q2: a DNS host is a DNS-ID and an IP host an IP-ID, with the same octets.
pub proof fn lemma_reference_identity()
    ensures
        reference_identity(clazel_tls::host::spec::Host::Dns(seq![104u8]))
            == clazel_x509::spec::ReferenceIdentity::Dns(seq![104u8]),
        reference_identity(clazel_tls::host::spec::Host::Ip(seq![192u8, 0, 2, 10]))
            == clazel_x509::spec::ReferenceIdentity::Ip(seq![192u8, 0, 2, 10]),
{
    assert(reference_identity(clazel_tls::host::spec::Host::Dns(seq![104u8]))
        == clazel_x509::spec::ReferenceIdentity::Dns(seq![104u8])) by (compute_only);
    assert(reference_identity(clazel_tls::host::spec::Host::Ip(seq![192u8, 0, 2, 10]))
        == clazel_x509::spec::ReferenceIdentity::Ip(seq![192u8, 0, 2, 10])) by (compute_only);
}

/// An entry with this cert_data and no extensions.
pub open spec fn ex_entry(cert_data: Seq<u8>) -> clazel_tls::spec::CertificateEntry {
    clazel_tls::spec::CertificateEntry { cert_data, extensions: seq![] }
}

/// RFC 8446 §4.4.2: the certificates in message order, the sender's first.
pub proof fn lemma_presented_order()
    ensures presented(seq![ex_entry(seq![1u8]), ex_entry(seq![2u8])]) == seq![seq![1u8], seq![2u8]],
{
    assert(presented(seq![ex_entry(seq![1u8]), ex_entry(seq![2u8])]) =~= seq![seq![1u8], seq![2u8]]);
}

/// A link whose issuer key does not parse.
pub open spec fn ex_unparsed_link() -> clazel_x509::path::spec::SignedData {
    clazel_x509::path::spec::SignedData {
        issuer_spki: seq![],
        algorithm: clazel_x509::path::examples::ecdsa_sha256(),
        tbs_der: seq![],
        signature: seq![],
    }
}

/// The production environment: P11's links (an unparsed key verifies
/// nothing), nothing revoked, 6 intermediates.
pub proof fn lemma_production_environment()
    ensures
        !(production_environment().link)(ex_unparsed_link()),
        !(production_environment().revoked)(clazel_x509::path::examples::int()),
        production_environment().max_intermediates == 6,
{
    assert(!(production_environment().link)(ex_unparsed_link())) by (compute_only);
    assert(!(production_environment().revoked)(clazel_x509::path::examples::int())) by (compute_only);
    assert(production_environment().max_intermediates == 6) by (compute_only);
}

/// The outcome: the leaf's key, or the refusal's certificate error.
pub proof fn lemma_outcome()
    ensures
        outcome(Ok(clazel_x509::path::verifier::Validated { anchor: 0, path: seq![], leaf_spki: seq![7u8] }))
            == Ok::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(seq![7u8]),
        outcome(Err(clazel_x509::path::spec::PathError::UnknownIssuer))
            == Err::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(clazel_tls::auth::spec::CertificateError::UnknownCa),
{
    assert(outcome(Ok(clazel_x509::path::verifier::Validated { anchor: 0, path: seq![], leaf_spki: seq![7u8] }))
        == Ok::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(seq![7u8])) by (compute_only);
    assert(outcome(Err(clazel_x509::path::spec::PathError::UnknownIssuer))
        == Err::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(clazel_tls::auth::spec::CertificateError::UnknownCa)) by (compute_only);
}

/// A row with an anchor adds it; (R) a row without one adds nothing and
/// keeps the anchors before it.
pub proof fn lemma_add_anchor()
    ensures
        add_anchor(seq![], Some(clazel_x509::path::examples::anchor())).len() == 1,
        add_anchor(seq![clazel_x509::path::examples::anchor()], None).len() == 1,
{
    assert(add_anchor(seq![], Some(clazel_x509::path::examples::anchor())).len() == 1) by (compute_only);
    assert(add_anchor(seq![clazel_x509::path::examples::anchor()], None).len() == 1) by (compute_only);
}

/// A body that is not a Certificate is a bad certificate (42), and
/// CertificateVerify under a key that does not parse verifies nothing.
pub proof fn lemma_not_a_certificate()
    ensures
        validate(seq![], clazel_tls::host::spec::Host::Dns(seq![104u8]), 0, seq![0xffu8])
            == Err::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(clazel_tls::auth::spec::CertificateError::BadCertificate),
        !(verification(seq![]).signature)(seq![], 0x0403, seq![], seq![]),
{
    assert(validate(seq![], clazel_tls::host::spec::Host::Dns(seq![104u8]), 0, seq![0xffu8])
        == Err::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(clazel_tls::auth::spec::CertificateError::BadCertificate)) by (compute_only);
    assert(!(verification(seq![]).signature)(seq![], 0x0403, seq![], seq![])) by (compute_only);
}

} // verus!
