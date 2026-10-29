//! Known answers for the §6.1 transcription (`spec.rs`), the profile
//! (`profile.rs`) and the verdict on a candidate (`verifier.rs`), each proven
//! by evaluation. They are the theorems the certified mutations in
//! `mutations.json` contradict.
//!
//! The examples work over small `PathCert` and `Anchor` values, not DER
//! (design §3.2): the compute-only evaluator reaches its recursion limit on
//! whole certificates, and the decoders are pinned by their own examples.
//! The fixtures:
//! - Names are one-RDN CN names (`root`, `int`, `in2`, `in3`, `lea`), so that
//!   name-constraint checks can decode them, and each certificate's
//!   SubjectPublicKeyInfo is a distinct short placeholder.
//! - `link()` accepts a link exactly when the certificate's signature bytes
//!   are its issuer's key: a stand-in for real verification in which a
//!   certificate "signed" under the wrong key fails.
//! - Validity runs from 2020 to 2040 and `now` is 2026-06-01, except where an
//!   example says otherwise.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// A one-RDN Name `CN=<a b c>`, as DER.
pub open spec fn cn(a: u8, b: u8, c: u8) -> Seq<u8> {
    seq![0x30u8, 0x0e, 0x31, 0x0c, 0x30, 0x0a, 0x06, 0x03, 0x55, 0x04, 0x03, 0x0c, 0x03, a, b, c]
}

/// `CN=roo`, the anchor.
pub open spec fn root_name() -> Seq<u8> { cn(b'r', b'o', b'o') }
/// `CN=int`, the first intermediate.
pub open spec fn int_name() -> Seq<u8> { cn(b'i', b'n', b't') }
/// `CN=in2`, a second intermediate.
pub open spec fn in2_name() -> Seq<u8> { cn(b'i', b'n', b'2') }
/// `CN=in3`, a third intermediate.
pub open spec fn in3_name() -> Seq<u8> { cn(b'i', b'n', b'3') }
/// `CN=lea`, the leaf.
pub open spec fn leaf_name() -> Seq<u8> { cn(b'l', b'e', b'a') }

/// A placeholder SubjectPublicKeyInfo, distinct per `k`.
pub open spec fn key(k: u8) -> Seq<u8> { seq![0x30u8, 0x01, k] }

/// The link stand-in: the signature bytes are the issuer's key.
pub open spec fn link() -> LinkFn {
    |data: SignedData| data.signature == data.issuer_spki
}

/// Nothing is revoked (the production instance).
pub open spec fn not_revoked() -> RevokedFn {
    |cert: super::parsed::spec::PathCert| false
}

/// Everything is revoked.
pub open spec fn all_revoked() -> RevokedFn {
    |cert: super::parsed::spec::PathCert| true
}

/// A time on a day, at midnight.
pub open spec fn day(year: u16, month: u8, d: u8) -> crate::time::spec::CertificateTime {
    crate::time::spec::CertificateTime { year, month, day: d, hour: 0, minute: 0, second: 0 }
}

/// `now`: 2026-06-01T00:00:00Z.
pub open spec fn now() -> crate::time::spec::CertificateTime { day(2026, 6, 1) }

/// ecdsa-with-SHA256, parameters absent.
pub open spec fn ecdsa_sha256() -> crate::certificate::spec::AlgorithmIdentifier {
    crate::certificate::spec::AlgorithmIdentifier { oid: seq![1nat, 2, 840, 10045, 4, 3, 2], parameters_der: None }
}

/// "dNSName example.com".
pub open spec fn example_com() -> Seq<u8> {
    seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'c', b'o', b'm']
}

/// "dNSName other.com".
pub open spec fn other_com() -> Seq<u8> {
    seq![b'o', b't', b'h', b'e', b'r', b'.', b'c', b'o', b'm']
}

/// The reference identity: DNS `example.com`.
pub open spec fn reference() -> crate::spec::ReferenceIdentity {
    crate::spec::ReferenceIdentity::Dns(example_com())
}

/// An extension with this value.
pub open spec fn extension(oid: Seq<nat>, critical: bool, value: Seq<u8>) -> crate::extensions::spec::Extension {
    crate::extensions::spec::Extension { oid, critical, value }
}

/// An OID no part of the crate recognizes.
pub open spec fn unknown_oid() -> Seq<nat> { seq![1nat, 2, 3, 4] }

/// certificatePolicies `{ 2 5 29 32 }`.
pub open spec fn certificate_policies_oid() -> Seq<nat> { seq![2nat, 5, 29, 32] }

/// subjectAltName `SEQUENCE { [2] "example.com" }`, DER.
pub open spec fn san_example_com_der() -> Seq<u8> {
    seq![0x30u8, 0x0d, 0x82, 0x0b, b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'c', b'o', b'm']
}

/// extKeyUsage `SEQUENCE { id-kp-serverAuth }`, DER.
pub open spec fn eku_server_auth_der() -> Seq<u8> {
    seq![0x30u8, 0x0a, 0x06, 0x08, 0x2b, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01]
}

/// extKeyUsage `SEQUENCE { anyExtendedKeyUsage }`, DER.
pub open spec fn eku_any_der() -> Seq<u8> {
    seq![0x30u8, 0x06, 0x06, 0x04, 0x55, 0x1d, 0x25, 0x00]
}

/// ExtKeyUsage { serverAuth }.
pub open spec fn eku_server_auth() -> crate::constraints::spec::ExtendedKeyUsage {
    crate::constraints::spec::ExtendedKeyUsage { purposes: seq![crate::constraints::spec::server_auth_oid()] }
}

/// ExtKeyUsage { anyExtendedKeyUsage }.
pub open spec fn eku_any() -> crate::constraints::spec::ExtendedKeyUsage {
    crate::constraints::spec::ExtendedKeyUsage { purposes: seq![crate::constraints::spec::any_extended_key_usage_oid()] }
}

/// ExtKeyUsage { id-kp-clientAuth }.
pub open spec fn eku_client_auth() -> crate::constraints::spec::ExtendedKeyUsage {
    crate::constraints::spec::ExtendedKeyUsage { purposes: seq![seq![1nat, 3, 6, 1, 5, 5, 7, 3, 2]] }
}

/// KeyUsage { keyCertSign, cRLSign }.
pub open spec fn key_cert_sign() -> crate::constraints::spec::KeyUsage {
    crate::constraints::spec::KeyUsage { bits: seq![0x06u8], bit_count: 7 }
}

/// KeyUsage { digitalSignature }.
pub open spec fn digital_signature() -> crate::constraints::spec::KeyUsage {
    crate::constraints::spec::KeyUsage { bits: seq![0x80u8], bit_count: 1 }
}

/// basicConstraints with this cA and pathLenConstraint.
pub open spec fn basic(ca: bool, path_len: Option<Seq<u8>>) -> crate::constraints::spec::BasicConstraints {
    crate::constraints::spec::BasicConstraints { ca, path_len_constraint: path_len }
}

/// NameConstraints with these permitted and excluded dNSName bases.
pub open spec fn dns_constraints(permitted: Option<Seq<u8>>, excluded: Option<Seq<u8>>)
    -> crate::name_constraints::spec::NameConstraints
{
    crate::name_constraints::spec::NameConstraints {
        permitted_subtrees: match permitted {
            Some(base) => Some(seq![crate::name_constraints::spec::GeneralSubtree {
                base: crate::name_constraints::spec::GeneralNameConstraint::DnsName(base) }]),
            None => None,
        },
        excluded_subtrees: match excluded {
            Some(base) => Some(seq![crate::name_constraints::spec::GeneralSubtree {
                base: crate::name_constraints::spec::GeneralNameConstraint::DnsName(base) }]),
            None => None,
        },
    }
}

/// A TBSCertificate with these names and key, valid 2020 to 2040.
pub open spec fn tbs(issuer: Seq<u8>, subject: Seq<u8>, spki: Seq<u8>) -> crate::tbs::spec::TbsCertificate {
    crate::tbs::spec::TbsCertificate {
        version: 2,
        serial_number_der: seq![0x02u8, 0x01, 0x01],
        signature: ecdsa_sha256(),
        issuer_der: issuer,
        not_before: day(2020, 1, 1),
        not_after: day(2040, 1, 1),
        subject_der: subject,
        subject_public_key_info_der: spki,
        issuer_unique_id_der: None, subject_unique_id_der: None,
        extensions_der: None, extensions_sequence_der: None,
        tbs_certificate_der: subject,
    }
}

/// A certificate `issuer -> subject` with key `spki`, signed under
/// `issuer_key`, with no extensions; `id` makes its DER distinct.
pub open spec fn cert(id: u8, issuer: Seq<u8>, subject: Seq<u8>, spki: Seq<u8>, issuer_key: Seq<u8>)
    -> super::parsed::spec::PathCert
{
    super::parsed::spec::PathCert {
        der: seq![id],
        envelope: crate::certificate::spec::CertificateEnvelope {
            tbs_certificate_der: subject, signature_algorithm: ecdsa_sha256(),
            signature_unused_bits: 0, signature_bits: issuer_key,
        },
        tbs: tbs(issuer, subject, spki),
        extensions: seq![],
        basic: None, key_usage: None, eku: None, name_constraints: None, san: None,
        require_explicit_policy: None, has_policy_mappings: false,
        signature: crate::signature_algorithm::spec::PreparedSignature {
            tbs_algorithm: ecdsa_sha256(), outer_algorithm: ecdsa_sha256(),
            class: crate::signature_algorithm::spec::AlgorithmClass::Ecdsa(
                crate::signature_algorithm::spec::EcdsaHash::Sha256),
            tbs_der: subject, signature_bits: issuer_key, signature_unused_bits: 0,
        },
    }
}

/// A CA certificate as the profile wants it: basicConstraints cA, keyUsage
/// keyCertSign, no extKeyUsage.
pub open spec fn ca(id: u8, issuer: Seq<u8>, subject: Seq<u8>, spki: Seq<u8>, issuer_key: Seq<u8>)
    -> super::parsed::spec::PathCert
{
    super::parsed::spec::PathCert {
        basic: Some(basic(true, None)), key_usage: Some(key_cert_sign()),
        ..cert(id, issuer, subject, spki, issuer_key)
    }
}

/// A leaf for `example.com`: subjectAltName and extKeyUsage serverAuth, both
/// as extensions (which `leaf::spec::check_extensions` decodes) and decoded.
pub open spec fn leaf_cert(id: u8, issuer: Seq<u8>, issuer_key: Seq<u8>) -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert {
        extensions: seq![
            extension(crate::extensions::spec::subject_alt_name_oid(), false, san_example_com_der()),
            extension(crate::leaf::spec::extended_key_usage_extension_oid(), false, eku_server_auth_der()),
        ],
        eku: Some(eku_server_auth()),
        san: Some(crate::extensions::spec::SubjectAltName {
            names: seq![crate::extensions::spec::GeneralName::DnsName(example_com())] }),
        ..cert(id, issuer, leaf_name(), key(9), issuer_key)
    }
}

/// The anchor `CN=roo` with key 1, valid 2020 to 2040, unconstrained.
pub open spec fn anchor() -> super::parsed::spec::Anchor {
    super::parsed::spec::Anchor {
        subject_der: root_name(), spki_der: key(1), name_constraints: None, path_len: None,
        not_before: day(2020, 1, 1), not_after: day(2040, 1, 1), server_distrust_after: None,
    }
}

/// The anchor with nameConstraints.
pub open spec fn anchor_constrained(value: crate::name_constraints::spec::NameConstraints) -> super::parsed::spec::Anchor {
    super::parsed::spec::Anchor { name_constraints: Some(value), ..anchor() }
}

/// The anchor with a pathLenConstraint.
pub open spec fn anchor_path_len(p: nat) -> super::parsed::spec::Anchor {
    super::parsed::spec::Anchor { path_len: Some(p), ..anchor() }
}

/// The intermediate `roo -> int`, key 2.
pub open spec fn int() -> super::parsed::spec::PathCert { ca(10, root_name(), int_name(), key(2), key(1)) }

/// The intermediate `int -> in2`, key 3.
pub open spec fn in2() -> super::parsed::spec::PathCert { ca(11, int_name(), in2_name(), key(3), key(2)) }

/// The intermediate `in2 -> in3`, key 4.
pub open spec fn in3() -> super::parsed::spec::PathCert { ca(12, in2_name(), in3_name(), key(4), key(3)) }

/// A self-issued intermediate `int -> int`, keeping key 2 (a re-issue).
pub open spec fn int_self() -> super::parsed::spec::PathCert { ca(13, int_name(), int_name(), key(2), key(2)) }

/// The leaf under `int`.
pub open spec fn leaf() -> super::parsed::spec::PathCert { leaf_cert(20, int_name(), key(2)) }

/// The leaf under `in2`.
pub open spec fn leaf_under_in2() -> super::parsed::spec::PathCert { leaf_cert(21, in2_name(), key(3)) }

/// The leaf under `in3`.
pub open spec fn leaf_under_in3() -> super::parsed::spec::PathCert { leaf_cert(22, in3_name(), key(4)) }

/// The leaf directly under the anchor.
pub open spec fn leaf_under_root() -> super::parsed::spec::PathCert { leaf_cert(23, root_name(), key(1)) }

/// `anchor -> int -> leaf` under `process` with the production `revoked`.
pub open spec fn run(anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>)
    -> Result<Seq<u8>, PathError>
{
    process(link(), not_revoked(), anchor, certs, now())
}

/// The profile of a path at `now` for `example.com`.
pub open spec fn profile_of(anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>)
    -> Result<(), PathError>
{
    super::profile::path_profile(anchor, certs, reference(), now())
}

/// The key a successful path returns.
pub open spec fn leaf_key() -> Result<Seq<u8>, PathError> { Ok(key(9)) }

// ---------------------------------------------------------------------------
// Accepted paths
// ---------------------------------------------------------------------------

/// A two-certificate path verifies and returns the leaf's key (§6.1.6).
pub proof fn lemma_two_certificate_path()
    ensures run(anchor(), seq![int(), leaf()]) == leaf_key(),
{
    assert(run(anchor(), seq![int(), leaf()]) == leaf_key()) by (compute_only);
}

/// A leaf directly under the anchor (n = 1): explicit_policy starts at
/// n + 1 = 2 (§6.1.2 (d)), so §6.1.5 (a) leaves 1 and the path succeeds.
pub proof fn lemma_leaf_under_anchor()
    ensures run(anchor(), seq![leaf_under_root()]) == leaf_key(),
{
    assert(run(anchor(), seq![leaf_under_root()]) == leaf_key()) by (compute_only);
}

/// §6.1.3 (a)(2): validity is inclusive at notAfter.
pub proof fn lemma_valid_at_not_after()
    ensures process(link(), not_revoked(), anchor(), seq![leaf_under_root()], day(2040, 1, 1)) == leaf_key(),
{
    assert(process(link(), not_revoked(), anchor(), seq![leaf_under_root()], day(2040, 1, 1)) == leaf_key())
        by (compute_only);
}

/// The profile accepts the two-certificate path.
pub proof fn lemma_profile_accepts()
    ensures profile_of(anchor(), seq![int(), leaf()]) == Ok::<(), PathError>(()),
{
    assert(profile_of(anchor(), seq![int(), leaf()]) == Ok::<(), PathError>(())) by (compute_only);
}

// ---------------------------------------------------------------------------
// §6.1.3 (a): signature, validity, revocation, name chaining
// ---------------------------------------------------------------------------

/// §6.1.3 (a)(1): a certificate whose signature is not under the working
/// key fails.
pub proof fn lemma_bad_signature()
    ensures run(anchor(), seq![int(), leaf_cert(20, int_name(), key(7))]) == Err::<Seq<u8>, PathError>(PathError::BadSignature),
{
    assert(run(anchor(), seq![int(), leaf_cert(20, int_name(), key(7))]) == Err::<Seq<u8>, PathError>(PathError::BadSignature))
        by (compute_only);
}

/// A certificate with an unsupported signature algorithm.
pub open spec fn unsupported_leaf() -> super::parsed::spec::PathCert {
    let base = leaf_under_root();
    super::parsed::spec::PathCert {
        signature: crate::signature_algorithm::spec::PreparedSignature {
            class: crate::signature_algorithm::spec::AlgorithmClass::Unsupported, ..base.signature },
        ..base
    }
}

/// §6.1.3 (a)(1), (R): an unsupported algorithm refuses, even under a link
/// function that would accept it.
pub proof fn lemma_unsupported_algorithm()
    ensures run(anchor(), seq![unsupported_leaf()]) == Err::<Seq<u8>, PathError>(PathError::UnsupportedAlgorithm),
{
    assert(run(anchor(), seq![unsupported_leaf()]) == Err::<Seq<u8>, PathError>(PathError::UnsupportedAlgorithm))
        by (compute_only);
}

/// §6.1.3 (a)(2): one second after notAfter is outside the validity period.
pub proof fn lemma_expired()
    ensures process(link(), not_revoked(), anchor(), seq![leaf_under_root()],
        crate::time::spec::CertificateTime { year: 2040, month: 1, day: 1, hour: 0, minute: 0, second: 1 })
        == Err::<Seq<u8>, PathError>(PathError::Expired),
{
    assert(process(link(), not_revoked(), anchor(), seq![leaf_under_root()],
        crate::time::spec::CertificateTime { year: 2040, month: 1, day: 1, hour: 0, minute: 0, second: 1 })
        == Err::<Seq<u8>, PathError>(PathError::Expired)) by (compute_only);
}

/// §6.1.3 (a)(3): a revoked certificate fails.
pub proof fn lemma_revoked()
    ensures process(link(), all_revoked(), anchor(), seq![leaf_under_root()], now())
        == Err::<Seq<u8>, PathError>(PathError::Revoked),
{
    assert(process(link(), all_revoked(), anchor(), seq![leaf_under_root()], now())
        == Err::<Seq<u8>, PathError>(PathError::Revoked)) by (compute_only);
}

/// §6.1.3 (a)(4): certificate 1's issuer must be the anchor's name, even
/// when the signature verifies.
pub proof fn lemma_name_chaining()
    ensures run(anchor(), seq![leaf_cert(20, int_name(), key(1))]) == Err::<Seq<u8>, PathError>(PathError::NameChaining),
{
    assert(run(anchor(), seq![leaf_cert(20, int_name(), key(1))]) == Err::<Seq<u8>, PathError>(PathError::NameChaining))
        by (compute_only);
}

/// §6.1: the same certificate twice refuses the path (here a self-issued
/// re-issue that would otherwise chain to itself).
pub proof fn lemma_repeated_certificate()
    ensures run(anchor(), seq![int(), int_self(), int_self(), leaf()])
        == Err::<Seq<u8>, PathError>(PathError::RepeatedCertificate),
{
    assert(run(anchor(), seq![int(), int_self(), int_self(), leaf()])
        == Err::<Seq<u8>, PathError>(PathError::RepeatedCertificate)) by (compute_only);
}

// ---------------------------------------------------------------------------
// Name constraints: §6.1.3 (b), (c); §6.1.4 (g); RFC 5937 §3.2
// ---------------------------------------------------------------------------

/// RFC 5937 §3.2 bullet 2: the anchor's permitted `example.com` holds the
/// leaf's `example.com` (and the CN-only subjects, which a dNSName base does
/// not constrain).
pub proof fn lemma_anchor_constraints_permit()
    ensures run(anchor_constrained(dns_constraints(Some(example_com()), None)), seq![int(), leaf()]) == leaf_key(),
{
    assert(run(anchor_constrained(dns_constraints(Some(example_com()), None)), seq![int(), leaf()]) == leaf_key())
        by (compute_only);
}

/// RFC 5937 §3.2 bullet 2 with §6.1.3 (b): the anchor permits only
/// `other.com`, so the leaf's `example.com` fails.
pub proof fn lemma_anchor_constraints_refuse()
    ensures run(anchor_constrained(dns_constraints(Some(other_com()), None)), seq![int(), leaf()])
        == Err::<Seq<u8>, PathError>(PathError::NameConstraint),
{
    assert(run(anchor_constrained(dns_constraints(Some(other_com()), None)), seq![int(), leaf()])
        == Err::<Seq<u8>, PathError>(PathError::NameConstraint)) by (compute_only);
}

/// An intermediate whose nameConstraints permits only `other.com`.
pub open spec fn int_constrained() -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert { name_constraints: Some(dns_constraints(Some(other_com()), None)), ..int() }
}

/// §6.1.4 (g) then §6.1.3 (b): an intermediate's constraints apply to the
/// certificates below it.
pub proof fn lemma_intermediate_constraints_refuse()
    ensures run(anchor(), seq![int_constrained(), leaf()]) == Err::<Seq<u8>, PathError>(PathError::NameConstraint),
{
    assert(run(anchor(), seq![int_constrained(), leaf()]) == Err::<Seq<u8>, PathError>(PathError::NameConstraint))
        by (compute_only);
}

/// A self-issued intermediate whose own subjectAltName is `other.com`.
pub open spec fn int_self_with_san() -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert {
        san: Some(crate::extensions::spec::SubjectAltName {
            names: seq![crate::extensions::spec::GeneralName::DnsName(other_com())] }),
        ..int_self()
    }
}

/// (R) Self-issued intermediates are checked (Firefox): the anchor excludes
/// `other.com`, and the self-issued intermediate's own name fails §6.1.3
/// (c), which RFC 5280 and Chrome would skip; the leaf's `example.com` is
/// fine.
pub proof fn lemma_self_issued_intermediate_checked()
    ensures run(anchor_constrained(dns_constraints(None, Some(other_com()))),
        seq![int(), int_self_with_san(), leaf_cert(20, int_name(), key(2))])
        == Err::<Seq<u8>, PathError>(PathError::NameConstraint),
{
    assert(run(anchor_constrained(dns_constraints(None, Some(other_com()))),
        seq![int(), int_self_with_san(), leaf_cert(20, int_name(), key(2))])
        == Err::<Seq<u8>, PathError>(PathError::NameConstraint)) by (compute_only);
}

/// §6.1.4 (g), P4: a dNSName base with a leading period is unsupported and
/// refuses the path, in an intermediate or in the anchor.
pub proof fn lemma_unsupported_constraints()
    ensures
        run(anchor(), seq![super::parsed::spec::PathCert {
            name_constraints: Some(dns_constraints(Some(seq![b'.', b'c', b'o', b'm']), None)), ..int() }, leaf()])
            == Err::<Seq<u8>, PathError>(PathError::NameConstraintUnsupported),
        run(anchor_constrained(dns_constraints(Some(seq![b'.', b'c', b'o', b'm']), None)), seq![int(), leaf()])
            == Err::<Seq<u8>, PathError>(PathError::NameConstraintUnsupported),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert {
        name_constraints: Some(dns_constraints(Some(seq![b'.', b'c', b'o', b'm']), None)), ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::NameConstraintUnsupported)) by (compute_only);
    assert(run(anchor_constrained(dns_constraints(Some(seq![b'.', b'c', b'o', b'm']), None)), seq![int(), leaf()])
        == Err::<Seq<u8>, PathError>(PathError::NameConstraintUnsupported)) by (compute_only);
}

// ---------------------------------------------------------------------------
// explicit_policy: §6.1.2 (d), §6.1.3 (f), §6.1.4 (h), (i), §6.1.5 (a), (b), (g)
// ---------------------------------------------------------------------------

/// An intermediate with policyConstraints requireExplicitPolicy `r`.
pub open spec fn int_require(r: nat) -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert { require_explicit_policy: Some(r), ..int() }
}

/// §6.1.4 (i)(1) and §6.1.5 (a): requireExplicitPolicy 1 on the
/// intermediate leaves explicit_policy 1 for the leaf, which the wrap-up
/// decrements to 0: the RFC then needs a non-NULL policy tree, which is not
/// modelled, so (R) the path is refused. With 2 it succeeds.
pub proof fn lemma_require_explicit_policy_counts_the_leaf()
    ensures
        run(anchor(), seq![int_require(1), leaf()]) == Err::<Seq<u8>, PathError>(PathError::PolicyRequired),
        run(anchor(), seq![int_require(2), leaf()]) == leaf_key(),
{
    assert(run(anchor(), seq![int_require(1), leaf()]) == Err::<Seq<u8>, PathError>(PathError::PolicyRequired))
        by (compute_only);
    assert(run(anchor(), seq![int_require(2), leaf()]) == leaf_key()) by (compute_only);
}

/// §6.1.3 (f) reports first: requireExplicitPolicy 0 makes the next
/// certificate fail (f), before §6.1.4 (k) would refuse it as a non-CA.
pub proof fn lemma_policy_check_runs_before_preparation()
    ensures run(anchor(), seq![int_require(0), super::parsed::spec::PathCert { basic: Some(basic(false, None)), ..in2() },
        leaf_under_in2()]) == Err::<Seq<u8>, PathError>(PathError::PolicyRequired),
{
    assert(run(anchor(), seq![int_require(0), super::parsed::spec::PathCert { basic: Some(basic(false, None)), ..in2() },
        leaf_under_in2()]) == Err::<Seq<u8>, PathError>(PathError::PolicyRequired)) by (compute_only);
}

/// §6.1.5 (b): requireExplicitPolicy 0 on the leaf sets explicit_policy to
/// 0, and (g) then refuses (R: no policy tree).
pub proof fn lemma_leaf_require_explicit_policy_zero()
    ensures run(anchor(), seq![super::parsed::spec::PathCert { require_explicit_policy: Some(0), ..leaf_under_root() }])
        == Err::<Seq<u8>, PathError>(PathError::PolicyRequired),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert { require_explicit_policy: Some(0), ..leaf_under_root() }])
        == Err::<Seq<u8>, PathError>(PathError::PolicyRequired)) by (compute_only);
}

/// §6.1.4 (h): a self-issued certificate does not decrement explicit_policy.
/// requireExplicitPolicy 2 on `int`, then a self-issued `int`, then the
/// leaf: 2 stays 2 across the self-issued one, and the wrap-up leaves 1.
pub proof fn lemma_self_issued_keeps_explicit_policy()
    ensures run(anchor(), seq![int_require(2), int_self(), leaf_cert(20, int_name(), key(2))]) == leaf_key(),
{
    assert(run(anchor(), seq![int_require(2), int_self(), leaf_cert(20, int_name(), key(2))]) == leaf_key())
        by (compute_only);
}

// ---------------------------------------------------------------------------
// §6.1.4 (a), (k), (l), (m), (n), (o); §6.1.5 (f)
// ---------------------------------------------------------------------------

/// §6.1.4 (a), (R): policyMappings refuses an intermediate.
pub proof fn lemma_policy_mappings_refused()
    ensures run(anchor(), seq![super::parsed::spec::PathCert { has_policy_mappings: true, ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::PolicyMappings),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert { has_policy_mappings: true, ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::PolicyMappings)) by (compute_only);
}

/// §6.1.4 (k): an intermediate with cA FALSE, and a version 1 intermediate,
/// are not CAs.
pub proof fn lemma_not_ca()
    ensures
        run(anchor(), seq![super::parsed::spec::PathCert { basic: Some(basic(false, None)), ..int() }, leaf()])
            == Err::<Seq<u8>, PathError>(PathError::NotCa),
        run(anchor(), seq![super::parsed::spec::PathCert { tbs: crate::tbs::spec::TbsCertificate { version: 0, ..int().tbs }, ..int() }, leaf()])
            == Err::<Seq<u8>, PathError>(PathError::NotCa),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert { basic: Some(basic(false, None)), ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::NotCa)) by (compute_only);
    assert(run(anchor(), seq![super::parsed::spec::PathCert { tbs: crate::tbs::spec::TbsCertificate { version: 0, ..int().tbs }, ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::NotCa)) by (compute_only);
}

/// An intermediate with pathLenConstraint `p` (one octet).
pub open spec fn int_path_len(p: u8) -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert { basic: Some(basic(true, Some(seq![p]))), ..int() }
}

/// §6.1.4 (l), (m): pathLenConstraint 0 on `int` allows no further
/// non-self-issued intermediate.
pub proof fn lemma_path_len_zero()
    ensures run(anchor(), seq![int_path_len(0), in2(), leaf_under_in2()]) == Err::<Seq<u8>, PathError>(PathError::PathLen),
{
    assert(run(anchor(), seq![int_path_len(0), in2(), leaf_under_in2()]) == Err::<Seq<u8>, PathError>(PathError::PathLen))
        by (compute_only);
}

/// §6.1.4 (l): a self-issued intermediate does not count. With
/// pathLenConstraint 1 on `int`, a self-issued `int` and then `in2` fit.
pub proof fn lemma_path_len_skips_self_issued()
    ensures run(anchor(), seq![int_path_len(1), int_self(), in2(), leaf_under_in2()]) == leaf_key(),
{
    assert(run(anchor(), seq![int_path_len(1), int_self(), in2(), leaf_under_in2()]) == leaf_key()) by (compute_only);
}

/// RFC 5937 §3.2 bullet 8: an anchor pathLenConstraint 0 allows no
/// intermediate; 1 allows one.
pub proof fn lemma_anchor_path_len()
    ensures
        run(anchor_path_len(0), seq![int(), leaf()]) == Err::<Seq<u8>, PathError>(PathError::PathLen),
        run(anchor_path_len(1), seq![int(), leaf()]) == leaf_key(),
{
    assert(run(anchor_path_len(0), seq![int(), leaf()]) == Err::<Seq<u8>, PathError>(PathError::PathLen)) by (compute_only);
    assert(run(anchor_path_len(1), seq![int(), leaf()]) == leaf_key()) by (compute_only);
}

/// §6.1.4 (n): a keyUsage without keyCertSign refuses.
pub proof fn lemma_key_usage_without_key_cert_sign()
    ensures run(anchor(), seq![super::parsed::spec::PathCert { key_usage: Some(digital_signature()), ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::KeyUsage),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert { key_usage: Some(digital_signature()), ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::KeyUsage)) by (compute_only);
}

/// §6.1.4 (o): an unknown critical extension, and a critical
/// certificatePolicies (not processed, design §1.6), refuse an
/// intermediate; a critical policyConstraints is processed.
pub proof fn lemma_intermediate_critical_extensions()
    ensures
        run(anchor(), seq![super::parsed::spec::PathCert { extensions: seq![extension(unknown_oid(), true, seq![])], ..int() }, leaf()])
            == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension),
        run(anchor(), seq![super::parsed::spec::PathCert { extensions: seq![extension(certificate_policies_oid(), true, seq![])], ..int() }, leaf()])
            == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension),
        run(anchor(), seq![super::parsed::spec::PathCert { extensions: seq![extension(
            crate::policy_constraints::spec::policy_constraints_oid(), true, seq![])], ..int() }, leaf()]) == leaf_key(),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert { extensions: seq![extension(unknown_oid(), true, seq![])], ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension)) by (compute_only);
    assert(run(anchor(), seq![super::parsed::spec::PathCert { extensions: seq![extension(certificate_policies_oid(), true, seq![])], ..int() }, leaf()])
        == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension)) by (compute_only);
    assert(run(anchor(), seq![super::parsed::spec::PathCert { extensions: seq![extension(
        crate::policy_constraints::spec::policy_constraints_oid(), true, seq![])], ..int() }, leaf()]) == leaf_key())
        by (compute_only);
}

/// §6.1.5 (f): an unknown critical extension on the target refuses, and so
/// does a critical nameConstraints there.
pub proof fn lemma_leaf_critical_extensions()
    ensures
        run(anchor(), seq![super::parsed::spec::PathCert {
            extensions: leaf_under_root().extensions.push(extension(unknown_oid(), true, seq![])), ..leaf_under_root() }])
            == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension),
        run(anchor(), seq![super::parsed::spec::PathCert {
            extensions: leaf_under_root().extensions.push(extension(
                crate::name_constraints::spec::name_constraints_oid(), true, seq![])), ..leaf_under_root() }])
            == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension),
{
    assert(run(anchor(), seq![super::parsed::spec::PathCert {
        extensions: leaf_under_root().extensions.push(extension(unknown_oid(), true, seq![])), ..leaf_under_root() }])
        == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension)) by (compute_only);
    assert(run(anchor(), seq![super::parsed::spec::PathCert {
        extensions: leaf_under_root().extensions.push(extension(
            crate::name_constraints::spec::name_constraints_oid(), true, seq![])), ..leaf_under_root() }])
        == Err::<Seq<u8>, PathError>(PathError::UnknownCriticalExtension)) by (compute_only);
}

/// §6.1.4 (c), (d): the working name and key advance, so a third
/// certificate must chain to the second.
pub proof fn lemma_three_certificate_path()
    ensures run(anchor(), seq![int(), in2(), in3(), leaf_under_in3()]) == leaf_key(),
{
    assert(run(anchor(), seq![int(), in2(), in3(), leaf_under_in3()]) == leaf_key()) by (compute_only);
}

// ---------------------------------------------------------------------------
// The profile (`profile.rs`)
// ---------------------------------------------------------------------------

/// (R) A leaf without extKeyUsage is refused.
pub proof fn lemma_leaf_without_eku()
    ensures profile_of(anchor(), seq![super::parsed::spec::PathCert {
        extensions: seq![extension(crate::extensions::spec::subject_alt_name_oid(), false, san_example_com_der())],
        eku: None, ..leaf_under_root() }]) == Err::<(), PathError>(PathError::ExtendedKeyUsage),
{
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert {
        extensions: seq![extension(crate::extensions::spec::subject_alt_name_oid(), false, san_example_com_der())],
        eku: None, ..leaf_under_root() }]) == Err::<(), PathError>(PathError::ExtendedKeyUsage)) by (compute_only);
}

/// (R) A leaf carrying nameConstraints (non-critical) is refused
/// (`rfc5280::nc::not-allowed-in-ee-noncritical`).
pub proof fn lemma_leaf_name_constraints()
    ensures profile_of(anchor(), seq![super::parsed::spec::PathCert {
        name_constraints: Some(dns_constraints(Some(example_com()), None)), ..leaf_under_root() }])
        == Err::<(), PathError>(PathError::LeafNameConstraints),
{
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert {
        name_constraints: Some(dns_constraints(Some(example_com()), None)), ..leaf_under_root() }])
        == Err::<(), PathError>(PathError::LeafNameConstraints)) by (compute_only);
}

/// The leaf checks: a leaf for another name fails; one whose only purpose
/// is anyExtendedKeyUsage fails.
pub proof fn lemma_leaf_checks()
    ensures
        super::profile::path_profile(anchor(), seq![leaf_under_root()],
            crate::spec::ReferenceIdentity::Dns(other_com()), now()) == Err::<(), PathError>(PathError::Leaf),
        profile_of(anchor(), seq![super::parsed::spec::PathCert {
            extensions: seq![
                extension(crate::extensions::spec::subject_alt_name_oid(), false, san_example_com_der()),
                extension(crate::leaf::spec::extended_key_usage_extension_oid(), false, eku_any_der())],
            eku: Some(eku_any()), ..leaf_under_root() }]) == Err::<(), PathError>(PathError::Leaf),
{
    assert(super::profile::path_profile(anchor(), seq![leaf_under_root()],
        crate::spec::ReferenceIdentity::Dns(other_com()), now()) == Err::<(), PathError>(PathError::Leaf)) by (compute_only);
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert {
        extensions: seq![
            extension(crate::extensions::spec::subject_alt_name_oid(), false, san_example_com_der()),
            extension(crate::leaf::spec::extended_key_usage_extension_oid(), false, eku_any_der())],
        eku: Some(eku_any()), ..leaf_under_root() }]) == Err::<(), PathError>(PathError::Leaf)) by (compute_only);
}

/// (R) An intermediate without keyUsage is refused by the profile (§6.1.4
/// (n) alone accepts it).
pub proof fn lemma_intermediate_without_key_usage()
    ensures
        profile_of(anchor(), seq![super::parsed::spec::PathCert { key_usage: None, ..int() }, leaf()])
            == Err::<(), PathError>(PathError::KeyUsage),
        run(anchor(), seq![super::parsed::spec::PathCert { key_usage: None, ..int() }, leaf()]) == leaf_key(),
{
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert { key_usage: None, ..int() }, leaf()])
        == Err::<(), PathError>(PathError::KeyUsage)) by (compute_only);
    assert(run(anchor(), seq![super::parsed::spec::PathCert { key_usage: None, ..int() }, leaf()]) == leaf_key())
        by (compute_only);
}

/// (R) Intermediate extKeyUsage: serverAuth passes; anyExtendedKeyUsage
/// alone, and clientAuth alone, are refused.
pub proof fn lemma_intermediate_eku()
    ensures
        profile_of(anchor(), seq![super::parsed::spec::PathCert { eku: Some(eku_server_auth()), ..int() }, leaf()])
            == Ok::<(), PathError>(()),
        profile_of(anchor(), seq![super::parsed::spec::PathCert { eku: Some(eku_any()), ..int() }, leaf()])
            == Err::<(), PathError>(PathError::ExtendedKeyUsage),
        profile_of(anchor(), seq![super::parsed::spec::PathCert { eku: Some(eku_client_auth()), ..int() }, leaf()])
            == Err::<(), PathError>(PathError::ExtendedKeyUsage),
{
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert { eku: Some(eku_server_auth()), ..int() }, leaf()])
        == Ok::<(), PathError>(())) by (compute_only);
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert { eku: Some(eku_any()), ..int() }, leaf()])
        == Err::<(), PathError>(PathError::ExtendedKeyUsage)) by (compute_only);
    assert(profile_of(anchor(), seq![super::parsed::spec::PathCert { eku: Some(eku_client_auth()), ..int() }, leaf()])
        == Err::<(), PathError>(PathError::ExtendedKeyUsage)) by (compute_only);
}

/// (R) Design Q9: an anchor certificate past its notAfter is refused.
pub proof fn lemma_anchor_expired()
    ensures profile_of(super::parsed::spec::Anchor { not_after: day(2026, 1, 1), ..anchor() }, seq![int(), leaf()])
        == Err::<(), PathError>(PathError::AnchorExpired),
{
    assert(profile_of(super::parsed::spec::Anchor { not_after: day(2026, 1, 1), ..anchor() }, seq![int(), leaf()])
        == Err::<(), PathError>(PathError::AnchorExpired)) by (compute_only);
}

/// A leaf issued 2025-01-01, valid to 2027-01-01.
pub open spec fn leaf_2025() -> super::parsed::spec::PathCert {
    let base = leaf_under_root();
    super::parsed::spec::PathCert {
        tbs: crate::tbs::spec::TbsCertificate { not_before: day(2025, 1, 1), not_after: day(2027, 1, 1), ..base.tbs },
        ..base
    }
}

/// The anchor with this server-distrust-after time.
pub open spec fn anchor_distrust(after: crate::time::spec::CertificateTime) -> super::parsed::spec::Anchor {
    super::parsed::spec::Anchor { server_distrust_after: Some(after), ..anchor() }
}

/// (R) NSS distrust-after compares the leaf's notBefore: issued 2025, after
/// a 2024 distrust date, is refused; issued 2025, before a 2026 date (though
/// valid past it), and issued exactly at the date, are accepted.
pub proof fn lemma_distrust_after()
    ensures
        profile_of(anchor_distrust(day(2024, 1, 1)), seq![leaf_2025()]) == Err::<(), PathError>(PathError::Distrusted),
        profile_of(anchor_distrust(day(2026, 1, 1)), seq![leaf_2025()]) == Ok::<(), PathError>(()),
        profile_of(anchor_distrust(day(2025, 1, 1)), seq![leaf_2025()]) == Ok::<(), PathError>(()),
{
    assert(profile_of(anchor_distrust(day(2024, 1, 1)), seq![leaf_2025()]) == Err::<(), PathError>(PathError::Distrusted))
        by (compute_only);
    assert(profile_of(anchor_distrust(day(2026, 1, 1)), seq![leaf_2025()]) == Ok::<(), PathError>(())) by (compute_only);
    assert(profile_of(anchor_distrust(day(2025, 1, 1)), seq![leaf_2025()]) == Ok::<(), PathError>(())) by (compute_only);
}

// ---------------------------------------------------------------------------
// One candidate (`verifier.rs`)
// ---------------------------------------------------------------------------

/// The environment with `max_intermediates` m.
pub open spec fn environment(m: nat) -> super::verifier::Environment {
    super::verifier::Environment { link: link(), revoked: not_revoked(), max_intermediates: m }
}

/// The verdict on a candidate over the pool `[int, int_self]` and `leaf()`.
pub open spec fn verdict(m: nat, path: Seq<nat>) -> Result<Seq<u8>, PathError> {
    super::verifier::candidate_verdict(environment(m), seq![anchor()], seq![Some(int()), Some(int_self())], leaf(),
        super::verifier::Candidate { anchor: 0, path }, reference(), now())
}

/// The candidate `anchor -> pool[0] -> leaf` is valid, with the leaf's key.
pub proof fn lemma_candidate_valid()
    ensures verdict(6, seq![0nat]) == leaf_key(),
{
    assert(verdict(6, seq![0nat]) == leaf_key()) by (compute_only);
}

/// Design §1.12: with `max_intermediates` 0, a candidate with one
/// intermediate is too long.
pub proof fn lemma_candidate_too_long()
    ensures verdict(0, seq![0nat]) == Err::<Seq<u8>, PathError>(PathError::TooManyIntermediates),
{
    assert(verdict(0, seq![0nat]) == Err::<Seq<u8>, PathError>(PathError::TooManyIntermediates)) by (compute_only);
}

/// Design §2.6: a candidate naming one pool index twice is not a candidate.
pub proof fn lemma_candidate_repeats_index()
    ensures verdict(6, seq![0nat, 1, 1]) == Err::<Seq<u8>, PathError>(PathError::UnknownIssuer),
{
    assert(verdict(6, seq![0nat, 1, 1]) == Err::<Seq<u8>, PathError>(PathError::UnknownIssuer)) by (compute_only);
}

/// Seventeen empty presented certificates.
pub open spec fn seventeen() -> Seq<Seq<u8>> {
    seq![seq![], seq![], seq![], seq![], seq![], seq![], seq![], seq![], seq![],
        seq![], seq![], seq![], seq![], seq![], seq![], seq![], seq![]]
}

/// Design §1.12 (Firefox): the number of presented certificates is not
/// capped, so seventeen are refused only because the first does not parse;
/// none at all is malformed.
pub proof fn lemma_presented_not_capped()
    ensures
        super::verifier::chain_inputs(seventeen(), 0) == Err::<super::verifier::ChainInputs, PathError>(PathError::Malformed),
        super::verifier::chain_inputs(seq![], 0) == Err::<super::verifier::ChainInputs, PathError>(PathError::Malformed),
{
    assert(super::verifier::chain_inputs(seventeen(), 0) == Err::<super::verifier::ChainInputs, PathError>(PathError::Malformed)) by (compute_only);
    assert(super::verifier::chain_inputs(seq![], 0) == Err::<super::verifier::ChainInputs, PathError>(PathError::Malformed)) by (compute_only);
}

} // verus!
