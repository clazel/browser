//! Known answers for the `PathCert` and `Anchor` spec, each proven by
//! evaluation. They are also the theorems that the certified mutations in
//! `mutations.json` contradict.
//!
//! The examples work over decoded structures (`Extension`, `BasicConstraints`,
//! `KeyUsage`, ...), not DER: the compute-only evaluator reaches its
//! recursion limit on a whole certificate, and the decoders' own byte-level
//! behaviour is pinned by their specs' examples. What the examples cover is
//! what `parsed/spec.rs` adds to the decoders: which extensions are looked for
//! and under which OID, the anchor checks (RFC 5937 §2 and §3.2, the design's
//! role, EKU and policy refusals), the number a SkipCerts or pathLenConstraint
//! spells, and the distrust-after text. Whole certificates, and the real
//! Mozilla roots, are in `tests/path_parsed.rs`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Structures used below
// ---------------------------------------------------------------------------

/// An extension with an empty value.
pub open spec fn extension(oid: Seq<nat>, critical: bool) -> crate::extensions::spec::Extension {
    crate::extensions::spec::Extension { oid, critical, value: seq![] }
}

/// An extension with the given value.
pub open spec fn extension_with(oid: Seq<nat>, value: Seq<u8>) -> crate::extensions::spec::Extension {
    crate::extensions::spec::Extension { oid, critical: false, value }
}

/// An OID no decoder knows.
pub open spec fn unknown_oid() -> Seq<nat> { seq![1nat, 2, 3] }

/// `BasicConstraints { cA, pathLenConstraint }`.
pub open spec fn basic(ca: bool, path_len: Option<Seq<u8>>) -> crate::constraints::spec::BasicConstraints {
    crate::constraints::spec::BasicConstraints { ca, path_len_constraint: path_len }
}

/// KeyUsage with only keyCertSign (bit 5) set.
pub open spec fn key_cert_sign_only() -> crate::constraints::spec::KeyUsage {
    crate::constraints::spec::KeyUsage { bits: seq![0x04u8], bit_count: 6 }
}

/// KeyUsage with only digitalSignature (bit 0) set.
pub open spec fn digital_signature_only() -> crate::constraints::spec::KeyUsage {
    crate::constraints::spec::KeyUsage { bits: seq![0x80u8], bit_count: 1 }
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

/// PolicyConstraints { requireExplicitPolicy 2, inhibitPolicyMapping 9 }.
pub open spec fn policy_constraints_2_9() -> crate::policy_constraints::spec::PolicyConstraints {
    crate::policy_constraints::spec::PolicyConstraints {
        require_explicit_policy: Some(seq![2u8]), inhibit_policy_mapping: Some(seq![9u8]),
    }
}

/// A TBSCertificate without extensions (a v1 certificate).
pub open spec fn tbs_without_extensions() -> crate::tbs::spec::TbsCertificate {
    crate::tbs::spec::TbsCertificate {
        version: 0,
        serial_number_der: seq![0x02u8, 0x01, 0x01],
        signature: crate::certificate::spec::AlgorithmIdentifier { oid: seq![1nat, 2, 3], parameters_der: None },
        issuer_der: seq![0x30u8, 0x02, 0x05, 0x00],
        not_before: crate::time::spec::CertificateTime { year: 2020, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
        not_after: crate::time::spec::CertificateTime { year: 2040, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
        subject_der: seq![0x30u8, 0x02, 0x05, 0x00],
        subject_public_key_info_der: seq![0x30u8, 0x00],
        issuer_unique_id_der: None, subject_unique_id_der: None,
        extensions_der: None, extensions_sequence_der: None,
        tbs_certificate_der: seq![0x30u8, 0x00],
    }
}

/// `20260415235959Z`: a GeneralizedTime string, not a UTCTime.
pub open spec fn distrust_text_generalized() -> Seq<u8> {
    seq![b'2', b'0', b'2', b'6', b'0', b'4', b'1', b'5', b'2', b'3', b'5', b'9', b'5', b'9', b'Z']
}

// ---------------------------------------------------------------------------
// The number a SkipCerts or pathLenConstraint spells (design §1.7)
// ---------------------------------------------------------------------------

/// The octets are a big-endian number: `01 00` is 256.
pub proof fn lemma_skip_certs_is_big_endian()
    ensures skip_certs_value(seq![0x01u8, 0x00u8]) == 256nat
{
    assert(skip_certs_value(seq![0x01u8, 0x00u8]) == 256nat) by (compute_only);
}

/// `requireExplicitPolicy` is the `[0]` field, not `inhibitPolicyMapping`.
pub proof fn lemma_require_explicit_policy_is_the_first_field()
    ensures require_explicit_policy_of(Some(policy_constraints_2_9())) == Some(2nat)
{
    assert(require_explicit_policy_of(Some(policy_constraints_2_9())) == Some(2nat)) by (compute_only);
}

/// No policyConstraints, no `requireExplicitPolicy`.
pub proof fn lemma_no_policy_constraints_no_require_explicit_policy()
    ensures require_explicit_policy_of(None) is None
{
    assert(require_explicit_policy_of(None) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// Which extensions are looked for
// ---------------------------------------------------------------------------

/// An extension with OID 2.5.29.33 is policyMappings (RFC 5280 §4.2.1.5).
pub proof fn lemma_policy_mappings_is_found()
    ensures has_extension(seq![extension(seq![2nat, 5, 29, 33], false)], policy_mappings_oid())
{
    assert(has_extension(seq![extension(seq![2nat, 5, 29, 33], false)], policy_mappings_oid())) by (compute_only);
}

/// A certificate with no extensions has no policyMappings.
pub proof fn lemma_no_extensions_no_policy_mappings()
    ensures !has_extension(seq![], policy_mappings_oid())
{
    assert(!has_extension(seq![], policy_mappings_oid())) by (compute_only);
}

/// An absent subjectAltName is not an error.
pub proof fn lemma_absent_subject_alt_name_is_none()
    ensures optional_subject_alt_name(seq![]) == Some(Option::<crate::extensions::spec::SubjectAltName>::None)
{
    assert(optional_subject_alt_name(seq![]) == Some(Option::<crate::extensions::spec::SubjectAltName>::None)) by (compute_only);
}

/// An absent nameConstraints is not an error.
pub proof fn lemma_absent_name_constraints_is_none()
    ensures optional_name_constraints(seq![]) == Some(Option::<crate::name_constraints::spec::NameConstraints>::None)
{
    assert(optional_name_constraints(seq![]) == Some(Option::<crate::name_constraints::spec::NameConstraints>::None)) by (compute_only);
}

/// An absent policyConstraints is not an error.
pub proof fn lemma_absent_policy_constraints_is_none()
    ensures optional_policy_constraints(seq![])
        == Some(Option::<crate::policy_constraints::spec::PolicyConstraints>::None)
{
    assert(optional_policy_constraints(seq![])
        == Some(Option::<crate::policy_constraints::spec::PolicyConstraints>::None)) by (compute_only);
}

/// An empty GeneralNames is malformed, so a subjectAltName that holds one
/// refuses the certificate (R).
pub proof fn lemma_malformed_subject_alt_name_refuses()
    ensures optional_subject_alt_name(
        seq![extension_with(crate::extensions::spec::subject_alt_name_oid(), seq![0x30u8, 0x00])]) is None
{
    assert(optional_subject_alt_name(
        seq![extension_with(crate::extensions::spec::subject_alt_name_oid(), seq![0x30u8, 0x00])]) is None) by (compute_only);
}

/// An empty `permittedSubtrees` is malformed, so the certificate is refused (R).
pub proof fn lemma_malformed_name_constraints_refuses()
    ensures optional_name_constraints(
        seq![extension_with(crate::name_constraints::spec::name_constraints_oid(), seq![0x30u8, 0x02, 0xa0, 0x00])]) is None
{
    assert(optional_name_constraints(
        seq![extension_with(crate::name_constraints::spec::name_constraints_oid(), seq![0x30u8, 0x02, 0xa0, 0x00])]) is None) by (compute_only);
}

/// An empty PolicyConstraints is refused by its decoder, so the certificate is (R).
pub proof fn lemma_malformed_policy_constraints_refuses()
    ensures optional_policy_constraints(
        seq![extension_with(crate::policy_constraints::spec::policy_constraints_oid(), seq![0x30u8, 0x00])]) is None
{
    assert(optional_policy_constraints(
        seq![extension_with(crate::policy_constraints::spec::policy_constraints_oid(), seq![0x30u8, 0x00])]) is None) by (compute_only);
}

/// A certificate with no `[3]` field has an empty Extensions list.
pub proof fn lemma_no_extensions_field_is_an_empty_list()
    ensures match tbs_extensions(tbs_without_extensions()) { Some(list) => list.len() == 0, None => false }
{
    assert(match tbs_extensions(tbs_without_extensions()) { Some(list) => list.len() == 0, None => false }) by (compute_only);
}

// ---------------------------------------------------------------------------
// The anchor (RFC 5937 §2 and §3.2; design §1.4, Q9)
// ---------------------------------------------------------------------------

/// RFC 5937 §2: critical extensions of the kinds the anchor reads are
/// recognized.
pub proof fn lemma_anchor_reads_critical_basic_constraints()
    ensures anchor_critical_supported(seq![extension(crate::leaf::spec::basic_constraints_oid(), true)], 0)
{
    assert(anchor_critical_supported(seq![extension(crate::leaf::spec::basic_constraints_oid(), true)], 0)) by (compute_only);
}

/// As above, for keyUsage.
pub proof fn lemma_anchor_reads_critical_key_usage()
    ensures anchor_critical_supported(seq![extension(crate::leaf::spec::key_usage_oid(), true)], 0)
{
    assert(anchor_critical_supported(seq![extension(crate::leaf::spec::key_usage_oid(), true)], 0)) by (compute_only);
}

/// As above, for extKeyUsage.
pub proof fn lemma_anchor_reads_critical_extended_key_usage()
    ensures anchor_critical_supported(seq![extension(crate::leaf::spec::extended_key_usage_extension_oid(), true)], 0)
{
    assert(anchor_critical_supported(seq![extension(crate::leaf::spec::extended_key_usage_extension_oid(), true)], 0)) by (compute_only);
}

/// As above, for nameConstraints (RFC 5937 §3.2 bullets 2 and 3).
pub proof fn lemma_anchor_reads_critical_name_constraints()
    ensures anchor_critical_supported(seq![extension(crate::name_constraints::spec::name_constraints_oid(), true)], 0)
{
    assert(anchor_critical_supported(seq![extension(crate::name_constraints::spec::name_constraints_oid(), true)], 0)) by (compute_only);
}

/// RFC 5937 §2: a critical extension the anchor does not read refuses it.
pub proof fn lemma_anchor_unknown_critical_extension_refuses()
    ensures !anchor_critical_supported(seq![extension(unknown_oid(), true)], 0)
{
    assert(!anchor_critical_supported(seq![extension(unknown_oid(), true)], 0)) by (compute_only);
}

/// A critical subjectAltName is not one the anchor reads either.
pub proof fn lemma_anchor_critical_subject_alt_name_refuses()
    ensures !anchor_critical_supported(seq![extension(crate::extensions::spec::subject_alt_name_oid(), true)], 0)
{
    assert(!anchor_critical_supported(seq![extension(crate::extensions::spec::subject_alt_name_oid(), true)], 0)) by (compute_only);
}

/// A non-critical extension of any kind is allowed.
pub proof fn lemma_anchor_noncritical_unknown_extension_is_allowed()
    ensures anchor_critical_supported(seq![extension(unknown_oid(), false)], 0)
{
    assert(anchor_critical_supported(seq![extension(unknown_oid(), false)], 0)) by (compute_only);
}

/// RFC 5937 §3.2 bullet 1: an empty Name is no name (R).
pub proof fn lemma_anchor_empty_subject_refuses()
    ensures !anchor_has_subject(seq![0x30u8, 0x00u8])
{
    assert(!anchor_has_subject(seq![0x30u8, 0x00u8])) by (compute_only);
}

/// A Name with one (here dummy) RDN is a name.
pub proof fn lemma_anchor_nonempty_subject_is_allowed()
    ensures anchor_has_subject(seq![0x30u8, 0x02u8, 0x05u8, 0x00u8])
{
    assert(anchor_has_subject(seq![0x30u8, 0x02u8, 0x05u8, 0x00u8])) by (compute_only);
}

/// RFC 5937 §3.2 bullets 5 to 7: an `inhibitAnyPolicy` extension refuses the anchor (R).
pub proof fn lemma_anchor_inhibit_any_policy_refuses()
    ensures !anchor_policy_inputs_absent(seq![extension(seq![2nat, 5, 29, 54], false)])
{
    assert(!anchor_policy_inputs_absent(seq![extension(seq![2nat, 5, 29, 54], false)])) by (compute_only);
}

/// As above, for `policyConstraints` (2.5.29.36).
pub proof fn lemma_anchor_policy_constraints_refuses()
    ensures !anchor_policy_inputs_absent(seq![extension(seq![2nat, 5, 29, 36], false)])
{
    assert(!anchor_policy_inputs_absent(seq![extension(seq![2nat, 5, 29, 36], false)])) by (compute_only);
}

/// RFC 5937 §3.2 bullet 4 (I): `certificatePolicies` (2.5.29.32) does not refuse.
pub proof fn lemma_anchor_certificate_policies_is_allowed()
    ensures anchor_policy_inputs_absent(seq![extension(seq![2nat, 5, 29, 32], false)])
{
    assert(anchor_policy_inputs_absent(seq![extension(seq![2nat, 5, 29, 32], false)])) by (compute_only);
}

/// The anchor's `path_len` is its pathLenConstraint (RFC 5937 §3.2 bullet 8).
pub proof fn lemma_anchor_path_len_is_the_constraint()
    ensures anchor_path_len(basic(true, Some(seq![3u8]))) == Some(3nat)
{
    assert(anchor_path_len(basic(true, Some(seq![3u8]))) == Some(3nat)) by (compute_only);
}

/// No pathLenConstraint, no `path_len`.
pub proof fn lemma_anchor_without_path_len()
    ensures anchor_path_len(basic(true, None)) is None
{
    assert(anchor_path_len(basic(true, None)) is None) by (compute_only);
}

/// (R) A non-CA is no anchor.
pub proof fn lemma_anchor_role_needs_ca()
    ensures !anchor_role_allowed(basic(false, None), Some(key_cert_sign_only()))
{
    assert(!anchor_role_allowed(basic(false, None), Some(key_cert_sign_only()))) by (compute_only);
}

/// (R) With keyUsage present, keyCertSign is required.
pub proof fn lemma_anchor_role_needs_key_cert_sign()
    ensures !anchor_role_allowed(basic(true, None), Some(digital_signature_only()))
{
    assert(!anchor_role_allowed(basic(true, None), Some(digital_signature_only()))) by (compute_only);
}

/// A CA with keyCertSign is an anchor.
pub proof fn lemma_anchor_role_accepts_a_ca_with_key_cert_sign()
    ensures anchor_role_allowed(basic(true, None), Some(key_cert_sign_only()))
{
    assert(anchor_role_allowed(basic(true, None), Some(key_cert_sign_only()))) by (compute_only);
}

/// keyUsage may be absent (design §1.4: "KeyUsage with keyCertSign if KeyUsage is present").
pub proof fn lemma_anchor_role_allows_absent_key_usage()
    ensures anchor_role_allowed(basic(true, None), None)
{
    assert(anchor_role_allowed(basic(true, None), None)) by (compute_only);
}

/// (R) An EKU with serverAuth is allowed.
pub proof fn lemma_anchor_eku_with_server_auth_is_allowed()
    ensures anchor_eku_allowed(Some(eku_server_auth()))
{
    assert(anchor_eku_allowed(Some(eku_server_auth()))) by (compute_only);
}

/// (R) anyExtendedKeyUsage alone does not allow an anchor.
pub proof fn lemma_anchor_eku_any_alone_refuses()
    ensures !anchor_eku_allowed(Some(eku_any()))
{
    assert(!anchor_eku_allowed(Some(eku_any()))) by (compute_only);
}

/// (R) An EKU without serverAuth refuses (limbo `webpki::eku::root-has-eku`).
pub proof fn lemma_anchor_eku_without_server_auth_refuses()
    ensures !anchor_eku_allowed(Some(eku_client_auth()))
{
    assert(!anchor_eku_allowed(Some(eku_client_auth()))) by (compute_only);
}

/// A root with no EKU, which is all 118 Mozilla roots, is allowed.
pub proof fn lemma_anchor_absent_eku_is_allowed()
    ensures anchor_eku_allowed(None)
{
    assert(anchor_eku_allowed(None)) by (compute_only);
}

/// A root without a distrust-after has none.
pub proof fn lemma_no_distrust_after_text_is_none()
    ensures match decode_distrust_after(None) { Some(None) => true, _ => false }
{
    assert(match decode_distrust_after(None) { Some(None) => true, _ => false }) by (compute_only);
}

/// (R) Text that is not a 13-octet UTCTime refuses the anchor: here a
/// GeneralizedTime string. (A positive decode, `260415235959Z` as 2026-04-15
/// 23:59:59, cannot be evaluated by `compute_only`, because `decode_time`'s
/// digit check is a quantifier; `tests/path_parsed.rs` pins it.)
pub proof fn lemma_distrust_after_text_must_decode()
    ensures decode_distrust_after(Some(distrust_text_generalized())) is None
{
    assert(decode_distrust_after(Some(distrust_text_generalized())) is None) by (compute_only);
}

/// Empty text does not decode either.
pub proof fn lemma_empty_distrust_after_text_refuses()
    ensures decode_distrust_after(Some(seq![])) is None
{
    assert(decode_distrust_after(Some(seq![])) is None) by (compute_only);
}

} // verus!
