//! Executable `parse_path_cert` and `anchor_from_root`, each proven equal to
//! its spec (`spec.rs`). They add no byte parsing: every step is a call to a
//! decoder that is itself proven against its own spec.

use crate::constraints::exec as constraints;
use crate::extensions::exec as extensions;
use crate::leaf::exec as leaf;
use crate::name_constraints::exec as name_constraints;
use crate::signature_algorithm::exec as signature;
use crate::time::exec::CertificateTime;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One certificate of a path, decoded. The borrowed fields point into the
/// certificate DER. The signature inputs are not kept as a
/// `PreparedSignatureInput` (which borrows the algorithm identifiers stored
/// here); `signature_class` is its class, and the rest of the spec's
/// `PreparedSignature` is read from the envelope and the TBS.
pub struct PathCert<'a> {
    /// The complete certificate DER.
    pub der: &'a [u8],
    /// RFC 5280 §4.1 outer fields.
    pub envelope: crate::certificate::exec::CertificateEnvelope<'a>,
    /// RFC 5280 §4.1.2 TBSCertificate fields.
    pub tbs: crate::tbs::exec::TbsCertificate<'a>,
    /// Every extension, in encoded order.
    pub extensions: Vec<extensions::Extension<'a>>,
    /// basicConstraints, if present.
    pub basic: Option<constraints::BasicConstraints<'a>>,
    /// keyUsage, if present.
    pub key_usage: Option<constraints::KeyUsage<'a>>,
    /// extKeyUsage, if present.
    pub eku: Option<constraints::ExtendedKeyUsage>,
    /// nameConstraints, if present.
    pub name_constraints: Option<name_constraints::NameConstraints<'a>>,
    /// subjectAltName, if present.
    pub san: Option<extensions::SubjectAltName<'a>>,
    /// The magnitude octets of `requireExplicitPolicy`, if present (at most 4).
    pub require_explicit_policy: Option<&'a [u8]>,
    /// Whether policyMappings is present.
    pub has_policy_mappings: bool,
    /// The class of the signature algorithm (RFC 5280 §4.1.1.2).
    pub signature_class: signature::AlgorithmClass,
}

/// A trust anchor extracted from a root certificate.
pub struct Anchor<'a> {
    /// The subject Name DER.
    pub subject_der: &'a [u8],
    /// The complete SubjectPublicKeyInfo DER.
    pub spki_der: &'a [u8],
    /// The anchor's nameConstraints, if present.
    pub name_constraints: Option<name_constraints::NameConstraints<'a>>,
    /// The pathLenConstraint magnitude octets, if present.
    pub path_len: Option<&'a [u8]>,
    /// The start of validity.
    pub not_before: CertificateTime,
    /// The end of validity.
    pub not_after: CertificateTime,
    /// NSS's distrust-after time, if the table has one.
    pub server_distrust_after: Option<CertificateTime>,
}

/// The magnitude octets of a SkipCerts or pathLenConstraint as the spec's number.
pub open spec fn view_magnitude(value: Option<&[u8]>) -> Option<nat> {
    match value {
        Some(octets) => Some(super::spec::skip_certs_value(octets@)),
        None => None,
    }
}

pub open spec fn view_eku_option(value: &Option<constraints::ExtendedKeyUsage>)
    -> Option<crate::constraints::spec::ExtendedKeyUsage>
{
    match value { Some(item) => Some(item@), None => None }
}

pub open spec fn view_san_option(value: &Option<extensions::SubjectAltName<'_>>)
    -> Option<crate::extensions::spec::SubjectAltName>
{
    match value { Some(item) => Some(extensions::view_subject_alt_name(item)), None => None }
}

pub open spec fn view_name_constraints_option(value: &Option<name_constraints::NameConstraints<'_>>)
    -> Option<crate::name_constraints::spec::NameConstraints>
{
    match value { Some(item) => Some(name_constraints::view_name_constraints(item)), None => None }
}

/// The spec `PreparedSignature` of a decoded certificate.
pub open spec fn view_prepared_signature(
    envelope: &crate::certificate::exec::CertificateEnvelope<'_>,
    tbs: &crate::tbs::exec::TbsCertificate<'_>,
    class: signature::AlgorithmClass,
) -> crate::signature_algorithm::spec::PreparedSignature {
    crate::signature_algorithm::spec::PreparedSignature {
        tbs_algorithm: crate::certificate::contract::view_algorithm_identifier(&tbs.signature),
        outer_algorithm: crate::certificate::contract::view_algorithm_identifier(&envelope.signature_algorithm),
        class: signature::view_class(class),
        tbs_der: envelope.tbs_certificate_der@,
        signature_bits: envelope.signature_bits@,
        signature_unused_bits: envelope.signature_unused_bits,
    }
}

pub open spec fn view_path_cert(value: &PathCert<'_>) -> super::spec::PathCert {
    super::spec::PathCert {
        der: value.der@,
        envelope: crate::certificate::exec::view_certificate_envelope(&value.envelope),
        tbs: crate::tbs::exec::view_tbs_certificate(&value.tbs),
        extensions: extensions::view_extensions(value.extensions@),
        basic: constraints::view_basic_option(value.basic),
        key_usage: constraints::view_key_usage_option(value.key_usage),
        eku: view_eku_option(&value.eku),
        name_constraints: view_name_constraints_option(&value.name_constraints),
        san: view_san_option(&value.san),
        require_explicit_policy: view_magnitude(value.require_explicit_policy),
        has_policy_mappings: value.has_policy_mappings,
        signature: view_prepared_signature(&value.envelope, &value.tbs, value.signature_class),
    }
}

pub open spec fn view_path_cert_result(result: Option<PathCert<'_>>) -> Option<super::spec::PathCert> {
    match result { Some(value) => Some(view_path_cert(&value)), None => None }
}

pub open spec fn view_anchor(value: &Anchor<'_>) -> super::spec::Anchor {
    super::spec::Anchor {
        subject_der: value.subject_der@,
        spki_der: value.spki_der@,
        name_constraints: view_name_constraints_option(&value.name_constraints),
        path_len: view_magnitude(value.path_len),
        not_before: value.not_before@,
        not_after: value.not_after@,
        server_distrust_after: match value.server_distrust_after { Some(time) => Some(time@), None => None },
    }
}

pub open spec fn view_anchor_result(result: Option<Anchor<'_>>) -> Option<super::spec::Anchor> {
    match result { Some(value) => Some(view_anchor(&value)), None => None }
}

fn copy_time(value: &CertificateTime) -> (result: CertificateTime)
    ensures result@ == value@
{
    CertificateTime {
        year: value.year, month: value.month, day: value.day,
        hour: value.hour, minute: value.minute, second: value.second,
    }
}

pub(crate) fn name_constraints_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= crate::name_constraints::spec::name_constraints_oid()
{
    let arcs = vec![2u64, 5, 29, 30];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= crate::name_constraints::spec::name_constraints_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(crate::name_constraints::spec::name_constraints_oid);
        }
    }
    arcs
}

pub(crate) fn policy_constraints_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= crate::policy_constraints::spec::policy_constraints_oid()
{
    let arcs = vec![2u64, 5, 29, 36];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= crate::policy_constraints::spec::policy_constraints_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(crate::policy_constraints::spec::policy_constraints_oid);
        }
    }
    arcs
}

fn policy_mappings_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= super::spec::policy_mappings_oid()
{
    let arcs = vec![2u64, 5, 29, 33];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= super::spec::policy_mappings_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(super::spec::policy_mappings_oid);
        }
    }
    arcs
}

fn inhibit_any_policy_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= super::spec::inhibit_any_policy_oid()
{
    let arcs = vec![2u64, 5, 29, 54];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= super::spec::inhibit_any_policy_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(super::spec::inhibit_any_policy_oid);
        }
    }
    arcs
}

/// Whether an extension with this OID is present.
fn has_extension(input: &[extensions::Extension<'_>], oid: &[u64]) -> (result: bool)
    ensures result == super::spec::has_extension(
        extensions::view_extensions(input@), clazel_der::decode::nats(oid@))
{
    let found = leaf::find_extension_index(input, oid);
    proof { reveal(super::spec::has_extension); }
    found.is_some()
}

/// The Extensions of a TBSCertificate (none when absent).
fn tbs_extensions<'a>(tbs: &crate::tbs::exec::TbsCertificate<'a>)
    -> (result: Option<Vec<extensions::Extension<'a>>>)
    ensures extensions::view_extensions_result(result)
        == super::spec::tbs_extensions(crate::tbs::exec::view_tbs_certificate(tbs))
{
    match tbs.extensions_sequence_der {
        None => {
            let empty: Vec<extensions::Extension<'a>> = Vec::new();
            proof {
                reveal(super::spec::tbs_extensions);
                reveal(crate::tbs::exec::view_tbs_certificate);
                assert(extensions::view_extensions(empty@) =~= Seq::<crate::extensions::spec::Extension>::empty());
            }
            Some(empty)
        },
        Some(encoded) => {
            let parsed = extensions::parse_extensions(encoded);
            proof {
                reveal(super::spec::tbs_extensions);
                reveal(crate::tbs::exec::view_tbs_certificate);
            }
            parsed
        },
    }
}

pub open spec fn view_optional_name_constraints_result(
    result: Option<Option<name_constraints::NameConstraints<'_>>>,
) -> Option<Option<crate::name_constraints::spec::NameConstraints>> {
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => Some(Some(name_constraints::view_name_constraints(&value))),
    }
}

fn parse_optional_name_constraints<'b>(
    input: &[extensions::Extension<'b>], oid: &[u64],
) -> (result: Option<Option<name_constraints::NameConstraints<'b>>>)
    requires clazel_der::decode::nats(oid@) =~= crate::name_constraints::spec::name_constraints_oid()
    ensures view_optional_name_constraints_result(result)
        == super::spec::optional_name_constraints(extensions::view_extensions(input@))
{
    match leaf::find_extension_index(input, oid) {
        None => {
            proof { reveal(super::spec::optional_name_constraints); }
            Some(None)
        },
        Some(index) => {
            let extension = input.get(index)?;
            let value = name_constraints::parse_name_constraints(extension.value)?;
            proof {
                reveal(super::spec::optional_name_constraints);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int].value == extension.value@);
            }
            Some(Some(value))
        },
    }
}

pub open spec fn view_optional_san_result(
    result: Option<Option<extensions::SubjectAltName<'_>>>,
) -> Option<Option<crate::extensions::spec::SubjectAltName>> {
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => Some(Some(extensions::view_subject_alt_name(&value))),
    }
}

fn parse_optional_san<'b>(
    input: &[extensions::Extension<'b>], oid: &[u64],
) -> (result: Option<Option<extensions::SubjectAltName<'b>>>)
    requires clazel_der::decode::nats(oid@) =~= crate::extensions::spec::subject_alt_name_oid()
    ensures view_optional_san_result(result)
        == super::spec::optional_subject_alt_name(extensions::view_extensions(input@))
{
    match leaf::find_extension_index(input, oid) {
        None => {
            proof { reveal(super::spec::optional_subject_alt_name); }
            Some(None)
        },
        Some(index) => {
            let extension = input.get(index)?;
            let value = extensions::parse_subject_alt_name(extension.value)?;
            proof {
                reveal(super::spec::optional_subject_alt_name);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                reveal(extensions::view_subject_alt_name_result);
                assert(extensions::view_extensions(input@)[index as int].value == extension.value@);
            }
            Some(Some(value))
        },
    }
}

pub open spec fn view_optional_policy_result(
    result: Option<Option<crate::policy_constraints::exec::PolicyConstraints<'_>>>,
) -> Option<Option<crate::policy_constraints::spec::PolicyConstraints>> {
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => Some(Some(value@)),
    }
}

fn parse_optional_policy_constraints<'b>(
    input: &[extensions::Extension<'b>], oid: &[u64],
) -> (result: Option<Option<crate::policy_constraints::exec::PolicyConstraints<'b>>>)
    requires clazel_der::decode::nats(oid@) =~= crate::policy_constraints::spec::policy_constraints_oid()
    ensures view_optional_policy_result(result)
        == super::spec::optional_policy_constraints(extensions::view_extensions(input@))
{
    match leaf::find_extension_index(input, oid) {
        None => {
            proof { reveal(super::spec::optional_policy_constraints); }
            Some(None)
        },
        Some(index) => {
            let extension = input.get(index)?;
            let value = crate::policy_constraints::exec::parse_policy_constraints(extension.value)?;
            proof {
                reveal(super::spec::optional_policy_constraints);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int].value == extension.value@);
            }
            Some(Some(value))
        },
    }
}

/// The class of the signature (RFC 5280 §4.1.1.2), if the two identifiers agree.
fn prepare_class(
    envelope: &crate::certificate::exec::CertificateEnvelope<'_>,
    tbs: &crate::tbs::exec::TbsCertificate<'_>,
) -> (result: Option<signature::AlgorithmClass>)
    ensures match result {
        Some(class) => crate::signature_algorithm::spec::prepare_signature(
            crate::certificate::contract::view_algorithm_identifier(&tbs.signature),
            crate::certificate::contract::view_algorithm_identifier(&envelope.signature_algorithm),
            envelope.tbs_certificate_der@, envelope.signature_bits@, envelope.signature_unused_bits)
            == Some(view_prepared_signature(envelope, tbs, class)),
        None => crate::signature_algorithm::spec::prepare_signature(
            crate::certificate::contract::view_algorithm_identifier(&tbs.signature),
            crate::certificate::contract::view_algorithm_identifier(&envelope.signature_algorithm),
            envelope.tbs_certificate_der@, envelope.signature_bits@, envelope.signature_unused_bits) is None,
    }
{
    let prepared = signature::prepare_signature_input(
        &tbs.signature, &envelope.signature_algorithm, envelope.tbs_certificate_der,
        envelope.signature_unused_bits, envelope.signature_bits);
    Some(prepared?.class)
}

/// Design §3.2, `parse_path_cert`.
pub fn parse_path_cert(der: &[u8]) -> (result: Option<PathCert<'_>>)
    ensures super::contract::parse_path_cert_ensures(der@, view_path_cert_result(result))
{
    hide(crate::certificate::spec::parse_certificate);
    hide(crate::tbs::spec::parse_tbs_certificate);
    hide(crate::extensions::spec::parse_extensions);
    hide(crate::extensions::spec::parse_subject_alt_name);
    hide(crate::constraints::spec::parse_basic_constraints);
    hide(crate::constraints::spec::parse_key_usage);
    hide(crate::constraints::spec::parse_extended_key_usage);
    hide(crate::name_constraints::spec::parse_name_constraints);
    hide(crate::policy_constraints::spec::parse_policy_constraints);
    hide(crate::signature_algorithm::spec::prepare_signature);
    hide(clazel_der::spec::read_tlv);
    hide(clazel_der::spec::read_oid);
    hide(clazel_der::spec::expect_sequence);
    hide(clazel_der::spec::read_boolean);
    hide(clazel_der::spec::read_octet_string);
    hide(clazel_der::spec::read_bit_string);
    hide(clazel_der::spec::expect_constructed);
    let envelope = crate::certificate::exec::parse_certificate(der)?;
    let tbs = crate::tbs::exec::parse_tbs_certificate(envelope.tbs_certificate_der)?;
    let parsed = tbs_extensions(&tbs)?;
    let basic_oid = leaf::basic_constraints_oid();
    let usage_oid = leaf::key_usage_oid();
    let eku_oid = leaf::extended_key_usage_oid();
    let nc_oid = name_constraints_oid();
    let san_oid = leaf::san_oid();
    let policy_oid = policy_constraints_oid();
    let mappings_oid = policy_mappings_oid();
    let basic = leaf::parse_optional_basic_constraints(&parsed, &basic_oid)?;
    let key_usage = leaf::parse_optional_key_usage(&parsed, &usage_oid)?;
    let eku = leaf::parse_optional_eku(&parsed, &eku_oid)?;
    let name_constraints = parse_optional_name_constraints(&parsed, &nc_oid)?;
    let san = parse_optional_san(&parsed, &san_oid)?;
    let policy = parse_optional_policy_constraints(&parsed, &policy_oid)?;
    let class = prepare_class(&envelope, &tbs)?;
    let has_policy_mappings = has_extension(&parsed, &mappings_oid);
    let require_explicit_policy = match policy {
        Some(value) => value.require_explicit_policy,
        None => None,
    };
    let result = PathCert {
        der, envelope, tbs, extensions: parsed, basic, key_usage, eku, name_constraints, san,
        require_explicit_policy, has_policy_mappings, signature_class: class,
    };
    proof {
        reveal(super::spec::parse_path_cert);
        reveal(super::spec::require_explicit_policy_of);
    }
    Some(result)
}

/// RFC 5937 §2: every critical extension is one the anchor code reads.
fn anchor_critical_supported(input: &[extensions::Extension<'_>]) -> (result: bool)
    ensures result == super::spec::anchor_critical_supported(extensions::view_extensions(input@), 0)
{
    let basic_oid = leaf::basic_constraints_oid();
    let usage_oid = leaf::key_usage_oid();
    let eku_oid = leaf::extended_key_usage_oid();
    let nc_oid = name_constraints_oid();
    let mut index = 0;
    while index < input.len()
        invariant index <= input.len(), input@.len() == input.len(),
            clazel_der::decode::nats(basic_oid@) =~= crate::leaf::spec::basic_constraints_oid(),
            clazel_der::decode::nats(usage_oid@) =~= crate::leaf::spec::key_usage_oid(),
            clazel_der::decode::nats(eku_oid@) =~= crate::leaf::spec::extended_key_usage_extension_oid(),
            clazel_der::decode::nats(nc_oid@) =~= crate::name_constraints::spec::name_constraints_oid(),
            super::spec::anchor_critical_supported(extensions::view_extensions(input@), 0)
                == super::spec::anchor_critical_supported(extensions::view_extensions(input@), index as int),
        decreases input.len() - index
    {
        let extension = match input.get(index) { Some(value) => value, None => return false };
        let basic_supported = leaf::oid_arcs_equal(&extension.oid, &basic_oid);
        let usage_supported = leaf::oid_arcs_equal(&extension.oid, &usage_oid);
        let eku_supported = leaf::oid_arcs_equal(&extension.oid, &eku_oid);
        let nc_supported = leaf::oid_arcs_equal(&extension.oid, &nc_oid);
        let current_supported = !extension.critical || basic_supported || usage_supported
            || eku_supported || nc_supported;
        proof {
            reveal_with_fuel(super::spec::anchor_critical_supported, 1);
            reveal(extensions::view_extensions);
            reveal(extensions::view_extension);
            assert(extensions::view_extensions(input@)[index as int]
                == extensions::view_extension(&input@[index as int]));
            assert(basic_supported == (clazel_der::decode::nats(extension.oid@) =~= crate::leaf::spec::basic_constraints_oid()));
            assert(usage_supported == (clazel_der::decode::nats(extension.oid@) =~= crate::leaf::spec::key_usage_oid()));
            assert(eku_supported == (clazel_der::decode::nats(extension.oid@) =~= crate::leaf::spec::extended_key_usage_extension_oid()));
            assert(nc_supported == (clazel_der::decode::nats(extension.oid@) =~= crate::name_constraints::spec::name_constraints_oid()));
            assert(super::spec::anchor_critical_supported(extensions::view_extensions(input@), index as int)
                == (current_supported && super::spec::anchor_critical_supported(
                    extensions::view_extensions(input@), (index + 1) as int)));
        }
        if !current_supported { return false; }
        index = index.saturating_add(1);
    }
    proof {
        reveal_with_fuel(super::spec::anchor_critical_supported, 1);
    }
    true
}

/// **(R)** RFC 5937 §3.2 bullets 5 to 7.
fn anchor_policy_inputs_absent(input: &[extensions::Extension<'_>]) -> (result: bool)
    ensures result == super::spec::anchor_policy_inputs_absent(extensions::view_extensions(input@))
{
    let inhibit_oid = inhibit_any_policy_oid();
    let policy_oid = policy_constraints_oid();
    let has_inhibit = has_extension(input, &inhibit_oid);
    let has_policy = has_extension(input, &policy_oid);
    proof { reveal(super::spec::anchor_policy_inputs_absent); }
    !has_inhibit && !has_policy
}

/// RFC 5937 §3.2 bullet 8.
fn anchor_path_len(basic: constraints::BasicConstraints<'_>) -> (result: Option<&[u8]>)
    ensures view_magnitude(result)
        == super::spec::anchor_path_len(constraints::view_basic_constraints(&basic))
{
    proof { reveal(super::spec::anchor_path_len); }
    basic.path_len_constraint
}

/// RFC 5937 §3.2 bullet 1, with the empty Name counted as none.
fn anchor_has_subject(subject: &[u8]) -> (result: bool)
    ensures result == super::spec::anchor_has_subject(subject@)
{
    let empty = subject.len() == 2 && subject.first() == Some(&0x30u8) && subject.get(1) == Some(&0x00u8);
    proof {
        reveal(super::spec::anchor_has_subject);
        if empty {
            assert(subject@ =~= seq![0x30u8, 0x00u8]);
        }
        if subject@ == seq![0x30u8, 0x00u8] {
            assert(subject@.len() == 2);
            assert(subject@[0] == 0x30u8);
            assert(subject@[1] == 0x00u8);
        }
    }
    !empty
}

fn anchor_role_allowed(
    basic: constraints::BasicConstraints<'_>, key_usage: Option<constraints::KeyUsage<'_>>,
) -> (result: bool)
    ensures result == super::spec::anchor_role_allowed(
        constraints::view_basic_constraints(&basic), constraints::view_key_usage_option(key_usage))
{
    proof {
        reveal(super::spec::anchor_role_allowed);
        reveal(constraints::view_key_usage_bit);
    }
    basic.ca && match key_usage {
        Some(usage) => constraints::key_usage_has(usage, constraints::KeyUsageBit::KeyCertSign),
        None => true,
    }
}

fn anchor_eku_allowed(eku: Option<constraints::ExtendedKeyUsage>) -> (result: bool)
    ensures result == super::spec::anchor_eku_allowed(view_eku_option(&eku))
{
    proof { reveal(super::spec::anchor_eku_allowed); }
    match eku {
        Some(value) => constraints::eku_allows_server_auth(value, false),
        None => true,
    }
}

pub open spec fn view_text(text: Option<&[u8]>) -> Option<Seq<u8>> {
    match text { Some(bytes) => Some(bytes@), None => None }
}

pub open spec fn view_distrust_result(result: Option<Option<CertificateTime>>)
    -> Option<Option<crate::time::spec::CertificateTime>>
{
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(time)) => Some(Some(time@)),
    }
}

fn decode_distrust_after(text: Option<&[u8]>) -> (result: Option<Option<CertificateTime>>)
    ensures view_distrust_result(result) == super::spec::decode_distrust_after(view_text(text))
{
    proof { reveal(super::spec::decode_distrust_after); }
    match text {
        None => Some(None),
        Some(bytes) => {
            let time = crate::time::exec::decode_time(bytes, crate::time::exec::TimeKind::Utc)?;
            Some(Some(time))
        },
    }
}

/// Design §1.4, `anchor_from_root`: RFC 5937 §2 and §3.2.
pub fn anchor_from_root<'a>(der: &'a [u8], server_distrust_after: Option<&[u8]>)
    -> (result: Option<Anchor<'a>>)
    ensures super::contract::anchor_from_root_ensures(
        der@, view_text(server_distrust_after), view_anchor_result(result))
{
    hide(crate::certificate::spec::parse_certificate);
    hide(crate::tbs::spec::parse_tbs_certificate);
    hide(crate::extensions::spec::parse_extensions);
    hide(crate::constraints::spec::parse_basic_constraints);
    hide(crate::constraints::spec::parse_key_usage);
    hide(crate::constraints::spec::parse_extended_key_usage);
    hide(crate::name_constraints::spec::parse_name_constraints);
    hide(crate::time::spec::decode_time);
    hide(clazel_der::spec::read_tlv);
    hide(clazel_der::spec::read_oid);
    hide(clazel_der::spec::expect_sequence);
    hide(clazel_der::spec::read_boolean);
    hide(clazel_der::spec::read_octet_string);
    hide(clazel_der::spec::read_bit_string);
    hide(clazel_der::spec::expect_constructed);
    let envelope = crate::certificate::exec::parse_certificate(der)?;
    let tbs = crate::tbs::exec::parse_tbs_certificate(envelope.tbs_certificate_der)?;
    let parsed = tbs_extensions(&tbs)?;
    let critical_ok = anchor_critical_supported(&parsed);
    let policy_ok = anchor_policy_inputs_absent(&parsed);
    let subject_ok = anchor_has_subject(tbs.subject_der);
    if !critical_ok || !policy_ok || !subject_ok {
        proof {
            reveal(super::spec::anchor_from_root);
            reveal(crate::tbs::exec::view_tbs_certificate);
        }
        return None;
    }
    let basic_oid = leaf::basic_constraints_oid();
    let usage_oid = leaf::key_usage_oid();
    let eku_oid = leaf::extended_key_usage_oid();
    let nc_oid = name_constraints_oid();
    let basic_option = leaf::parse_optional_basic_constraints(&parsed, &basic_oid)?;
    let key_usage = leaf::parse_optional_key_usage(&parsed, &usage_oid)?;
    let eku = leaf::parse_optional_eku(&parsed, &eku_oid)?;
    let name_constraints = parse_optional_name_constraints(&parsed, &nc_oid)?;
    let distrust = decode_distrust_after(server_distrust_after)?;
    let basic = match basic_option {
        Some(value) => value,
        None => {
            proof { reveal(super::spec::anchor_from_root); }
            return None;
        },
    };
    let role_ok = anchor_role_allowed(basic, key_usage);
    let eku_ok = anchor_eku_allowed(eku);
    if !role_ok || !eku_ok {
        proof { reveal(super::spec::anchor_from_root); }
        return None;
    }
    let result = Anchor {
        subject_der: tbs.subject_der,
        spki_der: tbs.subject_public_key_info_der,
        name_constraints,
        path_len: anchor_path_len(basic),
        not_before: copy_time(&tbs.not_before),
        not_after: copy_time(&tbs.not_after),
        server_distrust_after: distrust,
    };
    proof {
        reveal(super::spec::anchor_from_root);
        reveal(crate::tbs::exec::view_tbs_certificate);
        reveal(constraints::view_basic_constraints);
    }
    Some(result)
}

} // verus!
