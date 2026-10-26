//! Partial X.509 server leaf checks composed from the RFC-specific decoders.
//! RFC 5280 §§4.1, 4.1.2.5, 4.1.2.9, 4.2.1.3, 4.2.1.6, 4.2.1.9, 4.2.1.12;
//! RFC 8446 §4.4.2.2; RFC 9525 §§4.1, 6.2–6.4.
//! <https://www.rfc-editor.org/rfc/rfc5280.html>
//! <https://www.rfc-editor.org/rfc/rfc8446.html#section-4.4.2.2>
//! <https://www.rfc-editor.org/rfc/rfc9525.html>
//!
//! Modelling choices and limits:
//! - This returns only `NeedsPathValidation`; it does not verify either
//!   signatureAlgorithm, signature bytes, chain, trust, revocation, or name
//!   constraints, and is not integrated into a production verifier.
//! - Reference DNS bytes are already canonical ASCII from the URL layer;
//!   reference IP addresses are binary IPv4/IPv6 octets. Existing RFC 9525
//!   matching is used unchanged. Subject Common Name and other RDNs are never
//!   identity fallbacks (RFC 9525 §7.1).
//! - A subjectAltName with at least one matching DNS-ID/IP-ID is required.
//!   Because this slice interprets only dNSName and iPAddress, any other
//!   GeneralName choice causes rejection, including when SAN is noncritical.
//! - Unknown critical extensions are rejected. Recognized critical SAN,
//!   BasicConstraints, KeyUsage, and ExtendedKeyUsage values are parsed and
//!   processed here; unknown noncritical extensions remain outside this
//!   slice's semantics.
//! - RFC 5280 §4.2.1.3/.12 impose no additional purpose restriction when
//!   KeyUsage or EKU is absent. If KeyUsage is present, RFC 8446 §4.4.2.2
//!   requires digitalSignature for TLS 1.3 server authentication. If EKU is
//!   present, serverAuth is required; accepting anyExtendedKeyUsage is an
//!   explicit caller policy and defaults to false in `LeafPolicy`.
//! - BasicConstraints is optional for an end entity. When present, cA must be
//!   false; keyCertSign and pathLen coupling is checked by the existing
//!   RFC 5280 constraint helper. This is a leaf-role profile, not path
//!   validation.
//! - Captured `now` is checked against the inclusive validity interval. Time
//!   interpretation and ordering come from the existing RFC 5280 time model.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// State of a successful partial result. Full validation is explicitly pending.
pub enum PartialValidationState {
    /// Signature, path, trust, revocation, and policy validation remain required.
    NeedsPathValidation,
}

/// Explicit local policy for accepting the RFC 5280 anyExtendedKeyUsage OID.
pub struct LeafPolicy {
    /// Accept a present EKU containing anyExtendedKeyUsage without serverAuth.
    pub allow_any_extended_key_usage: bool,
}

/// Evidence that a subset of server-leaf checks succeeded.
pub struct PartialLeafChecks {
    /// The captured DNS-ID or binary IP-ID reference used for matching.
    pub reference: crate::spec::ReferenceIdentity,
    /// Captured comparison time.
    pub now: crate::time::spec::CertificateTime,
    /// Parsed inclusive validity start.
    pub not_before: crate::time::spec::CertificateTime,
    /// Parsed inclusive validity end.
    pub not_after: crate::time::spec::CertificateTime,
    /// True only when one supported SAN identifier matched the reference.
    pub identity_matched: bool,
    /// True only when the captured time is within the inclusive validity range.
    pub valid_at_captured_time: bool,
    /// True only when EKU is absent or permits TLS WWW server authentication.
    pub server_auth_purpose_allowed: bool,
    /// True only when KeyUsage is absent or includes digitalSignature.
    pub digital_signature_allowed: bool,
    /// True only when the certificate has the permitted end-entity role.
    pub leaf_role_allowed: bool,
    /// Whether KeyUsage was present; absence itself imposes no KU restriction.
    pub key_usage_present: bool,
    /// Whether ExtendedKeyUsage was present; absence itself imposes no EKU restriction.
    pub extended_key_usage_present: bool,
    /// Whether BasicConstraints was present.
    pub basic_constraints_present: bool,
    /// A successful value always carries this incomplete-validation state.
    pub state: PartialValidationState,
}

/// id-ce-keyUsage ::= { id-ce 15 }.
pub open spec fn key_usage_oid() -> Seq<nat> { seq![2nat, 5, 29, 15] }

/// id-ce-basicConstraints ::= { id-ce 19 }.
pub open spec fn basic_constraints_oid() -> Seq<nat> { seq![2nat, 5, 29, 19] }

/// id-ce-extKeyUsage ::= { id-ce 37 }.
pub open spec fn extended_key_usage_extension_oid() -> Seq<nat> { seq![2nat, 5, 29, 37] }

/// Locate a unique extension by OID in the already duplicate-free extension list.
pub open spec fn find_extension(
    extensions: Seq<crate::extensions::spec::Extension>, oid: Seq<nat>, index: int,
) -> Option<crate::extensions::spec::Extension>
    recommends 0 <= index <= extensions.len()
    decreases extensions.len() as int - index
{
    if index >= extensions.len() { None }
    else if extensions[index].oid =~= oid { Some(extensions[index]) }
    else { find_extension(extensions, oid, index + 1) }
}

/// Locate the first matching extension index, preserving encoded order.
pub open spec fn find_extension_index(
    extensions: Seq<crate::extensions::spec::Extension>, oid: Seq<nat>, index: int,
) -> Option<int>
    recommends 0 <= index <= extensions.len()
    decreases extensions.len() as int - index
{
    if index >= extensions.len() { None }
    else if extensions[index].oid =~= oid { Some(index) }
    else { find_extension_index(extensions, oid, index + 1) }
}

/// RFC 5280 §4.2: every critical extension must be among the four semantics
/// this partial checker actually processes.
pub open spec fn supported_critical_extensions(
    extensions: Seq<crate::extensions::spec::Extension>, index: int,
) -> bool
    recommends 0 <= index <= extensions.len()
    decreases extensions.len() as int - index
{
    if index >= extensions.len() { true }
    else {
        let extension = extensions[index];
        (!extension.critical
            || extension.oid =~= crate::extensions::spec::subject_alt_name_oid()
            || extension.oid =~= basic_constraints_oid()
            || extension.oid =~= key_usage_oid()
            || extension.oid =~= extended_key_usage_extension_oid())
            && supported_critical_extensions(extensions, index + 1)
    }
}

/// Reject GeneralName alternatives whose semantics this DNS/IP checker cannot process.
pub open spec fn only_supported_general_names(
    names: Seq<crate::extensions::spec::GeneralName>, index: int,
) -> bool
    recommends 0 <= index <= names.len()
    decreases names.len() as int - index
{
    if index >= names.len() { true }
    else {
        let supported = match names[index] {
            crate::extensions::spec::GeneralName::DnsName(_) => true,
            crate::extensions::spec::GeneralName::IpAddress(_) => true,
            crate::extensions::spec::GeneralName::Other(_, _) => false,
        };
        supported && only_supported_general_names(names, index + 1)
    }
}

/// RFC 9525 §6.2: match at least one same-type DNS-ID/IP-ID SAN entry.
pub open spec fn general_name_matches_reference(
    name: crate::extensions::spec::GeneralName,
    reference: crate::spec::ReferenceIdentity,
) -> bool {
    match name {
        crate::extensions::spec::GeneralName::DnsName(value) =>
            crate::spec::service_identity_match(reference, crate::spec::PresentedIdentity::Dns(value)),
        crate::extensions::spec::GeneralName::IpAddress(value) =>
            crate::spec::service_identity_match(reference, crate::spec::PresentedIdentity::Ip(value)),
        crate::extensions::spec::GeneralName::Other(_, _) => false,
    }
}

/// RFC 9525 §6.2: match at least one same-type DNS-ID/IP-ID SAN entry.
pub open spec fn san_matches_reference(
    names: Seq<crate::extensions::spec::GeneralName>,
    reference: crate::spec::ReferenceIdentity, index: int,
) -> bool
    recommends 0 <= index <= names.len()
    decreases names.len() as int - index
{
    if index >= names.len() { false }
    else {
        let matches = general_name_matches_reference(names[index], reference);
        matches || san_matches_reference(names, reference, index + 1)
    }
}

/// Decode an optional extension value; `None` means absent, outer `None`
/// means malformed.
pub open spec fn optional_basic_constraints(
    extensions: Seq<crate::extensions::spec::Extension>,
) -> Option<Option<crate::constraints::spec::BasicConstraints>> {
    match find_extension_index(extensions, basic_constraints_oid(), 0) {
        None => Some(None),
        Some(index) => match crate::constraints::spec::parse_basic_constraints(extensions[index].value) {
            Some(value) => Some(Some(value)), None => None,
        },
    }
}

/// Decode an optional KeyUsage value; `None` means absent, outer `None` malformed.
pub open spec fn optional_key_usage(
    extensions: Seq<crate::extensions::spec::Extension>,
) -> Option<Option<crate::constraints::spec::KeyUsage>> {
    match find_extension_index(extensions, key_usage_oid(), 0) {
        None => Some(None),
        Some(index) => match crate::constraints::spec::parse_key_usage(extensions[index].value) {
            Some(value) => Some(Some(value)), None => None,
        },
    }
}

/// Decode an optional EKU value; absence adds no restriction under RFC 5280 §4.2.1.12.
pub open spec fn optional_extended_key_usage(
    extensions: Seq<crate::extensions::spec::Extension>,
) -> Option<Option<crate::constraints::spec::ExtendedKeyUsage>> {
    match find_extension_index(extensions, extended_key_usage_extension_oid(), 0) {
        None => Some(None),
        Some(index) => match crate::constraints::spec::parse_extended_key_usage(extensions[index].value) {
            Some(value) => Some(Some(value)), None => None,
        },
    }
}

/// Check parsed fields after the outer certificate and TBS decoders succeed.
/// Steps 1–8 process supported critical extensions, SAN, usages, role, and time.
pub open spec fn check_extensions(
    extensions: Seq<crate::extensions::spec::Extension>,
    tbs: crate::tbs::spec::TbsCertificate,
    reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
    policy: LeafPolicy,
) -> Option<PartialLeafChecks> {
    if !supported_critical_extensions(extensions, 0) { None }
    else { match find_extension_index(extensions, crate::extensions::spec::subject_alt_name_oid(), 0) {
        None => None,
        Some(san_index) => match crate::extensions::spec::parse_subject_alt_name(extensions[san_index].value) {
            None => None,
            Some(san) => {
                // 1. Require only GeneralName semantics implemented here and a DNS/IP match.
                if !only_supported_general_names(san.names, 0)
                    || !san_matches_reference(san.names, reference, 0) { None }
                else { match (optional_basic_constraints(extensions), optional_key_usage(extensions)) {
                    (Some(basic), Some(usage)) => {
                        // 2. If KeyUsage is present, TLS 1.3 server auth needs digitalSignature.
                        let digital_signature_allowed = match usage {
                            Some(value) => crate::constraints::spec::key_usage_has(
                                value, crate::constraints::spec::KeyUsageBit::DigitalSignature),
                            None => true,
                        };
                        if !digital_signature_allowed { None }
                        else {
                            // 3. Process keyCertSign/pathLen coupling and reject CA-role leaves.
                            let role_compatible = crate::constraints::spec::basic_constraints_compatible(basic, usage);
                            let leaf_role_allowed = role_compatible && match basic {
                                Some(value) => !value.ca, None => true,
                            };
                            if !leaf_role_allowed { None }
                            else { match optional_extended_key_usage(extensions) {
                                None => None,
                                Some(eku) => {
                                    // 4. An absent EKU is unrestricted; a present EKU must permit serverAuth.
                                    let server_auth_allowed = match eku {
                                        Some(value) => crate::constraints::spec::eku_allows_server_auth(
                                            value, policy.allow_any_extended_key_usage),
                                        None => true,
                                    };
                                    if !server_auth_allowed { None }
                                    else {
                                        // 5. Compare captured time with the inclusive certificate validity.
                                        let valid_at = crate::time::spec::validity_contains(
                                            crate::time::spec::Validity { not_before: tbs.not_before, not_after: tbs.not_after }, now);
                                        if !valid_at { None }
                                        else { Some(PartialLeafChecks {
                                            reference, now, not_before: tbs.not_before, not_after: tbs.not_after,
                                            identity_matched: true, valid_at_captured_time: true,
                                            server_auth_purpose_allowed: true, digital_signature_allowed: true,
                                            leaf_role_allowed: true, key_usage_present: usage.is_some(),
                                            extended_key_usage_present: eku.is_some(),
                                            basic_constraints_present: basic.is_some(),
                                            state: PartialValidationState::NeedsPathValidation,
                                        }) }
                                    }
                                },
                            }}
                        }
                    },
                    _ => None,
                }}
            },
        },
    }}
}

/// RFC 5280 envelope and TBS composition around `check_extensions`.
pub open spec fn check_leaf_certificate(
    input: Seq<u8>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime, policy: LeafPolicy,
) -> Option<PartialLeafChecks> {
    match crate::certificate::spec::parse_certificate(input) {
        None => None,
        Some(envelope) => match crate::tbs::spec::parse_tbs_certificate(envelope.tbs_certificate_der) {
            None => None,
            Some(tbs) => match tbs.extensions_sequence_der {
                None => None,
                Some(encoded_extensions) => match crate::extensions::spec::parse_extensions(encoded_extensions) {
                    None => None,
                    Some(extensions) => check_extensions(extensions, tbs, reference, now, policy),
                },
            },
        },
    }
}

} // verus!
