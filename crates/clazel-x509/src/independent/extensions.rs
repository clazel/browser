//! The standard extensions, transcribed for the independent decoder from
//! Rec. ITU-T X.509 (10/2019) | ISO/IEC 9594-8:2020, clauses 7.3, 9.2.2, 9.3.2
//! and 9.4.2 and the module `CertificateExtensions` of Annex A (PDF SHA-256
//! `1f4ea2939ecc31a3433c499084d485e770f9b8dcee55a0ba9fe4c27128822e8c`).
//! `UnboundedDirectoryString` is from Rec. ITU-T X.520 (10/2019), `INSTANCE
//! OF` from Rec. ITU-T X.681 (02/2021) Annex C (PDF SHA-256
//! `fec21841db1bb8bfc109c21590a531bfefabeb029df5218e6cd6264b0148e32e`).
//!
//! Not read while writing this file: see the list in `independent/mod.rs`.
//!
//! Modelling choices:
//! - `CertificateExtensions` is `IMPLICIT TAGS`, so a tagged component
//!   replaces its base type's tag (X.690 8.14.4), unless the base is an
//!   untagged CHOICE or open type, which keeps its own tag inside the context
//!   tag (X.680 31.2.7 c)). So `directoryName [4] Name`, and the two
//!   `UnboundedDirectoryString` components of `EDIPartyName`, wrap one
//!   encoding, and `dNSName [2] IA5String` does not.
//! - `otherName [0] INSTANCE OF OTHER-NAME` is the SEQUENCE of X.681 Annex C,
//!   `{ type-id, value [0] Type }`, the outer tag implicit. `value` wraps an
//!   open type, so that inner `[0]` is explicit by 31.2.7 c).
//! - `x400Address [3] ORAddress` is kept as its encoding. `ORAddress` is a
//!   large external type of Annex D and is not interpreted here.
//! - A `GeneralName` alternative that this edition does not define is kept
//!   as `Unknown`: the CHOICE has an extension marker. Only a defined tag in
//!   the wrong form is a refusal.
//! - Each extension's `extnValue` is `ENCODED BY der`, so it must be exactly
//!   one DER encoding of the type its `extnId` selects. A value that fails is
//!   not a value of `Extension`, whatever its `critical` flag says, so the
//!   whole certificate is refused here. An `extnId` this file does not
//!   decode is kept as `Unrecognized`, its value unread.
//! - Additions (see `structures.rs`) are kept per SEQUENCE. 7.3's rule for
//!   them, which depends on `critical`, is in `requirements.rs`.
//!
//! The extensions decoded are those named for this module: authority and
//! subject key identifiers, key usage, extended key usage, certificate
//! policies, subject alternative name, basic constraints, name constraints,
//! policy constraints and inhibit any policy.
//!
//! Open choices, all listed in the pull request:
//! - 9.3.2.1's "four octets" and "16 octets" for `iPAddress` are in the prose,
//!   so they are in `requirements.rs`, and only for a subject alternative
//!   name. X.509 says nothing of a `GeneralSubtree` base's address form, and
//!   this decoder does not constrain it.
//! - A PolicyQualifierInfo's `qualifier` is an open type: kept, unread.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der::*;
use super::der::{BitString, Tlv};
#[cfg(verus_only)]
use super::structures::*;
use super::structures::{Name, ObjectIdentifier};

verus! {

/// Annex A: `id-ce` is `certificateExtension`, which X.501 Annex A makes
/// `{ds 29}`, and `ds` is `{joint-iso-itu-t ds(5)}`.
pub open spec fn id_ce(n: nat) -> ObjectIdentifier {
    seq![2nat, 5nat, 29nat, n]
}

/// Annex A: `id-ce-subjectKeyIdentifier`.
pub open spec fn id_ce_subject_key_identifier() -> ObjectIdentifier {
    id_ce(14)
}

/// Annex A: `id-ce-keyUsage`.
pub open spec fn id_ce_key_usage() -> ObjectIdentifier {
    id_ce(15)
}

/// Annex A: `id-ce-subjectAltName`.
pub open spec fn id_ce_subject_alt_name() -> ObjectIdentifier {
    id_ce(17)
}

/// Annex A: `id-ce-basicConstraints`.
pub open spec fn id_ce_basic_constraints() -> ObjectIdentifier {
    id_ce(19)
}

/// Annex A: `id-ce-nameConstraints`.
pub open spec fn id_ce_name_constraints() -> ObjectIdentifier {
    id_ce(30)
}

/// Annex A: `id-ce-certificatePolicies`.
pub open spec fn id_ce_certificate_policies() -> ObjectIdentifier {
    id_ce(32)
}

/// Annex A: `id-ce-authorityKeyIdentifier`.
pub open spec fn id_ce_authority_key_identifier() -> ObjectIdentifier {
    id_ce(35)
}

/// Annex A: `id-ce-policyConstraints`.
pub open spec fn id_ce_policy_constraints() -> ObjectIdentifier {
    id_ce(36)
}

/// Annex A: `id-ce-extKeyUsage`.
pub open spec fn id_ce_ext_key_usage() -> ObjectIdentifier {
    id_ce(37)
}

/// Annex A: `id-ce-inhibitAnyPolicy`.
pub open spec fn id_ce_inhibit_any_policy() -> ObjectIdentifier {
    id_ce(54)
}

/// X.520 `UnboundedDirectoryString`: which alternative, and its octets.
pub enum UnboundedDirectoryString {
    /// The `teletexString` alternative.
    TeletexString(Seq<u8>),
    /// The `printableString` alternative.
    PrintableString(Seq<u8>),
    /// The `bmpString` alternative.
    BmpString(Seq<u8>),
    /// The `universalString` alternative.
    UniversalString(Seq<u8>),
    /// The `uTF8String` alternative.
    Utf8String(Seq<u8>),
}

/// 9.3.2.1 `EDIPartyName`.
pub struct EDIPartyName {
    /// `nameAssigner`.
    pub name_assigner: Option<UnboundedDirectoryString>,
    /// `partyName`.
    pub party_name: UnboundedDirectoryString,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.3.2.1 `GeneralName`.
pub enum GeneralName {
    /// The `otherName` alternative.
    OtherName {
        /// `type-id`.
        type_id: ObjectIdentifier,
        /// The value inside `[0]`.
        value: Tlv,
    },
    /// The `rfc822Name` alternative.
    Rfc822Name(Seq<u8>),
    /// The `dNSName` alternative.
    DNSName(Seq<u8>),
    /// The `x400Address` alternative.
    X400Address(Tlv),
    /// The `directoryName` alternative.
    DirectoryName(Name),
    /// The `ediPartyName` alternative.
    EdiPartyName(EDIPartyName),
    /// The `uniformResourceIdentifier` alternative.
    UniformResourceIdentifier(Seq<u8>),
    /// The `iPAddress` alternative.
    IPAddress(Seq<u8>),
    /// The `registeredID` alternative.
    RegisteredID(ObjectIdentifier),
    /// An alternative added by a later edition.
    Unknown(Tlv),
}

/// 9.2.2.1 `AuthorityKeyIdentifier`.
pub struct AuthorityKeyIdentifier {
    /// `keyIdentifier`.
    pub key_identifier: Option<Seq<u8>>,
    /// `authorityCertIssuer`.
    pub authority_cert_issuer: Option<Seq<GeneralName>>,
    /// `authorityCertSerialNumber`.
    pub authority_cert_serial_number: Option<int>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.2.2.6 `PolicyQualifierInfo`.
pub struct PolicyQualifierInfo {
    /// `policyQualifierId`.
    pub policy_qualifier_id: ObjectIdentifier,
    /// `qualifier`.
    pub qualifier: Option<Tlv>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.2.2.6 `PolicyInformation`.
pub struct PolicyInformation {
    /// `policyIdentifier`.
    pub policy_identifier: ObjectIdentifier,
    /// `policyQualifiers`.
    pub policy_qualifiers: Option<Seq<PolicyQualifierInfo>>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.4.2.1 `BasicConstraintsSyntax`.
pub struct BasicConstraintsSyntax {
    /// `cA`, FALSE by default.
    pub c_a: bool,
    /// `pathLenConstraint`.
    pub path_len_constraint: Option<nat>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.4.2.2 `GeneralSubtree`.
pub struct GeneralSubtree {
    /// `base`.
    pub base: GeneralName,
    /// `minimum`.
    pub minimum: nat,
    /// `maximum`.
    pub maximum: Option<nat>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.4.2.2 `NameConstraintsSyntax`.
pub struct NameConstraintsSyntax {
    /// `permittedSubtrees`.
    pub permitted_subtrees: Option<Seq<GeneralSubtree>>,
    /// `excludedSubtrees`.
    pub excluded_subtrees: Option<Seq<GeneralSubtree>>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// 9.4.2.3 `PolicyConstraintsSyntax`.
pub struct PolicyConstraintsSyntax {
    /// `requireExplicitPolicy`.
    pub require_explicit_policy: Option<nat>,
    /// `inhibitPolicyMapping`.
    pub inhibit_policy_mapping: Option<nat>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// The decoded `extnValue`.
pub enum ExtensionValue {
    /// The `authorityKeyIdentifier` alternative.
    AuthorityKeyIdentifier(AuthorityKeyIdentifier),
    /// The `subjectKeyIdentifier` alternative.
    SubjectKeyIdentifier(Seq<u8>),
    /// The `keyUsage` alternative.
    KeyUsage(BitString),
    /// The `extKeyUsage` alternative.
    ExtKeyUsage(Seq<ObjectIdentifier>),
    /// The `certificatePolicies` alternative.
    CertificatePolicies(Seq<PolicyInformation>),
    /// The `subjectAltName` alternative.
    SubjectAltName(Seq<GeneralName>),
    /// The `basicConstraints` alternative.
    BasicConstraints(BasicConstraintsSyntax),
    /// The `nameConstraints` alternative.
    NameConstraints(NameConstraintsSyntax),
    /// The `policyConstraints` alternative.
    PolicyConstraints(PolicyConstraintsSyntax),
    /// The `inhibitAnyPolicy` alternative.
    InhibitAnyPolicy(nat),
    /// An `extnId` this transcription does not decode.
    Unrecognized,
}

/// 7.2.1 `Extension`.
pub struct Extension {
    /// `extnId`.
    pub extn_id: ObjectIdentifier,
    /// `critical`.
    pub critical: bool,
    /// The octets of `extnValue`.
    pub extn_value: Seq<u8>,
    /// The value.
    pub value: ExtensionValue,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

// ---------------------------------------------------------------------------
// 9.3.2.1 GeneralName
// ---------------------------------------------------------------------------

/// X.520 `UnboundedDirectoryString`: the tag chooses the alternative (X.690
/// 8.13), each `SIZE (1..MAX)` in characters. TeletexString is universal 20,
/// PrintableString 19, UniversalString 28, UTF8String 12 and BMPString 30
/// (X.680 Table 8), all primitive (X.690 10.2).
pub open spec fn decode_unbounded_directory_string(t: Tlv) -> Option<UnboundedDirectoryString> {
    let s = t.contents;
    if t.class != class_universal() || t.constructed || s.len() == 0 {
        None
    } else if t.number == 20 {
        Some(UnboundedDirectoryString::TeletexString(s))
    } else if t.number == 19 && all_printable(s, 0) {
        Some(UnboundedDirectoryString::PrintableString(s))
    } else if t.number == 30 && s.len() % 2 == 0 {
        // X.680 41.15: BMPString is two octets a character.
        Some(UnboundedDirectoryString::BmpString(s))
    } else if t.number == 28 && s.len() % 4 == 0 {
        // X.680 41.6: UniversalString is four octets a character.
        Some(UnboundedDirectoryString::UniversalString(s))
    } else if t.number == 12 && well_formed_utf8(s, 0) {
        Some(UnboundedDirectoryString::Utf8String(s))
    } else {
        None
    }
}

/// A component tagged around a CHOICE (X.680 31.2.7 c)): constructed, its
/// contents one encoding.
pub open spec fn explicit_inner(t: Tlv) -> Option<Tlv> {
    if !t.constructed {
        None
    } else {
        parse_single(t.contents)
    }
}

/// `[n] UnboundedDirectoryString`.
pub open spec fn decode_wrapped_directory_string(t: Tlv) -> Option<UnboundedDirectoryString> {
    match explicit_inner(t) {
        None => None,
        Some(inner) => decode_unbounded_directory_string(inner),
    }
}

/// `ediPartyName [5] EDIPartyName`: implicit, so constructed with the
/// SEQUENCE's contents.
pub open spec fn decode_edi_party_name(t: Tlv) -> Option<EDIPartyName> {
    if !t.constructed {
        None
    } else {
        match parse_tlvs(t.contents) {
            None => None,
            Some(e) => {
                let i: nat = if tag_at(e, 0, class_context(), 0) {
                    1
                } else {
                    0
                };
                // partyName is required, and tagged [1].
                if !tag_at(e, i, class_context(), 1) {
                    None
                } else {
                    let assigner = if i == 1 {
                        match decode_wrapped_directory_string(e[0]) {
                            None => None,
                            Some(d) => Some(Some(d)),
                        }
                    } else {
                        Some(None)
                    };
                    match (assigner, decode_wrapped_directory_string(e[i as int])) {
                        (Some(name_assigner), Some(party_name)) => Some(
                            EDIPartyName {
                                name_assigner,
                                party_name,
                                additions: from_index(e, i + 1),
                            },
                        ),
                        _ => None,
                    }
                }
            },
        }
    }
}

/// `otherName [0] INSTANCE OF OTHER-NAME`.
pub open spec fn decode_other_name(t: Tlv) -> Option<GeneralName> {
    if !t.constructed {
        None
    } else {
        match parse_tlvs(t.contents) {
            None => None,
            Some(e) => {
                // X.681 Annex C: exactly `type-id` and `value`, with no
                // extension marker.
                if e.len() != 2 || !tag_at(e, 1, class_context(), 0) {
                    None
                } else {
                    match (decode_object_identifier(e[0]), explicit_inner(e[1])) {
                        (Some(type_id), Some(value)) => Some(
                            GeneralName::OtherName { type_id, value },
                        ),
                        _ => None,
                    }
                }
            },
        }
    }
}

/// 9.3.2.1 `GeneralName`: the context tag chooses the alternative.
pub open spec fn decode_general_name(t: Tlv) -> Option<GeneralName> {
    if t.class != class_context() || t.number > 8 {
        // A later edition's alternative.
        Some(GeneralName::Unknown(t))
    } else if t.number == 0 {
        decode_other_name(t)
    } else if t.number == 1 {
        match decode_tagged_ia5_string(t) {
            None => None,
            Some(s) => Some(GeneralName::Rfc822Name(s)),
        }
    } else if t.number == 2 {
        match decode_tagged_ia5_string(t) {
            None => None,
            Some(s) => Some(GeneralName::DNSName(s)),
        }
    } else if t.number == 3 {
        // `ORAddress` is a SEQUENCE (Annex D), so the implicit tag is
        // constructed.
        if t.constructed {
            Some(GeneralName::X400Address(t))
        } else {
            None
        }
    } else if t.number == 4 {
        match explicit_inner(t) {
            None => None,
            Some(inner) => match decode_name(inner) {
                None => None,
                Some(n) => Some(GeneralName::DirectoryName(n)),
            },
        }
    } else if t.number == 5 {
        match decode_edi_party_name(t) {
            None => None,
            Some(n) => Some(GeneralName::EdiPartyName(n)),
        }
    } else if t.number == 6 {
        match decode_tagged_ia5_string(t) {
            None => None,
            Some(s) => Some(GeneralName::UniformResourceIdentifier(s)),
        }
    } else if t.number == 7 {
        // `[7] OCTET STRING`, primitive by X.690 10.2.
        if t.constructed {
            None
        } else {
            Some(GeneralName::IPAddress(t.contents))
        }
    } else {
        match decode_tagged_object_identifier(t) {
            None => None,
            Some(o) => Some(GeneralName::RegisteredID(o)),
        }
    }
}

/// The names from `i`.
pub open spec fn decode_general_name_list(e: Seq<Tlv>, i: nat) -> Option<Seq<GeneralName>>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<GeneralName>::empty())
    } else {
        match decode_general_name(e[i as int]) {
            None => None,
            Some(first) => match decode_general_name_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// `GeneralNames ::= SEQUENCE SIZE (1..MAX) OF GeneralName`, from its
/// elements.
pub open spec fn general_names_from(e: Seq<Tlv>) -> Option<Seq<GeneralName>> {
    if e.len() == 0 {
        None
    } else {
        decode_general_name_list(e, 0)
    }
}

// ---------------------------------------------------------------------------
// 9.2.2 Key and policy information
// ---------------------------------------------------------------------------

/// `authorityCertIssuer [1] GeneralNames`: implicit, so constructed with the
/// SEQUENCE's contents.
pub open spec fn tagged_authority_issuer(t: Tlv) -> Option<Seq<GeneralName>> {
    if !t.constructed {
        None
    } else {
        match parse_tlvs(t.contents) {
            None => None,
            Some(e) => general_names_from(e),
        }
    }
}

/// `[2] CertificateSerialNumber` in an IMPLICIT TAGS module.
pub open spec fn tagged_integer(t: Tlv) -> Option<int> {
    if t.constructed {
        None
    } else {
        integer_contents(t.contents)
    }
}

/// 9.2.2.1 `AuthorityKeyIdentifier`.
pub open spec fn decode_authority_key_identifier(t: Tlv) -> Option<AuthorityKeyIdentifier> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            let i: nat = if tag_at(e, 0, class_context(), 0) {
                1
            } else {
                0
            };
            let j: nat = if tag_at(e, i, class_context(), 1) {
                i + 1
            } else {
                i
            };
            let k: nat = if tag_at(e, j, class_context(), 2) {
                j + 1
            } else {
                j
            };
            let identifier = if i == 1 {
                // `[0] KeyIdentifier`: an implicit OCTET STRING, primitive by
                // X.690 10.2.
                if e[0].constructed {
                    None
                } else {
                    Some(Some(e[0].contents))
                }
            } else {
                Some(None)
            };
            let issuer = if j > i {
                match tagged_authority_issuer(e[i as int]) {
                    None => None,
                    Some(g) => Some(Some(g)),
                }
            } else {
                Some(None)
            };
            let serial = if k > j {
                match tagged_integer(e[j as int]) {
                    None => None,
                    Some(n) => Some(Some(n)),
                }
            } else {
                Some(None)
            };
            match (identifier, issuer, serial) {
                (
                    Some(key_identifier),
                    Some(authority_cert_issuer),
                    Some(authority_cert_serial_number),
                ) => {
                    // The WITH COMPONENTS constraint: both or neither.
                    if authority_cert_issuer.is_some()
                        != authority_cert_serial_number.is_some() {
                        None
                    } else {
                        Some(
                            AuthorityKeyIdentifier {
                                key_identifier,
                                authority_cert_issuer,
                                authority_cert_serial_number,
                                additions: from_index(e, k),
                            },
                        )
                    }
                },
                _ => None,
            }
        },
    }
}

/// 9.2.2.3 `KeyUsage`: a named bit list, so X.690 11.2.2 applies.
pub open spec fn decode_key_usage(t: Tlv) -> Option<BitString> {
    match decode_bit_string(t) {
        None => None,
        Some(b) => {
            if no_trailing_zero_bits(b) {
                Some(b)
            } else {
                None
            }
        },
    }
}

/// `KeyPurposeId`s from `i`.
pub open spec fn decode_key_purpose_list(e: Seq<Tlv>, i: nat) -> Option<Seq<ObjectIdentifier>>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<ObjectIdentifier>::empty())
    } else {
        match decode_object_identifier(e[i as int]) {
            None => None,
            Some(first) => match decode_key_purpose_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// 9.2.2.4 `SEQUENCE SIZE (1..MAX) OF KeyPurposeId`.
pub open spec fn decode_ext_key_usage(t: Tlv) -> Option<Seq<ObjectIdentifier>> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() == 0 {
                None
            } else {
                decode_key_purpose_list(e, 0)
            }
        },
    }
}

/// 9.2.2.6 `PolicyQualifierInfo`.
pub open spec fn decode_policy_qualifier_info(t: Tlv) -> Option<PolicyQualifierInfo> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() == 0 {
                None
            } else {
                match decode_object_identifier(e[0]) {
                    None => None,
                    Some(policy_qualifier_id) => Some(
                        PolicyQualifierInfo {
                            policy_qualifier_id,
                            qualifier: if e.len() > 1 {
                                Some(e[1])
                            } else {
                                None
                            },
                            additions: from_index(e, 2),
                        },
                    ),
                }
            }
        },
    }
}

/// Qualifiers from `i`.
pub open spec fn decode_policy_qualifier_list(e: Seq<Tlv>, i: nat) -> Option<
    Seq<PolicyQualifierInfo>,
>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<PolicyQualifierInfo>::empty())
    } else {
        match decode_policy_qualifier_info(e[i as int]) {
            None => None,
            Some(first) => match decode_policy_qualifier_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// 9.2.2.6 `PolicyInformation`. `policyQualifiers` is `SEQUENCE SIZE (1..MAX)
/// OF`, untagged and optional, so a universal 16 second element is it.
pub open spec fn decode_policy_information(t: Tlv) -> Option<PolicyInformation> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() == 0 {
                None
            } else {
                match decode_object_identifier(e[0]) {
                    None => None,
                    Some(policy_identifier) => {
                        if tag_at(e, 1, class_universal(), 16) {
                            match sequence_elements(e[1]) {
                                None => None,
                                Some(q) => {
                                    if q.len() == 0 {
                                        None
                                    } else {
                                        match decode_policy_qualifier_list(q, 0) {
                                            None => None,
                                            Some(list) => Some(
                                                PolicyInformation {
                                                    policy_identifier,
                                                    policy_qualifiers: Some(list),
                                                    additions: from_index(e, 2),
                                                },
                                            ),
                                        }
                                    }
                                },
                            }
                        } else {
                            Some(
                                PolicyInformation {
                                    policy_identifier,
                                    policy_qualifiers: None,
                                    additions: from_index(e, 1),
                                },
                            )
                        }
                    },
                }
            }
        },
    }
}

/// Policies from `i`.
pub open spec fn decode_policy_list(e: Seq<Tlv>, i: nat) -> Option<Seq<PolicyInformation>>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<PolicyInformation>::empty())
    } else {
        match decode_policy_information(e[i as int]) {
            None => None,
            Some(first) => match decode_policy_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// 9.2.2.6 `CertificatePoliciesSyntax`.
pub open spec fn decode_certificate_policies(t: Tlv) -> Option<Seq<PolicyInformation>> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() == 0 {
                None
            } else {
                decode_policy_list(e, 0)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// 9.4.2 Certification path constraints
// ---------------------------------------------------------------------------

/// 9.4.2.1 `BasicConstraintsSyntax`.
pub open spec fn decode_basic_constraints(t: Tlv) -> Option<BasicConstraintsSyntax> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            let i: nat = if tag_at(e, 0, class_universal(), 1) {
                1
            } else {
                0
            };
            let c_a = if i == 1 {
                match decode_boolean(e[0]) {
                    None => None,
                    Some(b) => {
                        // X.690 11.5: `cA BOOLEAN DEFAULT FALSE` never
                        // encodes FALSE.
                        if b {
                            Some(true)
                        } else {
                            None
                        }
                    },
                }
            } else {
                Some(false)
            };
            let j: nat = if tag_at(e, i, class_universal(), 2) {
                i + 1
            } else {
                i
            };
            let path_len = if j > i {
                match decode_integer(e[i as int]) {
                    None => None,
                    Some(v) => {
                        // INTEGER(0..MAX).
                        if v < 0 {
                            None
                        } else {
                            Some(Some(v as nat))
                        }
                    },
                }
            } else {
                Some(None)
            };
            match (c_a, path_len) {
                (Some(c_a), Some(path_len_constraint)) => Some(
                    BasicConstraintsSyntax { c_a, path_len_constraint, additions: from_index(e, j) },
                ),
                _ => None,
            }
        },
    }
}

/// 9.4.2.2 `GeneralSubtree`.
pub open spec fn decode_general_subtree(t: Tlv) -> Option<GeneralSubtree> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() == 0 {
                None
            } else {
                let i: nat = if tag_at(e, 1, class_context(), 0) {
                    2
                } else {
                    1
                };
                let j: nat = if tag_at(e, i, class_context(), 1) {
                    i + 1
                } else {
                    i
                };
                let minimum = if i == 2 {
                    match decode_tagged_non_negative(e[1]) {
                        None => None,
                        Some(v) => {
                            // X.690 11.5: `minimum ... DEFAULT 0` never
                            // encodes 0.
                            if v == 0 {
                                None
                            } else {
                                Some(v)
                            }
                        },
                    }
                } else {
                    Some(0nat)
                };
                let maximum = if j > i {
                    match decode_tagged_non_negative(e[i as int]) {
                        None => None,
                        Some(v) => Some(Some(v)),
                    }
                } else {
                    Some(None)
                };
                match (decode_general_name(e[0]), minimum, maximum) {
                    (Some(base), Some(minimum), Some(maximum)) => Some(
                        GeneralSubtree { base, minimum, maximum, additions: from_index(e, j) },
                    ),
                    _ => None,
                }
            }
        },
    }
}

/// Subtrees from `i`.
pub open spec fn decode_general_subtree_list(e: Seq<Tlv>, i: nat) -> Option<Seq<GeneralSubtree>>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<GeneralSubtree>::empty())
    } else {
        match decode_general_subtree(e[i as int]) {
            None => None,
            Some(first) => match decode_general_subtree_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// `[n] GeneralSubtrees`, implicit, `SIZE (1..MAX)`.
pub open spec fn decode_general_subtrees(t: Tlv) -> Option<Seq<GeneralSubtree>> {
    if !t.constructed {
        None
    } else {
        match parse_tlvs(t.contents) {
            None => None,
            Some(e) => {
                if e.len() == 0 {
                    None
                } else {
                    decode_general_subtree_list(e, 0)
                }
            },
        }
    }
}

/// 9.4.2.2 `NameConstraintsSyntax`.
pub open spec fn decode_name_constraints(t: Tlv) -> Option<NameConstraintsSyntax> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            let i: nat = if tag_at(e, 0, class_context(), 0) {
                1
            } else {
                0
            };
            let j: nat = if tag_at(e, i, class_context(), 1) {
                i + 1
            } else {
                i
            };
            // The WITH COMPONENTS constraint, and "At least one of
            // permittedSubtrees and excludedSubtrees components shall be
            // present."
            if j == 0 {
                None
            } else {
                let permitted = if i == 1 {
                    match decode_general_subtrees(e[0]) {
                        None => None,
                        Some(s) => Some(Some(s)),
                    }
                } else {
                    Some(None)
                };
                let excluded = if j > i {
                    match decode_general_subtrees(e[i as int]) {
                        None => None,
                        Some(s) => Some(Some(s)),
                    }
                } else {
                    Some(None)
                };
                match (permitted, excluded) {
                    (Some(permitted_subtrees), Some(excluded_subtrees)) => Some(
                        NameConstraintsSyntax {
                            permitted_subtrees,
                            excluded_subtrees,
                            additions: from_index(e, j),
                        },
                    ),
                    _ => None,
                }
            }
        },
    }
}

/// 9.4.2.3 `PolicyConstraintsSyntax`.
pub open spec fn decode_policy_constraints(t: Tlv) -> Option<PolicyConstraintsSyntax> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            let i: nat = if tag_at(e, 0, class_context(), 0) {
                1
            } else {
                0
            };
            let j: nat = if tag_at(e, i, class_context(), 1) {
                i + 1
            } else {
                i
            };
            // "At least one of the requireExplicitPolicy and the
            // inhibitPolicyMapping components shall be present."
            if j == 0 {
                None
            } else {
                let require = if i == 1 {
                    match decode_tagged_non_negative(e[0]) {
                        None => None,
                        Some(v) => Some(Some(v)),
                    }
                } else {
                    Some(None)
                };
                let inhibit = if j > i {
                    match decode_tagged_non_negative(e[i as int]) {
                        None => None,
                        Some(v) => Some(Some(v)),
                    }
                } else {
                    Some(None)
                };
                match (require, inhibit) {
                    (Some(require_explicit_policy), Some(inhibit_policy_mapping)) => Some(
                        PolicyConstraintsSyntax {
                            require_explicit_policy,
                            inhibit_policy_mapping,
                            additions: from_index(e, j),
                        },
                    ),
                    _ => None,
                }
            }
        },
    }
}

/// 9.4.2.4 `SkipCerts ::= INTEGER(0..MAX)`.
pub open spec fn decode_skip_certs(t: Tlv) -> Option<nat> {
    match decode_integer(t) {
        None => None,
        Some(v) => {
            if v < 0 {
                None
            } else {
                Some(v as nat)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// 7.2.1 Extension
// ---------------------------------------------------------------------------

/// `extnValue`'s `CONTAINING EXTENSION.&ExtnType ... ENCODED BY der`: decode
/// the octets as the type `id` selects.
pub open spec fn decode_extension_value(id: ObjectIdentifier, octets: Seq<u8>) -> Option<
    ExtensionValue,
> {
    if id == id_ce_authority_key_identifier() || id == id_ce_subject_key_identifier() || id
        == id_ce_key_usage() || id == id_ce_ext_key_usage() || id == id_ce_certificate_policies()
        || id == id_ce_subject_alt_name() || id == id_ce_basic_constraints() || id
        == id_ce_name_constraints() || id == id_ce_policy_constraints() || id
        == id_ce_inhibit_any_policy() {
        match parse_single(octets) {
            None => None,
            Some(t) => {
                if id == id_ce_authority_key_identifier() {
                    match decode_authority_key_identifier(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::AuthorityKeyIdentifier(v)),
                    }
                } else if id == id_ce_subject_key_identifier() {
                    match decode_octet_string(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::SubjectKeyIdentifier(v)),
                    }
                } else if id == id_ce_key_usage() {
                    match decode_key_usage(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::KeyUsage(v)),
                    }
                } else if id == id_ce_ext_key_usage() {
                    match decode_ext_key_usage(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::ExtKeyUsage(v)),
                    }
                } else if id == id_ce_certificate_policies() {
                    match decode_certificate_policies(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::CertificatePolicies(v)),
                    }
                } else if id == id_ce_subject_alt_name() {
                    match sequence_elements(t) {
                        None => None,
                        Some(e) => match general_names_from(e) {
                            None => None,
                            Some(v) => Some(ExtensionValue::SubjectAltName(v)),
                        },
                    }
                } else if id == id_ce_basic_constraints() {
                    match decode_basic_constraints(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::BasicConstraints(v)),
                    }
                } else if id == id_ce_name_constraints() {
                    match decode_name_constraints(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::NameConstraints(v)),
                    }
                } else if id == id_ce_policy_constraints() {
                    match decode_policy_constraints(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::PolicyConstraints(v)),
                    }
                } else {
                    match decode_skip_certs(t) {
                        None => None,
                        Some(v) => Some(ExtensionValue::InhibitAnyPolicy(v)),
                    }
                }
            },
        }
    } else {
        Some(ExtensionValue::Unrecognized)
    }
}

/// 7.2.1 `Extension`.
pub open spec fn decode_extension(t: Tlv) -> Option<Extension> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() < 2 {
                None
            } else {
                let i: nat = if tag_at(e, 1, class_universal(), 1) {
                    2
                } else {
                    1
                };
                let critical = if i == 2 {
                    match decode_boolean(e[1]) {
                        None => None,
                        Some(b) => {
                            // X.690 11.5: `critical BOOLEAN DEFAULT FALSE`
                            // never encodes FALSE.
                            if b {
                                Some(true)
                            } else {
                                None
                            }
                        },
                    }
                } else {
                    Some(false)
                };
                if i >= e.len() {
                    None
                } else {
                    match (
                        decode_object_identifier(e[0]),
                        critical,
                        decode_octet_string(e[i as int]),
                    ) {
                        (Some(extn_id), Some(critical), Some(extn_value)) => {
                            match decode_extension_value(extn_id, extn_value) {
                                None => None,
                                Some(value) => Some(
                                    Extension {
                                        extn_id,
                                        critical,
                                        extn_value,
                                        value,
                                        additions: from_index(e, i + 1),
                                    },
                                ),
                            }
                        },
                        _ => None,
                    }
                }
            }
        },
    }
}

/// Extensions from `i`.
pub open spec fn decode_extension_list(e: Seq<Tlv>, i: nat) -> Option<Seq<Extension>>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<Extension>::empty())
    } else {
        match decode_extension(e[i as int]) {
            None => None,
            Some(first) => match decode_extension_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

} // verus!
