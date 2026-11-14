//! The public-key certificate, transcribed for the independent decoder from
//! Rec. ITU-T X.509 (10/2019) | ISO/IEC 9594-8:2020, clauses 6.2 and 7.2 and
//! the module `AuthenticationFramework` of Annex A (PDF SHA-256
//! `1f4ea2939ecc31a3433c499084d485e770f9b8dcee55a0ba9fe4c27128822e8c`), and
//! `Name` from Rec. ITU-T X.501 (10/2019) | ISO/IEC 9594-2:2020, clauses 9.2
//! and 9.3 (PDF SHA-256
//! `fa16c552c65a67ed0ab5be0291db368fc38ad94cb64df0bd90a9747586a3751b`), and
//! `UniqueIdentifier` from Rec. ITU-T X.520 (10/2019) | ISO/IEC 9594-6:2020
//! (PDF SHA-256
//! `78cac8b619e69af06ae0ae9216716d400117152086e85c4ad267efef80bd3fd1`).
//!
//! Not read while writing this file: see the list in `independent/mod.rs`.
//!
//! Modelling choices:
//! - This file decides what is a value of the ASN.1 type, encoded in DER. That
//!   covers the notation's own constraints (`SIZE`, `WITH COMPONENTS`,
//!   `DEFAULT`) and X.690. The prose's "shall" clauses about a value's
//!   content are in `requirements.rs`, so each refusal says which text
//!   caused it.
//! - `AuthenticationFramework` has an empty `TagDefault`, so tags are explicit
//!   (X.680 31.2.7 b)) unless marked IMPLICIT: `version` and `extensions`
//!   wrap their base encoding (X.690 8.14.3), and the two unique identifiers
//!   replace its tag (8.14.4).
//! - `Name` is a CHOICE of one alternative, so it has that alternative's tag
//!   and encoding (X.690 8.13), and the decoded value is the RDN list.
//! - An attribute value is an open type (`ATTRIBUTE.&Type`), kept as one
//!   encoding. Attribute types are not interpreted here.
//! - The object sets `SupportedAlgorithms`, `SupportedAltAlgorithms` and
//!   `ExtensionSet` are all `{...}`: left to referencing specifications. So
//!   any object identifier is a value of `algorithm`, and `parameters` is
//!   kept as one encoding, unread.
//!
//! Open choices, all listed in the pull request:
//! - Extensibility. `Certificate`, `TBSCertificate`, `Validity`,
//!   `SubjectPublicKeyInfo`, `AlgorithmIdentifier`, `AttributeTypeAndValue`
//!   and `Extension` all have an extension marker `...`. X.690 8.1.1.4's NOTE
//!   treats extensions as if they were in the root, so a later edition's
//!   component is a legal encoding, and X.509 7.3 points to the ignoring
//!   rule of X.519 12.2.2 (not read: X.519 is outside this file's sources).
//!   Every such type therefore keeps what follows its known components in a
//!   field `additions`, instead of refusing. A caller that wants a closed
//!   reading tests [`additions_absent`].
//! - X.509 7.2.1 requires DER for the TBSCertificate, and NOTE 2 calls a
//!   non-DER outer SEQUENCE a matter of local policy. This decoder requires
//!   DER for the whole Certificate.
//! - `version` is any INTEGER other than the DEFAULT: `Version`'s named
//!   numbers do not constrain it (X.680 19.3), so v4 is refused only by
//!   `requirements.rs`.
//! - Nothing here limits `serialNumber` or makes it positive: X.509 sets no
//!   such limit.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der::*;
use super::der::{BitString, Moment, Tlv};
use super::extensions::Extension;
#[cfg(verus_only)]
use super::extensions::*;

verus! {

/// An OBJECT IDENTIFIER value: its components.
pub type ObjectIdentifier = Seq<nat>;

/// X.509 6.2.2 `AlgorithmIdentifier`.
pub struct AlgorithmIdentifier {
    /// `algorithm`.
    pub algorithm: ObjectIdentifier,
    /// `parameters`.
    pub parameters: Option<Tlv>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
    /// The whole encoding, for 7.2.1's "the same value".
    pub encoding: Seq<u8>,
}

/// X.501 9.3 `AttributeTypeAndValue`.
pub struct AttributeTypeAndValue {
    /// `type`.
    pub attribute_type: ObjectIdentifier,
    /// The value.
    pub value: Tlv,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// X.501 9.3 `RelativeDistinguishedName`.
pub type RelativeDistinguishedName = Seq<AttributeTypeAndValue>;

/// X.501 9.2 `Name`, by its one alternative `rdnSequence`.
pub struct Name {
    /// `rdnSequence`.
    pub rdn_sequence: Seq<RelativeDistinguishedName>,
}

/// X.509 7.2.1 `Time`.
pub enum Time {
    /// The `utcTime` alternative.
    UtcTime(Moment),
    /// The `generalizedTime` alternative.
    GeneralizedTime(Moment),
}

/// X.509 7.2.1 `Validity`.
pub struct Validity {
    /// `notBefore`.
    pub not_before: Time,
    /// `notAfter`.
    pub not_after: Time,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// X.509 7.2.1 `SubjectPublicKeyInfo`.
pub struct SubjectPublicKeyInfo {
    /// `algorithm`.
    pub algorithm: AlgorithmIdentifier,
    /// `subjectPublicKey`.
    pub subject_public_key: BitString,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// X.509 7.2.1 `TBSCertificate`.
pub struct TBSCertificate {
    /// `v1` is 0, `v2` 1 and `v3` 2.
    pub version: int,
    /// `serialNumber`.
    pub serial_number: int,
    /// `signature`.
    pub signature: AlgorithmIdentifier,
    /// `issuer`.
    pub issuer: Name,
    /// `validity`.
    pub validity: Validity,
    /// `subject`.
    pub subject: Name,
    /// `subjectPublicKeyInfo`.
    pub subject_public_key_info: SubjectPublicKeyInfo,
    /// `issuerUniqueIdentifier`.
    pub issuer_unique_identifier: Option<BitString>,
    /// `subjectUniqueIdentifier`.
    pub subject_unique_identifier: Option<BitString>,
    /// `extensions`.
    pub extensions: Option<Seq<Extension>>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
    /// The octets the signature covers.
    pub encoding: Seq<u8>,
}

/// X.509 6.2.1 `SIGNED{TBSCertificate}`, with `COMPONENTS OF SIGNATURE`
/// written out as Annex A writes it.
pub struct Certificate {
    /// `toBeSigned`.
    pub to_be_signed: TBSCertificate,
    /// `algorithmIdentifier`.
    pub algorithm_identifier: AlgorithmIdentifier,
    /// `signature`.
    pub signature: BitString,
    /// `altAlgorithmIdentifier`.
    pub alt_algorithm_identifier: Option<AlgorithmIdentifier>,
    /// `altSignature`.
    pub alt_signature: Option<BitString>,
    /// Components after the known ones (see `structures.rs`).
    pub additions: Seq<Tlv>,
}

/// SEQUENCE is universal 16, constructed (X.680 Table 1, X.690 8.9.1): the
/// list of encodings in its contents.
pub open spec fn sequence_elements(t: Tlv) -> Option<Seq<Tlv>> {
    if !has_tag(t, class_universal(), 16, true) {
        None
    } else {
        parse_tlvs(t.contents)
    }
}

/// X.509 6.2.2 `AlgorithmIdentifier`.
pub open spec fn decode_algorithm_identifier(t: Tlv) -> Option<AlgorithmIdentifier> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() < 1 {
                None
            } else {
                match decode_object_identifier(e[0]) {
                    None => None,
                    Some(algorithm) => {
                        // `parameters` is OPTIONAL and of an open type, so
                        // whatever comes next is it.
                        let parameters = if e.len() > 1 {
                            Some(e[1])
                        } else {
                            None
                        };
                        Some(
                            AlgorithmIdentifier {
                                algorithm,
                                parameters,
                                additions: from_index(e, 2),
                                encoding: t.encoding,
                            },
                        )
                    },
                }
            }
        },
    }
}

/// X.501 9.3 `AttributeTypeAndValue`.
pub open spec fn decode_attribute_type_and_value(t: Tlv) -> Option<AttributeTypeAndValue> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() < 2 {
                None
            } else {
                match decode_object_identifier(e[0]) {
                    None => None,
                    Some(attribute_type) => Some(
                        AttributeTypeAndValue {
                            attribute_type,
                            value: e[1],
                            additions: from_index(e, 2),
                        },
                    ),
                }
            }
        },
    }
}

/// The components of a set-of, from `i`.
pub open spec fn decode_attribute_list(e: Seq<Tlv>, i: nat) -> Option<RelativeDistinguishedName>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<AttributeTypeAndValue>::empty())
    } else {
        match decode_attribute_type_and_value(e[i as int]) {
            None => None,
            Some(first) => match decode_attribute_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// X.501 9.3 `RelativeDistinguishedName ::= SET SIZE (1..MAX) OF
/// AttributeTypeAndValue`. SET OF is universal 17, constructed (X.690 8.12.1).
pub open spec fn decode_relative_distinguished_name(t: Tlv) -> Option<RelativeDistinguishedName> {
    if !has_tag(t, class_universal(), 17, true) {
        None
    } else {
        match parse_tlvs(t.contents) {
            None => None,
            Some(e) => {
                // SIZE (1..MAX).
                if e.len() == 0 {
                    None
                } else if !set_of_ordered(e, 0) {
                    // X.690 11.6.
                    None
                } else {
                    decode_attribute_list(e, 0)
                }
            },
        }
    }
}

/// The RDNs from `i` (X.690 8.10).
pub open spec fn decode_rdn_list(e: Seq<Tlv>, i: nat) -> Option<Seq<RelativeDistinguishedName>>
    decreases e.len() - i,
{
    if i >= e.len() {
        Some(Seq::<RelativeDistinguishedName>::empty())
    } else {
        match decode_relative_distinguished_name(e[i as int]) {
            None => None,
            Some(first) => match decode_rdn_list(e, i + 1) {
                None => None,
                Some(rest) => Some(seq![first] + rest),
            },
        }
    }
}

/// X.501 9.2 `Name`. `RDNSequence` has no size constraint, so the empty
/// sequence is a value here.
pub open spec fn decode_name(t: Tlv) -> Option<Name> {
    match sequence_elements(t) {
        None => None,
        Some(e) => match decode_rdn_list(e, 0) {
            None => None,
            Some(rdn_sequence) => Some(Name { rdn_sequence }),
        },
    }
}

/// X.509 7.2.1 `Time`: the tag chooses the alternative (X.690 8.13). UTCTime
/// is universal 23 and GeneralizedTime 24 (X.680 47.3 and 46.3), each a
/// string type and so primitive (X.690 10.2).
pub open spec fn decode_time(t: Tlv) -> Option<Time> {
    if has_tag(t, class_universal(), 23, false) {
        match utc_time_contents(t.contents) {
            None => None,
            Some(m) => Some(Time::UtcTime(m)),
        }
    } else if has_tag(t, class_universal(), 24, false) {
        match generalized_time_contents(t.contents) {
            None => None,
            Some(m) => Some(Time::GeneralizedTime(m)),
        }
    } else {
        None
    }
}

/// X.509 7.2.1 `Validity`.
pub open spec fn decode_validity(t: Tlv) -> Option<Validity> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() < 2 {
                None
            } else {
                match (decode_time(e[0]), decode_time(e[1])) {
                    (Some(not_before), Some(not_after)) => Some(
                        Validity { not_before, not_after, additions: from_index(e, 2) },
                    ),
                    _ => None,
                }
            }
        },
    }
}

/// X.509 7.2.1 `SubjectPublicKeyInfo`.
pub open spec fn decode_subject_public_key_info(t: Tlv) -> Option<SubjectPublicKeyInfo> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            if e.len() < 2 {
                None
            } else {
                match (decode_algorithm_identifier(e[0]), decode_bit_string(e[1])) {
                    (Some(algorithm), Some(subject_public_key)) => Some(
                        SubjectPublicKeyInfo {
                            algorithm,
                            subject_public_key,
                            additions: from_index(e, 2),
                        },
                    ),
                    _ => None,
                }
            }
        },
    }
}

/// `version [0] Version DEFAULT v1`, an explicit tag (X.690 8.14.3): the
/// contents are one complete INTEGER.
pub open spec fn decode_version(t: Tlv) -> Option<int> {
    if !t.constructed {
        None
    } else {
        match parse_single(t.contents) {
            None => None,
            Some(inner) => match decode_integer(inner) {
                None => None,
                Some(v) => {
                    // X.690 11.5: "shall not include an encoding for any
                    // component value which is equal to its default value".
                    if v == 0 {
                        None
                    } else {
                        Some(v)
                    }
                },
            },
        }
    }
}

/// `extensions [3] Extensions OPTIONAL`, an explicit tag around
/// `SEQUENCE SIZE (1..MAX) OF Extension`.
pub open spec fn decode_extensions_field(t: Tlv) -> Option<Seq<Extension>> {
    if !t.constructed {
        None
    } else {
        match parse_single(t.contents) {
            None => None,
            Some(inner) => match sequence_elements(inner) {
                None => None,
                Some(e) => {
                    // SIZE (1..MAX).
                    if e.len() == 0 {
                        None
                    } else {
                        decode_extension_list(e, 0)
                    }
                },
            },
        }
    }
}

/// The position after `version`.
pub open spec fn after_version(e: Seq<Tlv>) -> nat {
    if tag_at(e, 0, class_context(), 0) {
        1
    } else {
        0
    }
}

/// The value of the optional `version`, when it decodes.
pub open spec fn version_component(e: Seq<Tlv>) -> Option<int> {
    if tag_at(e, 0, class_context(), 0) {
        decode_version(e[0])
    } else {
        // "DEFAULT v1".
        Some(0)
    }
}

/// An optional `[n] IMPLICIT UniqueIdentifier` at `i`. The outer `Option` is
/// the decoding, the inner one presence.
pub open spec fn unique_identifier_component(e: Seq<Tlv>, i: nat, number: nat) -> Option<
    Option<BitString>,
> {
    if tag_at(e, i, class_context(), number) {
        match decode_tagged_bit_string(e[i as int]) {
            None => None,
            Some(b) => Some(Some(b)),
        }
    } else {
        Some(None)
    }
}

/// The optional `extensions` at `i`.
pub open spec fn extensions_component(e: Seq<Tlv>, i: nat) -> Option<Option<Seq<Extension>>> {
    if tag_at(e, i, class_context(), 3) {
        match decode_extensions_field(e[i as int]) {
            None => None,
            Some(x) => Some(Some(x)),
        }
    } else {
        Some(None)
    }
}

/// The value of an optional component, as a position step.
pub open spec fn step<T>(present: Option<T>) -> nat {
    match present {
        None => 0,
        Some(_) => 1,
    }
}

/// X.509 7.2.1 `TBSCertificate`. The components come in the order of the
/// definition (X.690 8.9.2), with an absent OPTIONAL or DEFAULT component
/// taking no place (8.9.3).
pub open spec fn decode_tbs_certificate(t: Tlv) -> Option<TBSCertificate> {
    match sequence_elements(t) {
        None => None,
        Some(e) => {
            let i = after_version(e);
            // serialNumber to subjectPublicKeyInfo: six required components.
            if i + 6 > e.len() {
                None
            } else {
                match (
                    version_component(e),
                    decode_integer(e[i as int]),
                    decode_algorithm_identifier(e[(i + 1) as int]),
                    decode_name(e[(i + 2) as int]),
                    decode_validity(e[(i + 3) as int]),
                    decode_name(e[(i + 4) as int]),
                    decode_subject_public_key_info(e[(i + 5) as int]),
                ) {
                    (
                        Some(version),
                        Some(serial_number),
                        Some(signature),
                        Some(issuer),
                        Some(validity),
                        Some(subject),
                        Some(subject_public_key_info),
                    ) => {
                        let j = i + 6;
                        match unique_identifier_component(e, j, 1) {
                            None => None,
                            Some(issuer_unique_identifier) => {
                                let k = j + step(issuer_unique_identifier);
                                match unique_identifier_component(e, k, 2) {
                                    None => None,
                                    Some(subject_unique_identifier) => {
                                        let l = k + step(subject_unique_identifier);
                                        match extensions_component(e, l) {
                                            None => None,
                                            Some(extensions) => Some(
                                                TBSCertificate {
                                                    version,
                                                    serial_number,
                                                    signature,
                                                    issuer,
                                                    validity,
                                                    subject,
                                                    subject_public_key_info,
                                                    issuer_unique_identifier,
                                                    subject_unique_identifier,
                                                    extensions,
                                                    additions: from_index(e, l + step(extensions)),
                                                    encoding: t.encoding,
                                                },
                                            ),
                                        }
                                    },
                                }
                            },
                        }
                    },
                    _ => None,
                }
            }
        },
    }
}

/// X.509 6.2.1 `SIGNED`: the components after the extension marker, from
/// position 3, as (altAlgorithmIdentifier, altSignature, next position), or
/// `None` when the `WITH COMPONENTS` constraint fails: the two are present
/// together or absent together.
pub open spec fn alternative_signature(e: Seq<Tlv>) -> Option<
    (Option<AlgorithmIdentifier>, Option<BitString>, nat),
> {
    if tag_at(e, 3, class_universal(), 16) {
        if e.len() < 5 {
            None
        } else {
            match (decode_algorithm_identifier(e[3]), decode_bit_string(e[4])) {
                (Some(a), Some(s)) => Some((Some(a), Some(s), 5)),
                _ => None,
            }
        }
    } else if tag_at(e, 3, class_universal(), 3) {
        // altSignature without altAlgorithmIdentifier.
        None
    } else {
        Some((None, None, 3))
    }
}

/// X.509 7.2.1 `Certificate ::= SIGNED{TBSCertificate}`, from the octets of
/// exactly one encoding.
pub open spec fn decode_certificate(der: Seq<u8>) -> Option<Certificate> {
    match parse_single(der) {
        None => None,
        Some(t) => match sequence_elements(t) {
            None => None,
            Some(e) => {
                if e.len() < 3 {
                    None
                } else {
                    match (
                        decode_tbs_certificate(e[0]),
                        decode_algorithm_identifier(e[1]),
                        decode_bit_string(e[2]),
                        alternative_signature(e),
                    ) {
                        (
                            Some(to_be_signed),
                            Some(algorithm_identifier),
                            Some(signature),
                            Some((alt_algorithm_identifier, alt_signature, next)),
                        ) => Some(
                            Certificate {
                                to_be_signed,
                                algorithm_identifier,
                                signature,
                                alt_algorithm_identifier,
                                alt_signature,
                                additions: from_index(e, next),
                            },
                        ),
                        _ => None,
                    }
                }
            },
        },
    }
}

/// No extension-addition components anywhere outside the extensions' values:
/// the closed reading of the open choice at the top of this file.
pub open spec fn additions_absent(c: Certificate) -> bool {
    let tbs = c.to_be_signed;
    c.additions.len() == 0 && tbs.additions.len() == 0 && tbs.validity.additions.len() == 0
        && tbs.subject_public_key_info.additions.len() == 0
        && tbs.subject_public_key_info.algorithm.additions.len() == 0
        && tbs.signature.additions.len() == 0 && c.algorithm_identifier.additions.len() == 0
}

} // verus!
