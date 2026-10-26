//! RFC 5280 §4.1.2.9 certificate extension and §4.2.1.6 SAN specification.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2.9>
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.6>
//!
//! RFC 9525 uses subjectAltName dNSName and iPAddress values as DNS-ID and
//! IP-ID inputs: <https://www.rfc-editor.org/rfc/rfc9525.html#section-4.1>.
//!
//! Modelling choices and limits:
//! - `parse_extensions` receives the complete DER `Extensions` SEQUENCE TLV
//!   (the inner value of TBSCertificate's optional `[3] EXPLICIT` field).
//! - Every Extension is parsed as OID, optional `critical`, and OCTET STRING.
//!   OIDs must be unique. An explicit BOOLEAN FALSE is rejected because DER
//!   §11.5 omits values equal to a DEFAULT (critical defaults to FALSE).
//! - Extension `extnValue` bytes are preserved without interpreting their
//!   extension-specific DER. Parsing these bytes does not validate extension
//!   semantics, path constraints, signatures, trust, or unknown critical OIDs.
//!   The caller must process recognized critical extensions and reject any
//!   critical extension whose semantics it cannot process (RFC 5280 §4.2).
//! - GeneralNames must be a nonempty DER SEQUENCE. dNSName must be nonempty
//!   ASCII IA5 and iPAddress must contain exactly 4 or 16 octets. DNS label
//!   syntax and matching are handled by the existing RFC 9525 identity layer.
//! - Other GeneralName alternatives are retained as opaque complete DER TLVs
//!   after checking their context-specific tag number and primitive/constructed
//!   form. This is syntax preservation, not semantic validation of those forms.
//! - Wildcards are preserved unchanged; RFC 5280 does not define their
//!   matching semantics, which RFC 9525 does for DNS-ID.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One Extension value (RFC 5280 §4.1.2.9).
pub struct Extension {
    /// extnID object identifier arcs.
    pub oid: Seq<nat>,
    /// Criticality; omitted DER DEFAULT FALSE is represented as false.
    pub critical: bool,
    /// extnValue OCTET STRING contents, kept opaque by the container parser.
    pub value: Seq<u8>,
}

/// A supported GeneralName extracted from subjectAltName, or an opaque
/// complete TLV for a recognized but otherwise unparsed GeneralName form.
pub enum GeneralName {
    /// dNSName [2] IA5String content bytes.
    DnsName(Seq<u8>),
    /// iPAddress [7] network-order address octets (4 or 16 bytes).
    IpAddress(Seq<u8>),
    /// Other RFC 5280 GeneralName [0..=8] TLV bytes, preserved without
    /// interpreting the alternative-specific internal structure.
    Other(u32, Seq<u8>),
}

/// Parsed nonempty GeneralNames sequence.
pub struct SubjectAltName {
    /// Original order of the GeneralName choices.
    pub names: Seq<GeneralName>,
}

/// OID arcs for id-ce-subjectAltName ::= { id-ce 17 }.
pub open spec fn subject_alt_name_oid() -> Seq<nat> {
    seq![2nat, 5, 29, 17]
}

/// True when an OID appears in the already parsed prefix.
pub open spec fn oid_seen(seen: Seq<Seq<nat>>, oid: Seq<nat>, i: int) -> bool
    recommends 0 <= i <= seen.len()
    decreases seen.len() as int - i
{
    i < seen.len() && (seen[i] =~= oid || oid_seen(seen, oid, i + 1))
}

/// RFC 5280 §4.1.2.9: one Extension SEQUENCE with a required extnID,
/// optional critical BOOLEAN DEFAULT FALSE, and required extnValue OCTET STRING.
pub open spec fn parse_extension(input: Seq<u8>, pos: nat, end: nat) -> Option<(Extension, nat)> {
    match clazel_der::spec::expect_sequence(input, pos, end) {
        None => None,
        Some((contents_start, contents_end)) => match clazel_der::spec::read_tlv(input, pos, end) {
            Some(outer) if outer.cstart == contents_start && outer.cend == contents_end =>
                match clazel_der::spec::read_oid(input, contents_start, contents_end) {
                    None => None,
                    Some((oid, after_oid)) => match clazel_der::spec::read_tlv(input, after_oid, contents_end) {
                        None => None,
                        Some(field) if field.tag == clazel_der::spec::universal_primitive(clazel_der::spec::BOOLEAN) =>
                            match clazel_der::spec::read_boolean(input, after_oid, contents_end) {
                                Some((true, after_critical)) => match clazel_der::spec::read_octet_string(input, after_critical, contents_end) {
                                    Some((value_start, value_end)) if value_end == contents_end => Some((Extension {
                                        oid,
                                        critical: true,
                                        value: input.subrange(value_start as int, value_end as int),
                                    }, contents_end)),
                                    _ => None,
                                },
                                // DER §11.5: the DEFAULT FALSE component must be absent.
                                _ => None,
                            },
                        Some(_) => match clazel_der::spec::read_octet_string(input, after_oid, contents_end) {
                            Some((value_start, value_end)) if value_end == contents_end => Some((Extension {
                                oid,
                                critical: false,
                                value: input.subrange(value_start as int, value_end as int),
                            }, contents_end)),
                            _ => None,
                        },
                    },
                },
            _ => None,
        },
    }
}

/// Accumulator form of the Extension reader, used to align its prefix with
/// an iterative executable cursor without recursively constructing a suffix.
pub open spec fn parse_extensions_acc(
    input: Seq<u8>, pos: nat, end: nat, seen: Seq<Seq<nat>>, acc: Seq<Extension>,
) -> Option<(Seq<Extension>, nat)>
    recommends pos <= end && end <= input.len()
    decreases end - pos
{
    if pos == end {
        Some((acc, end))
    } else {
        match parse_extension(input, pos, end) {
            Some((extension, next)) if next > pos && next <= end
                && !oid_seen(seen, extension.oid, 0) =>
                parse_extensions_acc(input, next, end, seen.push(extension.oid), acc.push(extension)),
            _ => None,
        }
    }
}

/// Read Extension SEQUENCE values through `end`, rejecting duplicate OIDs.
pub open spec fn parse_extensions_from(
    input: Seq<u8>, pos: nat, end: nat, seen: Seq<Seq<nat>>,
) -> Option<(Seq<Extension>, nat)>
    recommends pos <= end && end <= input.len()
{
    parse_extensions_acc(input, pos, end, seen, seq![])
}

/// RFC 5280 §4.1.2.9: parse one nonempty DER Extensions SEQUENCE and consume
/// the complete TLV.
pub open spec fn parse_extensions(input: Seq<u8>) -> Option<Seq<Extension>> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((contents_start, contents_end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == contents_start && outer.cend == contents_end
                && outer.cend == input.len() && contents_start < contents_end =>
            match parse_extensions_from(input, contents_start, contents_end, seq![]) {
                Some((extensions, final_pos)) if final_pos == contents_end && extensions.len() > 0 => Some(extensions),
                _ => None,
            },
            _ => None,
        },
    }
}

/// Whether a context-specific GeneralName tag uses the constructed form.
pub open spec fn general_name_constructed(number: u32) -> bool {
    number == 0 || number == 3 || number == 4 || number == 5
}

/// Every byte in a sequence is a 7-bit IA5 character.
pub open spec fn ia5_bytes(bytes: Seq<u8>, i: int) -> bool
    recommends 0 <= i <= bytes.len()
    decreases bytes.len() as int - i
{
    i >= bytes.len() as int || bytes[i] < 128 && ia5_bytes(bytes, i + 1)
}

/// RFC 5280 §4.2.1.6: decode one context-specific GeneralName choice.
/// Unsupported alternatives keep their full DER TLV for a later processor.
pub open spec fn parse_general_name(input: Seq<u8>, pos: nat, end: nat) -> Option<(GeneralName, nat)> {
    match clazel_der::spec::read_tlv(input, pos, end) {
        None => None,
        Some(tlv) if tlv.tag.class == clazel_der::spec::Class::ContextSpecific
            && tlv.tag.number <= 8
            && tlv.tag.constructed == general_name_constructed(tlv.tag.number) =>
        {
            if tlv.tag.number == 2 {
                let value = input.subrange(tlv.cstart as int, tlv.cend as int);
                if value.len() > 0 && ia5_bytes(value, 0) {
                    Some((GeneralName::DnsName(value), tlv.cend))
                } else { None }
            } else if tlv.tag.number == 7 {
                let value = input.subrange(tlv.cstart as int, tlv.cend as int);
                if value.len() == 4 || value.len() == 16 {
                    Some((GeneralName::IpAddress(value), tlv.cend))
                } else { None }
            } else {
                Some((GeneralName::Other(tlv.tag.number,
                    input.subrange(pos as int, tlv.cend as int)), tlv.cend))
            }
        },
        _ => None,
    }
}

/// Read the nonempty ordered GeneralName list in a SubjectAltName value.
pub open spec fn parse_general_names_from(input: Seq<u8>, pos: nat, end: nat)
    -> Option<(Seq<GeneralName>, nat)>
    recommends pos <= end && end <= input.len()
    decreases end - pos
{
    if pos == end {
        Some((seq![], end))
    } else {
        match parse_general_name(input, pos, end) {
            Some((name, next)) if next > pos && next <= end =>
                match parse_general_names_from(input, next, end) {
                    Some((rest, final_pos)) => Some((seq![name] + rest, final_pos)),
                    None => None,
                },
            _ => None,
        }
    }
}

/// RFC 5280 §4.2.1.6: parse a complete nonempty DER GeneralNames SEQUENCE.
pub open spec fn parse_subject_alt_name(input: Seq<u8>) -> Option<SubjectAltName> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((contents_start, contents_end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == contents_start && outer.cend == contents_end
                && outer.cend == input.len() && contents_start < contents_end =>
            match parse_general_names_from(input, contents_start, contents_end) {
                Some((names, final_pos)) if final_pos == contents_end && names.len() > 0 =>
                    Some(SubjectAltName { names }),
                _ => None,
            },
            _ => None,
        },
    }
}

} // verus!
