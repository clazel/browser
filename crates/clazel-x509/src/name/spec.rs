//! RFC 5280 §4.1.2.4 and §4.1.2.6 Name structure, with DER SET OF ordering.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2.4>
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2.6>
//! DER ordering is ITU-T X.690 (08/2015) §11.6:
//! <https://www.itu.int/rec/T-REC-X.690-201508-I/en>
//!
//! Modelling choices and limits:
//! - A Name is the `rdnSequence` CHOICE arm and its input is exactly one
//!   complete DER SEQUENCE TLV. An empty RDNSequence is retained because the
//!   ASN.1 declaration gives the outer SEQUENCE OF no minimum size; RFC 5280
//!   issuer/subject policy is a separate caller decision.
//! - Every RelativeDistinguishedName is a nonempty SET OF, as required by the
//!   `SIZE (1..MAX)` constraint. Its AttributeTypeAndValue encodings are
//!   checked using X.690 §11.6's octet comparison with trailing zero padding.
//! - Each AttributeTypeAndValue is a SEQUENCE containing one OBJECT
//!   IDENTIFIER followed by exactly one complete DER TLV for its open value.
//!   The value is retained opaque; attribute-specific syntax and Directory
//!   String validation/equivalence are outside this decoder.
//! - Full original Name, RDN and AttributeTypeAndValue TLV bytes are retained.
//!   This parser does not recursively validate the opaque open value's inner
//!   constructed contents, nor does it claim RFC 5280 §7.1 comparison.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One AttributeTypeAndValue from RFC 5280 §4.1.2.4/.6.
pub struct AttributeTypeAndValue {
    /// Complete original SEQUENCE TLV.
    pub der: Seq<u8>,
    /// AttributeType OBJECT IDENTIFIER arcs.
    pub oid: Seq<nat>,
    /// Complete original open-type value TLV, retained without interpretation.
    pub value_der: Seq<u8>,
    /// Tag of the retained open-type value.
    pub value_tag: clazel_der::spec::Tag,
}

/// One nonempty SET OF AttributeTypeAndValue.
pub struct RelativeDistinguishedName {
    /// Complete original SET TLV.
    pub der: Seq<u8>,
    /// Attributes in their encoded DER SET OF order.
    pub attributes: Seq<AttributeTypeAndValue>,
}

/// A Name's `rdnSequence` arm, retaining the original encoding.
pub struct Name {
    /// Complete original Name SEQUENCE TLV.
    pub der: Seq<u8>,
    /// Ordered sequence of RDNs.
    pub rdns: Seq<RelativeDistinguishedName>,
}

/// X.690 §11.6 compares octet strings after padding the shorter one with
/// trailing zero octets. This is the non-strict ordering used by SET OF.
pub open spec fn der_octets_le(a: Seq<u8>, b: Seq<u8>) -> bool
    decreases if a.len() > b.len() { a.len() } else { b.len() }
{
    der_octets_le_at(a, b, 0)
}

/// Compare through the maximum original extent, treating missing octets as 0.
pub open spec fn der_octets_le_at(a: Seq<u8>, b: Seq<u8>, i: nat) -> bool
    decreases (if a.len() > b.len() { a.len() } else { b.len() }) - i
{
    let n = if a.len() > b.len() { a.len() } else { b.len() };
    if i >= n { true }
    else {
        let x = if i < a.len() { a[i as int] as nat } else { 0 };
        let y = if i < b.len() { b[i as int] as nat } else { 0 };
        if x < y { true }
        else if x > y { false }
        else { der_octets_le_at(a, b, i + 1) }
    }
}

/// RFC 5280 §4.1.2.6 AttributeTypeAndValue: OID followed by one open value.
pub open spec fn parse_attribute(input: Seq<u8>, pos: nat, end: nat)
    -> Option<(AttributeTypeAndValue, nat)>
{
    match clazel_der::spec::expect_sequence(input, pos, end) {
        None => None,
        Some((start, finish)) => match clazel_der::spec::read_tlv(input, pos, end) {
            None => None,
            Some(sequence) => match clazel_der::spec::read_oid(input, start, finish) {
                None => None,
                Some((oid, after_oid)) => match clazel_der::spec::read_tlv(input, after_oid, finish) {
                    Some(value) if value.cend == finish => Some((AttributeTypeAndValue {
                        der: input.subrange(pos as int, sequence.cend as int),
                        oid,
                        value_der: input.subrange(after_oid as int, finish as int),
                        value_tag: value.tag,
                    }, sequence.cend)),
                    _ => None,
                },
            },
        },
    }
}

/// Parse the complete contents of one nonempty RDN SET OF.
pub open spec fn parse_attributes(
    input: Seq<u8>, pos: nat, end: nat, prior: Option<Seq<u8>>,
) -> Option<Seq<AttributeTypeAndValue>>
    decreases end - pos
{
    if pos == end { Some(Seq::empty()) }
    else {
        match parse_attribute(input, pos, end) {
            None => None,
            Some((attribute, next)) if next > pos && next <= end => {
                let ordered = match prior {
                    None => true,
                    Some(previous) => der_octets_le(previous, attribute.der),
                };
                if !ordered { None }
                else { match parse_attributes(input, next, end, Some(attribute.der)) {
                    None => None,
                    Some(rest) => Some(seq![attribute] + rest),
                }}
            },
            _ => None,
        }
    }
}

/// RFC 5280 §4.1.2.4 RelativeDistinguishedName ::= SET SIZE (1..MAX) OF ATV.
pub open spec fn parse_rdn(input: Seq<u8>, pos: nat, end: nat)
    -> Option<(RelativeDistinguishedName, nat)>
{
    match clazel_der::spec::expect_set(input, pos, end) {
        None => None,
        Some((start, finish)) => match clazel_der::spec::read_tlv(input, pos, end) {
            None => None,
            Some(set) => match parse_attributes(input, start, finish, None) {
                Some(attributes) if attributes.len() > 0 => Some((RelativeDistinguishedName {
                    der: input.subrange(pos as int, set.cend as int),
                    attributes,
                }, set.cend)),
                _ => None,
            },
        },
    }
}

/// Parse the RDNSequence contents in order, retaining each exact RDN TLV.
pub open spec fn parse_rdns(input: Seq<u8>, pos: nat, end: nat)
    -> Option<Seq<RelativeDistinguishedName>>
    decreases end - pos
{
    if pos == end { Some(Seq::empty()) }
    else {
        match parse_rdn(input, pos, end) {
            Some((rdn, next)) if next > pos && next <= end => match parse_rdns(input, next, end) {
                Some(rest) => Some(seq![rdn] + rest),
                None => None,
            },
            _ => None,
        }
    }
}

/// Parse exactly one complete DER Name SEQUENCE.
pub open spec fn parse_name(input: Seq<u8>) -> Option<Name> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(sequence) if sequence.cstart == start && sequence.cend == end && end == input.len() =>
                match parse_rdns(input, start, end) {
                    Some(rdns) => Some(Name { der: input, rdns }),
                    None => None,
                },
            _ => None,
        },
    }
}

} // verus!
