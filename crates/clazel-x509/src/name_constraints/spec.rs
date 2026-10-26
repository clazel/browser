//! RFC 5280 §4.2.1.10 NameConstraints syntax.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.10>
//! DER implicit tagging and DEFAULT omission: ITU-T X.690 (02/2021),
//! §§8.14.4 and 11.5. <https://www.itu.int/rec/T-REC-X.690-202102-I/en>
//!
//! Modelling choices and limits:
//! - The input is the complete DER value inside the nameConstraints
//!   extension's OCTET STRING. This module does not inspect outer criticality.
//! - `GeneralSubtrees` must contain at least one `GeneralSubtree`; permitted
//!   `[0]` must precede excluded `[1]`, and both optional fields may be absent
//!   because both are OPTIONAL in the RFC ASN.1 declaration.
//! - This profile accepts only the DER DEFAULT form for `minimum` (omitted,
//!   interpreted as zero) and requires `maximum` absent. Any encoded distance
//!   field is outside this decoder's profile and is rejected.
//! - dNSName constraints preserve nonempty IA5 bytes; leading-dot and DNS
//!   matching semantics are not interpreted here.
//! - iPAddress constraints split 8/32 octets into 4/16 address and mask bytes.
//!   Network matching and mask semantics are out of scope.
//! - Other context-specific GeneralName choices with the RFC-required
//!   primitive/constructed form are preserved as complete TLVs and marked
//!   `Unsupported`. A caller processing a critical NameConstraints extension
//!   must reject or fully implement those forms; this parser does not silently
//!   treat them as effective constraints.
//! - This is syntax and typed extraction only, not path validation, trust,
//!   name-constraint matching, or critical-extension processing.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A GeneralName subtree base accepted or explicitly preserved by the parser.
pub enum GeneralNameConstraint {
    /// RFC 5280 dNSName constraint IA5 bytes.
    DnsName(Seq<u8>),
    /// RFC 5280 iPAddress constraint, split into address and network mask.
    IpAddress {
        /// Address octets (4 or 16 bytes).
        address: Seq<u8>,
        /// Network mask octets, matching the address width.
        mask: Seq<u8>,
    },
    /// A syntactically framed but unsupported GeneralName alternative.
    Unsupported {
        /// Context-specific GeneralName tag number.
        tag: u32,
        /// Complete DER TLV retained for a later processor.
        der: Seq<u8>,
    },
}

/// One GeneralSubtree, with `minimum` modeled as its omitted DEFAULT zero and
/// `maximum` constrained absent by this decoder profile.
pub struct GeneralSubtree {
    /// The base GeneralName choice.
    pub base: GeneralNameConstraint,
}

/// Parsed NameConstraints with order and optional-field presence preserved.
pub struct NameConstraints {
    /// Permitted subtrees, if the `[0]` field was present.
    pub permitted_subtrees: Option<Seq<GeneralSubtree>>,
    /// Excluded subtrees, if the `[1]` field was present.
    pub excluded_subtrees: Option<Seq<GeneralSubtree>>,
}

/// `true` when `base` is an alternative this syntax-only profile does not
/// apply. A caller handling a critical extension must not ignore it.
pub open spec fn base_is_unsupported(base: GeneralNameConstraint) -> bool {
    match base {
        GeneralNameConstraint::Unsupported { .. } => true,
        _ => false,
    }
}

/// Whether any subtree in `items` has a preserved unsupported base.
pub open spec fn has_unsupported_from(items: Seq<GeneralSubtree>, i: int) -> bool
    recommends 0 <= i <= items.len()
    decreases items.len() as int - i
{
    i < items.len() && (base_is_unsupported(items[i].base) || has_unsupported_from(items, i + 1))
}

/// Explicit support indicator for an outer criticality policy.
pub open spec fn all_bases_supported(value: NameConstraints) -> bool {
    match value.permitted_subtrees {
        Some(items) if has_unsupported_from(items, 0) => false,
        _ => match value.excluded_subtrees {
            Some(items) => !has_unsupported_from(items, 0),
            None => true,
        },
    }
}

/// id-ce-nameConstraints `{ 2 5 29 30 }`.
pub open spec fn name_constraints_oid() -> Seq<nat> { seq![2nat, 5, 29, 30] }

/// Parse an RFC 5280 GeneralName choice, retaining unsupported choices whole.
pub open spec fn parse_base(input: Seq<u8>, pos: nat, end: nat) -> Option<(GeneralNameConstraint, nat)> {
    match clazel_der::spec::read_tlv(input, pos, end) {
        None => None,
        Some(tlv) if tlv.tag.class == clazel_der::spec::Class::ContextSpecific
            && tlv.tag.number <= 8
            && tlv.tag.constructed == crate::extensions::spec::general_name_constructed(tlv.tag.number) =>
        {
            let value = input.subrange(tlv.cstart as int, tlv.cend as int);
            if tlv.tag.number == 2 {
                if value.len() > 0 && crate::extensions::spec::ia5_bytes(value, 0) {
                    Some((GeneralNameConstraint::DnsName(value), tlv.cend))
                } else { None }
            } else if tlv.tag.number == 7 {
                if value.len() == 8 {
                    Some((GeneralNameConstraint::IpAddress {
                        address: value.subrange(0, 4), mask: value.subrange(4, 8),
                    }, tlv.cend))
                } else if value.len() == 32 {
                    Some((GeneralNameConstraint::IpAddress {
                        address: value.subrange(0, 16), mask: value.subrange(16, 32),
                    }, tlv.cend))
                } else { None }
            } else {
                Some((GeneralNameConstraint::Unsupported {
                    tag: tlv.tag.number, der: input.subrange(pos as int, tlv.cend as int),
                }, tlv.cend))
            }
        },
        _ => None,
    }
}

/// Parse a GeneralSubtree. This profile's DEFAULT minimum is omitted and
/// maximum is absent, so the base TLV must consume the SEQUENCE contents.
pub open spec fn parse_general_subtree(input: Seq<u8>, pos: nat, end: nat)
    -> Option<(GeneralSubtree, nat)>
{
    match clazel_der::spec::expect_sequence(input, pos, end) {
        None => None,
        Some((start, finish)) => match clazel_der::spec::read_tlv(input, pos, end) {
            Some(outer) if outer.cstart == start && outer.cend == finish =>
                match parse_base(input, start, finish) {
                    Some((base, next)) if next == finish =>
                        Some((GeneralSubtree { base }, outer.cend)),
                    _ => None,
                },
            _ => None,
        },
    }
}

/// Decode a nonempty implicit GeneralSubtrees [0]/[1] content list.
pub open spec fn parse_subtrees_acc(input: Seq<u8>, pos: nat, end: nat, acc: Seq<GeneralSubtree>)
    -> Option<(Seq<GeneralSubtree>, nat)>
    recommends pos <= end && end <= input.len()
    decreases end - pos
{
    if pos == end {
        if acc.len() > 0 { Some((acc, end)) } else { None }
    } else {
        match parse_general_subtree(input, pos, end) {
            Some((subtree, next)) if next > pos && next <= end =>
                parse_subtrees_acc(input, next, end, acc.push(subtree)),
            _ => None,
        }
    }
}

/// Parse a permitted/excluded implicit constructed field.
pub open spec fn parse_subtrees_field(input: Seq<u8>, pos: nat, end: nat, number: u32)
    -> Option<(Seq<GeneralSubtree>, nat)>
{
    match clazel_der::spec::read_tlv(input, pos, end) {
        Some(field) if field.tag == clazel_der::spec::context_specific(number, true) =>
            match parse_subtrees_acc(input, field.cstart, field.cend, seq![]) {
                Some((subtrees, next)) if next == field.cend => Some((subtrees, field.cend)),
                _ => None,
            },
        _ => None,
    }
}

/// Parse ordered optional fields after the outer NameConstraints SEQUENCE.
pub open spec fn parse_name_constraints_fields(input: Seq<u8>, pos: nat, end: nat)
    -> Option<NameConstraints>
    recommends pos <= end && end <= input.len()
{
    if pos == end {
        Some(NameConstraints { permitted_subtrees: None, excluded_subtrees: None })
    } else {
        match clazel_der::spec::read_tlv(input, pos, end) {
            Some(field) if field.tag == clazel_der::spec::context_specific(0, true) =>
                match parse_subtrees_field(input, pos, end, 0) {
                    Some((permitted, next)) =>
                        if next == end { Some(NameConstraints { permitted_subtrees: Some(permitted), excluded_subtrees: None }) }
                        else { match parse_subtrees_field(input, next, end, 1) {
                            Some((excluded, final_pos)) if final_pos == end => Some(NameConstraints {
                                permitted_subtrees: Some(permitted), excluded_subtrees: Some(excluded),
                            }),
                            _ => None,
                        } },
                    _ => None,
                },
            Some(field) if field.tag == clazel_der::spec::context_specific(1, true) =>
                match parse_subtrees_field(input, pos, end, 1) {
                    Some((excluded, next)) if next == end => Some(NameConstraints {
                        permitted_subtrees: None, excluded_subtrees: Some(excluded),
                    }),
                    _ => None,
                },
            _ => None,
        }
    }
}

/// Parse the complete DER NameConstraints value with exact outer consumption.
pub open spec fn parse_name_constraints(input: Seq<u8>) -> Option<NameConstraints> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == start && outer.cend == end && end == input.len() =>
                parse_name_constraints_fields(input, start, end),
            _ => None,
        },
    }
}

}
