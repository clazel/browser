//! Concrete witnesses for NameConstraints specification mutations.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An empty implicit GeneralSubtrees value violates SIZE (1..MAX).
pub proof fn lemma_empty_general_subtrees_are_rejected()
    ensures parse_name_constraints(seq![0x30u8, 0x02, 0xa0, 0x00]) is None
{
    assert(parse_name_constraints(seq![0x30u8, 0x02, 0xa0, 0x00]) is None) by (compute_only);
}

/// A GeneralSubtree carrying an encoded minimum zero violates DER DEFAULT
/// omission in this strict profile.
pub proof fn lemma_explicit_default_minimum_is_rejected()
    ensures parse_name_constraints(seq![
        0x30u8, 0x0a, 0xa0, 0x08, 0x30, 0x06, 0x82, 0x01, b'a', 0x80, 0x01, 0x00,
    ]) is None
{
    assert(parse_name_constraints(seq![
        0x30u8, 0x0a, 0xa0, 0x08, 0x30, 0x06, 0x82, 0x01, b'a', 0x80, 0x01, 0x00,
    ]) is None) by (compute_only);
}

/// A plain four-octet IP address is not the address-and-mask syntax required
/// for an IPv4 name constraint.
pub proof fn lemma_ip_constraint_requires_address_and_mask()
    ensures parse_name_constraints(seq![
        0x30u8, 0x0a, 0xa0, 0x08, 0x30, 0x06, 0x87, 0x04, 192, 0, 2, 1,
    ]) is None
{
    assert(parse_name_constraints(seq![
        0x30u8, 0x0a, 0xa0, 0x08, 0x30, 0x06, 0x87, 0x04, 192, 0, 2, 1,
    ]) is None) by (compute_only);
}

/// RFC NameConstraints fields appear in permitted-then-excluded order.
pub proof fn lemma_reversed_name_constraints_fields_are_rejected()
    ensures parse_name_constraints(seq![
        0x30u8, 0x0e,
        0xa1, 0x05, 0x30, 0x03, 0x82, 0x01, b'a',
        0xa0, 0x05, 0x30, 0x03, 0x82, 0x01, b'a',
    ]) is None
{
    assert(parse_name_constraints(seq![
        0x30u8, 0x0e,
        0xa1, 0x05, 0x30, 0x03, 0x82, 0x01, b'a',
        0xa0, 0x05, 0x30, 0x03, 0x82, 0x01, b'a',
    ]) is None) by (compute_only);
}

/// A second DER value after the outer NameConstraints SEQUENCE is rejected.
pub proof fn lemma_trailing_name_constraints_bytes_are_rejected()
    ensures parse_name_constraints(seq![0x30u8, 0x00, 0x05, 0x00]) is None
{
    assert(parse_name_constraints(seq![0x30u8, 0x00, 0x05, 0x00]) is None) by (compute_only);
}

/// CA/B BR §7.1.2.5.2's zero-length dNSName is accepted as a base, in
/// excludedSubtrees as in permittedSubtrees.
pub proof fn lemma_zero_length_dns_base_is_accepted()
    ensures
        match parse_name_constraints(seq![0x30u8, 0x06, 0xa1, 0x04, 0x30, 0x02, 0x82, 0x00]) {
            Some(value) => match value.excluded_subtrees {
                Some(items) => items.len() == 1 && match items[0].base {
                    GeneralNameConstraint::DnsName(base) => base.len() == 0,
                    _ => false,
                },
                None => false,
            },
            None => false,
        },
        parse_name_constraints(seq![0x30u8, 0x06, 0xa0, 0x04, 0x30, 0x02, 0x82, 0x00]) is Some,
{
    assert(match parse_name_constraints(seq![0x30u8, 0x06, 0xa1, 0x04, 0x30, 0x02, 0x82, 0x00]) {
        Some(value) => match value.excluded_subtrees {
            Some(items) => items.len() == 1 && match items[0].base {
                GeneralNameConstraint::DnsName(base) => base.len() == 0,
                _ => false,
            },
            None => false,
        },
        None => false,
    }) by (compute_only);
    assert(parse_name_constraints(seq![0x30u8, 0x06, 0xa0, 0x04, 0x30, 0x02, 0x82, 0x00]) is Some) by (compute_only);
}

/// An rfc822Name base `[1] "a"` is decoded as an rfc822Name, not kept
/// uninterpreted.
pub proof fn lemma_rfc822_base_is_decoded()
    ensures
        match parse_name_constraints(seq![0x30u8, 0x07, 0xa0, 0x05, 0x30, 0x03, 0x81, 0x01, b'a']) {
            Some(value) => match value.permitted_subtrees {
                Some(items) => items.len() == 1 && items[0].base is Rfc822Name,
                None => false,
            },
            None => false,
        },
{
    assert(match parse_name_constraints(seq![0x30u8, 0x07, 0xa0, 0x05, 0x30, 0x03, 0x81, 0x01, b'a']) {
        Some(value) => match value.permitted_subtrees {
            Some(items) => items.len() == 1 && items[0].base is Rfc822Name,
            None => false,
        },
        None => false,
    }) by (compute_only);
}

/// A directoryName base `[4] { 30 00 }` keeps the contents of the explicit
/// tag, the Name TLV `30 00`, not the `[4]` TLV around it.
pub proof fn lemma_directory_name_base_keeps_name_tlv()
    ensures
        match parse_name_constraints(seq![0x30u8, 0x08, 0xa0, 0x06, 0x30, 0x04, 0xa4, 0x02, 0x30, 0x00]) {
            Some(value) => match value.permitted_subtrees {
                Some(items) => items.len() == 1 && match items[0].base {
                    GeneralNameConstraint::DirectoryName(name) => name.len() == 2,
                    _ => false,
                },
                None => false,
            },
            None => false,
        },
{
    assert(match parse_name_constraints(seq![0x30u8, 0x08, 0xa0, 0x06, 0x30, 0x04, 0xa4, 0x02, 0x30, 0x00]) {
        Some(value) => match value.permitted_subtrees {
            Some(items) => items.len() == 1 && match items[0].base {
                GeneralNameConstraint::DirectoryName(name) => name.len() == 2,
                _ => false,
            },
            None => false,
        },
        None => false,
    }) by (compute_only);
}

}
