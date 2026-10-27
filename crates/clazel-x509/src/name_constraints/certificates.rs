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

}
