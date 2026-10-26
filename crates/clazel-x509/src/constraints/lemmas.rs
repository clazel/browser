//! Concrete RFC 5280 constraint-model witnesses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// DER omits BasicConstraints cA when its DEFAULT value is FALSE.
pub proof fn lemma_reject_explicit_default_ca_false()
    ensures parse_basic_constraints(seq![0x30u8, 0x03, 0x01, 0x01, 0x00]) is None
{
    assert(parse_basic_constraints(seq![0x30u8, 0x03, 0x01, 0x01, 0x00]) is None)
        by (compute_only);
}

/// A pathLenConstraint cannot accompany cA=FALSE or omitted cA.
pub proof fn lemma_reject_path_length_without_ca()
    ensures parse_basic_constraints(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is None
{
    assert(parse_basic_constraints(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is None)
        by (compute_only);
}

/// KeyUsage's named-bit list has no bit number greater than 8.
pub proof fn lemma_reject_unknown_key_usage_bit()
    ensures parse_key_usage(seq![0x03u8, 0x03, 0x06, 0x00, 0x80]) is None
{
    assert(parse_key_usage(seq![0x03u8, 0x03, 0x06, 0x00, 0x80]) is None)
        by (compute_only);
}

/// ExtendedKeyUsage purpose OIDs are unique.
pub proof fn lemma_reject_duplicate_eku_oid()
    ensures parse_extended_key_usage(seq![
        0x30u8, 0x0c,
        0x06, 0x04, 0x55, 0x1d, 0x25, 0x00,
        0x06, 0x04, 0x55, 0x1d, 0x25, 0x00,
    ]) is None
{
    assert(parse_extended_key_usage(seq![
        0x30u8, 0x0c,
        0x06, 0x04, 0x55, 0x1d, 0x25, 0x00,
        0x06, 0x04, 0x55, 0x1d, 0x25, 0x00,
    ]) is None) by (compute_only);
}

} // verus!
