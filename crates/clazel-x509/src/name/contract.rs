//! Contracts for the Name/RDN DER decoder.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The implementation accepts exactly the inputs represented by `parse_name`.
pub open spec fn parse_name_ensures(input: Seq<u8>, output: Option<Name>) -> bool {
    output == parse_name(input)
}

/// Contract for one AttributeTypeAndValue parser stage.
pub open spec fn parse_attribute_ensures(
    input: Seq<u8>, pos: nat, end: nat,
    output: Option<(AttributeTypeAndValue, nat)>,
) -> bool {
    output == parse_attribute(input, pos, end)
}

/// Contract for one RelativeDistinguishedName parser stage.
pub open spec fn parse_rdn_ensures(
    input: Seq<u8>, pos: nat, end: nat,
    output: Option<(RelativeDistinguishedName, nat)>,
) -> bool {
    output == parse_rdn(input, pos, end)
}

} // verus!
