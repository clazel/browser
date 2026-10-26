//! Refinement contracts for the selected RFC 5280 extension decoders.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn parse_basic_constraints_ensures(
    input: Seq<u8>, output: Option<BasicConstraints>,
) -> bool {
    output == parse_basic_constraints(input)
}

pub open spec fn parse_key_usage_ensures(input: Seq<u8>, output: Option<KeyUsage>) -> bool {
    output == parse_key_usage(input)
}

pub open spec fn parse_extended_key_usage_ensures(
    input: Seq<u8>, output: Option<ExtendedKeyUsage>,
) -> bool {
    output == parse_extended_key_usage(input)
}

} // verus!
