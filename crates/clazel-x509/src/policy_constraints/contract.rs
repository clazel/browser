//! Public refinement contract for PolicyConstraints DER decoding.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for parsing one complete PolicyConstraints extension value.
pub open spec fn parse_policy_constraints_ensures(
    input: Seq<u8>, output: Option<PolicyConstraints>,
) -> bool {
    output == parse_policy_constraints(input)
}

} // verus!
