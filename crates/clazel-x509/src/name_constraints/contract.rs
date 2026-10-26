//! Public refinement contract for NameConstraints DER decoding.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for parsing one complete NameConstraints extension value.
pub open spec fn parse_name_constraints_ensures(input: Seq<u8>, output: Option<NameConstraints>) -> bool {
    output == parse_name_constraints(input)
}

}
