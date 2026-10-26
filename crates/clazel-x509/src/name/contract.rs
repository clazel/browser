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

} // verus!
