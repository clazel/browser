//! The contract the executable replacement decoder must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode(&[u8]) -> Vec<u32>`: "process a queue" with a new
/// replacement decoder in "replacement" mode.
pub open spec fn decode_ensures(input: Seq<u8>, output: Seq<u32>) -> bool {
    output == decode(input)
}

} // verus!
