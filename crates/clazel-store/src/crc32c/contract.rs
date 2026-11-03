//! The contract the executable CRC32C must be proven to meet. Its
//! `ensures` clause is exactly this predicate, so reviewing it (and
//! [`super::spec`]) is enough to know what the implementation guarantees.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `crc32c(&[u8]) -> [u8; 4]`: the four digest octets of
/// RFC 7143 §13.1 for every input.
pub open spec fn crc32c_ensures(data: Seq<u8>, output: Seq<u8>) -> bool {
    output == crc32c(data)
}

} // verus!
