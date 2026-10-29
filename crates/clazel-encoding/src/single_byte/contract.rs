//! Contracts the executable single-byte decoder and encoder must be proven
//! to meet, in terms of [`super::spec`]. Output is code points as `u32`, as
//! in `utf8::contract`; every one is a scalar value
//! (`lemmas::lemma_decode_scalar`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use crate::labels::spec::Encoding;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of the decoders: `e` is a single-byte encoding (§9).
pub open spec fn decode_requires(e: Encoding) -> bool {
    is_single_byte(e)
}

/// Contract for `decode(Encoding, &[u8]) -> Vec<u32>`: "process a queue"
/// with `e`'s decoder in "replacement" mode.
pub open spec fn decode_ensures(e: Encoding, input: Seq<u8>, output: Seq<u32>) -> bool {
    output == decode(e, input)
}

/// Contract for `decode_or_fail(Encoding, &[u8]) -> Option<Vec<u32>>`: the
/// same in "fatal" mode, `None` exactly when it returns error.
pub open spec fn decode_or_fail_ensures(e: Encoding, input: Seq<u8>, output: Option<Seq<u32>>) -> bool {
    output == decode_or_fail(e, input)
}

/// Precondition of `encode(Encoding, &[u32]) -> Vec<u8>`: `e` is a
/// single-byte encoding and the input is "an I/O queue of scalar values"
/// (§6 encode; §4.1 process an item, step 3, asserts no surrogate).
pub open spec fn encode_requires(e: Encoding, input: Seq<u32>) -> bool {
    is_single_byte(e) && crate::utf8::spec::all_scalar_values(input)
}

/// Contract for `encode`: equals "encode" (§6) with `e`.
pub open spec fn encode_ensures(e: Encoding, input: Seq<u32>, output: Seq<u8>) -> bool {
    output == encode(e, input)
}

} // verus!
