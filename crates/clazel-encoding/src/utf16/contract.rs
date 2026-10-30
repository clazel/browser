//! Contracts the executable UTF-16BE/LE decoder must be proven to meet, in
//! terms of [`super::spec`]. Every code point it returns is a scalar value
//! (`lemmas::lemma_decode_scalar`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode(bool, &[u8]) -> Vec<u32>`: "process a queue" with
/// UTF-16BE's (`true`) or UTF-16LE's decoder in "replacement" mode.
pub open spec fn decode_ensures(is_utf16be: bool, input: Seq<u8>, output: Seq<u32>) -> bool {
    output == decode(is_utf16be, input)
}

/// Contract for `decode_or_fail(bool, &[u8]) -> Option<Vec<u32>>`: the same
/// in "fatal" mode, `None` exactly when it returns error.
pub open spec fn decode_or_fail_ensures(is_utf16be: bool, input: Seq<u8>, output: Option<Seq<u32>>) -> bool {
    output == decode_or_fail(is_utf16be, input)
}

} // verus!
