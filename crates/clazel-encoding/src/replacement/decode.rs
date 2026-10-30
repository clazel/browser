//! The executable replacement decoder, proven to meet
//! [`super::contract`] (through [`super::independent`]'s equation).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Process a queue" with a new replacement decoder over all of `input`, in
/// "replacement" mode: one U+FFFD for a non-empty input, nothing otherwise.
pub fn decode(input: &[u8]) -> (out: Vec<u32>)
    ensures
        super::contract::decode_ensures(input@, out@),
{
    proof {
        super::independent::lemma_equals_decode(input@);
    }
    let mut out = Vec::new();
    if !input.is_empty() {
        out.push(0xFFFD);
        assert(out@ =~= seq![0xFFFDu32]);
    }
    out
}

} // verus!
