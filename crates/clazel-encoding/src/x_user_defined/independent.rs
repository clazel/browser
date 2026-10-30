//! A second, independent transcription of the x-user-defined decoder
//! (Encoding §14.5), proven equal to [`super::spec`].
//!
//! The only text is the Encoding Standard's, so this is a same-text
//! transcription. Its reading of §14.5 ("While technically this is a
//! single-byte encoding, it is defined separately as it can be implemented
//! algorithmically"): one code point per byte, the byte itself below 0x80
//! and U+F780 to U+F7FF (Private Use) for 0x80 to 0xFF, in order.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The code point byte `b` decodes to.
pub open spec fn decode_one(b: u8) -> u32 {
    if b < 0x80 {
        b as u32
    } else {
        (0xF700 + b) as u32
    }
}

/// One code point per byte.
pub open spec fn decode_map(input: Seq<u8>) -> Seq<u32> {
    Seq::new(input.len(), |k: int| decode_one(input[k]))
}

proof fn lemma_queue(input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(input, i) == decode_map(input).subrange(i as int, input.len() as int),
    decreases input.len() - i,
{
    let m = decode_map(input);
    if i < input.len() {
        lemma_queue(input, i + 1);
        assert(m.subrange(i as int, input.len() as int) =~= seq![m[i as int]] + m.subrange(
            (i + 1) as int,
            input.len() as int,
        ));
    } else {
        assert(m.subrange(i as int, input.len() as int) =~= seq![]);
    }
}

/// The spec's decoder is the byte-by-byte map.
pub proof fn lemma_equals_decode(input: Seq<u8>)
    ensures
        decode(input) == decode_map(input),
{
    lemma_queue(input, 0);
    assert(decode_map(input).subrange(0, input.len() as int) =~= decode_map(input));
}

/// x-user-defined decodes to scalar values only (ASCII, or U+F780 to
/// U+F7FF).
pub proof fn lemma_decode_scalar(input: Seq<u8>)
    ensures
        crate::utf8::spec::all_scalar_values(decode(input)),
{
    lemma_equals_decode(input);
}

} // verus!
