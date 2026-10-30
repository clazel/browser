//! A second, independent transcription of the replacement decoder
//! (Encoding §14.1), proven equal to [`super::spec`].
//!
//! The only text is the Encoding Standard's, so this is a same-text
//! transcription. Its reading: the decoder returns one error for the first
//! byte and then finished, so a non-empty input decodes to one U+FFFD in
//! "replacement" mode, and the empty input to nothing (the handler sees
//! end-of-queue first). §14.1's note gives the purpose: the encoding
//! "exists to prevent certain attacks that abuse a mismatch between
//! encodings supported on the server and the client".

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One U+FFFD for a non-empty input, nothing for the empty one.
pub open spec fn one_error(input: Seq<u8>) -> Seq<u32> {
    if input.len() > 0 {
        seq![0xFFFDu32]
    } else {
        seq![]
    }
}

/// The spec's decoder gives [`one_error`].
pub proof fn lemma_equals_decode(input: Seq<u8>)
    ensures
        decode(input) == one_error(input),
{
    if input.len() > 0 {
        // The first byte is the error; the next item, byte or
        // end-of-queue, finishes.
        assert(process_queue(true, input, 1) == Seq::<u32>::empty());
        assert(seq![0xFFFDu32] + Seq::<u32>::empty() =~= seq![0xFFFDu32]);
    }
}

} // verus!
