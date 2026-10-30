//! A second, independent transcription of "BOM sniff" and "decode"
//! (Encoding §6), proven equal to [`super::spec`].
//!
//! The only text is the Encoding Standard's, so this is a same-text
//! transcription. It reads the byte order mark by looking at the first
//! bytes directly (rather than through "peek" and "starts with"), and
//! "decode" as: with a byte order mark, decode what follows it with the
//! encoding it names; otherwise decode everything with the fallback.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The encoding a leading byte order mark names, if any.
pub open spec fn byte_order_mark(input: Seq<u8>) -> Option<crate::labels::spec::Encoding> {
    if input.len() >= 3 && input[0] == 0xEF && input[1] == 0xBB && input[2] == 0xBF {
        Some(crate::labels::spec::Encoding::Utf8)
    } else if input.len() >= 2 && input[0] == 0xFE && input[1] == 0xFF {
        Some(crate::labels::spec::Encoding::Utf16Be)
    } else if input.len() >= 2 && input[0] == 0xFF && input[1] == 0xFE {
        Some(crate::labels::spec::Encoding::Utf16Le)
    } else {
        None
    }
}

/// The length of a byte order mark for `e`: three bytes for UTF-8, two for
/// UTF-16.
pub open spec fn mark_len(e: crate::labels::spec::Encoding) -> int {
    match e {
        crate::labels::spec::Encoding::Utf8 => 3,
        _ => 2,
    }
}

/// "Decode": the byte order mark's encoding on the rest, or the fallback
/// on everything.
pub open spec fn decode_with_mark(input: Seq<u8>, fallback: crate::labels::spec::Encoding) -> Option<Seq<u32>> {
    let (e, rest) = match byte_order_mark(input) {
        Some(m) => (m, input.subrange(mark_len(m), input.len() as int)),
        None => (fallback, input),
    };
    if has_decoder(e) {
        Some(run_decoder(e, rest))
    } else {
        None
    }
}

/// The two readings of "BOM sniff" agree.
pub proof fn lemma_equals_bom_sniff(input: Seq<u8>)
    ensures
        byte_order_mark(input) == bom_sniff(input),
{
    let bom = input.subrange(0, if input.len() < 3 { input.len() as int } else { 3 });
    if input.len() >= 3 {
        assert(bom.subrange(0, 3) =~= seq![input[0], input[1], input[2]]);
    }
    if input.len() >= 2 {
        assert(bom.subrange(0, 2) =~= seq![input[0], input[1]]);
    }
}

/// The two readings of "decode" agree.
pub proof fn lemma_equals_decode(input: Seq<u8>, fallback: crate::labels::spec::Encoding)
    ensures
        decode_with_mark(input, fallback) == decode(input, fallback),
{
    lemma_equals_bom_sniff(input);
}

} // verus!
