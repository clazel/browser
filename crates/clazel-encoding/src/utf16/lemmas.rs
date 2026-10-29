//! Facts proven about the UTF-16 spec. They are evidence that the
//! transcription is right, not part of what the implementation must meet:
//!
//! - [`lemma_decode_scalar`]: the UTF-16 decoder emits only scalar values
//!   (unpaired surrogates become errors, as §4.1 process an item step 6.1
//!   asserts of every decoder);
//! - [`lemma_replacement_total`]: in "replacement" mode it never fails.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A state every input reaches: a held leading surrogate is one.
pub open spec fn wf(d: Utf16Decoder) -> bool {
    match d.leading_surrogate {
        Some(s) => is_leading_surrogate(s),
        None => true,
    }
}

proof fn lemma_code_unit_bound(a: u8, b: u8)
    ensures
        (((a as u32) << 8u32) + b as u32) as u32 <= 0xFFFF,
{
    let x = a as u32;
    let y = b as u32;
    assert(x < 256 && y < 256 ==> ((x << 8u32) + y) as u32 <= 0xFFFF) by (bit_vector);
}

proof fn lemma_surrogates_scalar(leading: u32, trailing: u32)
    requires
        is_leading_surrogate(leading),
        is_trailing_surrogate(trailing),
    ensures
        0x10000 <= scalar_value_from_surrogates(leading, trailing) <= 0x10FFFF,
{
    let h = (leading - 0xD800) as u32;
    let l = (trailing - 0xDC00) as u32;
    assert(h <= 0x3FF && l <= 0x3FF ==> 0x10000 + (h << 10u32) + l <= 0x10FFFF) by (bit_vector);
}

/// One handler step keeps [`wf`] and returns only scalar values.
pub proof fn lemma_handler_scalar(d: Utf16Decoder, item: crate::utf8::spec::Item)
    requires
        wf(d),
    ensures
        wf(handler(d, item).decoder),
        match handler(d, item).result {
            crate::utf8::spec::HandlerResult::CodePoint(c) => crate::utf8::spec::is_scalar_value(c),
            _ => true,
        },
{
    if let crate::utf8::spec::Item::Byte(byte) = item {
        if let Some(lb) = d.leading_byte {
            lemma_code_unit_bound(lb, byte);
            lemma_code_unit_bound(byte, lb);
            if let Some(ls) = d.leading_surrogate {
                let cu: u32 = if d.is_utf16be {
                    (((lb as u32) << 8u32) + byte as u32) as u32
                } else {
                    (((byte as u32) << 8u32) + lb as u32) as u32
                };
                if is_trailing_surrogate(cu) {
                    lemma_surrogates_scalar(ls, cu);
                }
            }
        }
    }
}

/// In "replacement" mode the decoder never fails.
pub proof fn lemma_replacement_total(d: Utf16Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(crate::utf8::spec::ErrorMode::Replacement, d, input, i) is Some,
    decreases measure(d, input, i),
{
    let s = handler(d, crate::utf8::spec::item_at(input, i));
    if !(s.result is Finished) {
        lemma_replacement_total(s.decoder, input, next_position(input, i, s));
    }
}

/// The UTF-16 decoder emits only scalar values, in either mode.
pub proof fn lemma_decode_scalar(mode: crate::utf8::spec::ErrorMode, d: Utf16Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
        wf(d),
    ensures
        match process_queue(mode, d, input, i) {
            Some(out) => crate::utf8::spec::all_scalar_values(out),
            None => true,
        },
    decreases measure(d, input, i),
{
    let s = handler(d, crate::utf8::spec::item_at(input, i));
    lemma_handler_scalar(d, crate::utf8::spec::item_at(input, i));
    if !(s.result is Finished) {
        lemma_decode_scalar(mode, s.decoder, input, next_position(input, i, s));
    }
}

/// [`decode`] emits only scalar values.
pub proof fn lemma_decode_is_scalar(is_utf16be: bool, input: Seq<u8>)
    ensures
        crate::utf8::spec::all_scalar_values(decode(is_utf16be, input)),
{
    lemma_replacement_total(initial_decoder(is_utf16be), input, 0);
    lemma_decode_scalar(crate::utf8::spec::ErrorMode::Replacement, initial_decoder(is_utf16be), input, 0);
}

} // verus!
