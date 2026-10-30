//! Executable-style specification of the replacement encoding's decoder
//! (Encoding §14.1), transcribed from the standard, and "process a queue"
//! (§4.1) running it.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - An I/O queue of bytes is `input: Seq<u8>` plus a read position, with
//!   end-of-queue at `input.len()`, and the output a `Seq<u32>`, as in
//!   `utf8::spec`. The decoder never restores, so the position advances by
//!   one after every byte.
//! - Only "replacement" mode is modelled: it is the mode of the "decode"
//!   hook (§6), the decoder's only use here (`TextDecoder` rejects the
//!   encoding, §7.2).
//! - Items and handler results are those of `utf8::spec`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The replacement decoder's handler (§14.1.1,
/// <https://encoding.spec.whatwg.org/#replacement-decoder>), given its
/// "replacement error returned" flag and `byte`. Returns the new flag and
/// the result.
pub open spec fn handler(replacement_error_returned: bool, byte: crate::utf8::spec::Item) -> (bool, crate::utf8::spec::HandlerResult) {
    match byte {
        // 1. "If byte is end-of-queue, then return finished."
        crate::utf8::spec::Item::EndOfQueue => (replacement_error_returned, crate::utf8::spec::HandlerResult::Finished),
        crate::utf8::spec::Item::Byte(_) => {
            if !replacement_error_returned {
                // 2. "If replacement error returned is false, then set
                //    replacement error returned to true and return error."
                (true, crate::utf8::spec::HandlerResult::Error)
            } else {
                // 3. "Return finished."
                (replacement_error_returned, crate::utf8::spec::HandlerResult::Finished)
            }
        },
    }
}

/// "Process a queue" (§4.1) in "replacement" mode, with "process an item"
/// inlined, for the replacement decoder with flag `flag` reading `input`
/// from position `i`.
pub open spec fn process_queue(flag: bool, input: Seq<u8>, i: nat) -> Seq<u32>
    decreases input.len() - i,
    when i <= input.len()
{
    let (flag, result) = handler(flag, crate::utf8::spec::item_at(input, i));
    match result {
        // process an item, 7, "replacement": "Push U+FFFD (�) to output."
        // (An error is only returned for a byte, so i < input.len().)
        crate::utf8::spec::HandlerResult::Error => seq![0xFFFDu32] + process_queue(flag, input, i + 1),
        // 6: a code point (never returned) is pushed.
        crate::utf8::spec::HandlerResult::CodePoint(c) => seq![c] + process_queue(flag, input, i + 1),
        // continue (never returned).
        crate::utf8::spec::HandlerResult::Continue => process_queue(flag, input, i + 1),
        // 5: finished.
        crate::utf8::spec::HandlerResult::Finished => seq![],
    }
}

/// "Process a queue" with a new replacement decoder ("replacement error
/// returned ... initially false") over all of `input`.
pub open spec fn decode(input: Seq<u8>) -> Seq<u32> {
    process_queue(false, input, 0)
}

} // verus!
