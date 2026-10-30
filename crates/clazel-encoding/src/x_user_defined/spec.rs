//! Executable-style specification of the x-user-defined decoder (Encoding
//! §14.5), transcribed from the standard, and "process a queue" (§4.1)
//! running it.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - An I/O queue of bytes is `input: Seq<u8>` plus a read position, with
//!   end-of-queue at `input.len()`, and the output a `Seq<u32>`, as in
//!   `utf8::spec`. The decoder has no state and never restores.
//! - The handler never returns error, so the error mode changes nothing
//!   and is not a parameter.
//! - Items and handler results are those of `utf8::spec`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The x-user-defined decoder's handler (§14.5.1,
/// <https://encoding.spec.whatwg.org/#x-user-defined-decoder>), given
/// `byte`.
pub open spec fn handler(byte: crate::utf8::spec::Item) -> crate::utf8::spec::HandlerResult {
    match byte {
        // 1. "If byte is end-of-queue, then return finished."
        crate::utf8::spec::Item::EndOfQueue => crate::utf8::spec::HandlerResult::Finished,
        crate::utf8::spec::Item::Byte(byte) => {
            if byte <= 0x7F {
                // 2. "If byte is an ASCII byte, then return a code point
                //    whose value is byte."
                crate::utf8::spec::HandlerResult::CodePoint(byte as u32)
            } else {
                // 3. "Return a code point whose value is 0xF780 + byte −
                //    0x80."
                crate::utf8::spec::HandlerResult::CodePoint((0xF780 + byte - 0x80) as u32)
            }
        },
    }
}

/// "Process a queue" (§4.1), with "process an item" inlined, for the
/// x-user-defined decoder reading `input` from position `i`.
pub open spec fn process_queue(input: Seq<u8>, i: nat) -> Seq<u32>
    decreases input.len() - i,
    when i <= input.len()
{
    match handler(crate::utf8::spec::item_at(input, i)) {
        // process an item, 6: push the code point. (Only returned for a
        // byte, so i < input.len().)
        crate::utf8::spec::HandlerResult::CodePoint(c) => seq![c] + process_queue(input, i + 1),
        // 7: error (never returned), "replacement": push U+FFFD.
        crate::utf8::spec::HandlerResult::Error => seq![0xFFFDu32] + process_queue(input, i + 1),
        // continue (never returned).
        crate::utf8::spec::HandlerResult::Continue => process_queue(input, i + 1),
        // 5: finished.
        crate::utf8::spec::HandlerResult::Finished => seq![],
    }
}

/// "Process a queue" with an instance of x-user-defined's decoder over all
/// of `input`.
pub open spec fn decode(input: Seq<u8>) -> Seq<u32> {
    process_queue(input, 0)
}

} // verus!
