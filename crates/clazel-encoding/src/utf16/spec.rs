//! Executable-style specification of UTF-16BE and UTF-16LE decoding
//! (Encoding §14.2 "Common infrastructure for UTF-16BE/LE", §14.3
//! UTF-16BE, §14.4 UTF-16LE), transcribed from the standard: the shared
//! UTF-16 decoder, and "process a queue" (§4.1) running it.
//!
//! Section numbers: the plan (Phase 4 item 4.3) cites §14.2 and §14.3 for
//! UTF-16BE and UTF-16LE; at the pinned commit "Legacy miscellaneous
//! encodings" is §14 with replacement §14.1, the shared infrastructure
//! §14.2, UTF-16BE §14.3, UTF-16LE §14.4 and x-user-defined §14.5. The
//! anchors cited below are the standard's own.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - An I/O queue of bytes is `input: Seq<u8>` plus a read position `i`,
//!   with end-of-queue at `input.len()`, as in `utf8::spec`.
//! - "Restore bytes to ioQueue" (step 6.7) is modelled by moving the read
//!   position back to `i - 1`. The restored bytes are exactly the two
//!   last read, in the order read: the code unit was made from UTF-16
//!   leading byte, the byte read at `i - 1` (step 3), and `byte`, read at
//!   `i`; for UTF-16BE `bytes` is « codeUnit >> 8, codeUnit & 0xFF » =
//!   « leading byte, byte », and for UTF-16LE « codeUnit & 0xFF,
//!   codeUnit >> 8 » = « leading byte, byte » too. So the queue after the
//!   restore is `input` from `i - 1`. `independent.rs` transcribes the
//!   restore literally, prepending the two bytes to the queue, and is
//!   proven equal on every input, which checks this argument.
//!   (`i >= 1` whenever the leading byte is set; the guard `i >= 1` below
//!   only makes the function total on states no input reaches.)
//! - "Null or a byte" and "null or a leading surrogate" are `Option`s; a
//!   leading surrogate is held as its `u32` value.
//! - The output is a `Seq<u32>` of code points; `None` is the error
//!   returned in "fatal" mode.
//! - Items, handler results and error modes are those of `utf8::spec`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The shared UTF-16 decoder's associated state (§14.2.1).
pub struct Utf16Decoder {
    /// UTF-16 leading byte: "Null or a byte, initially null."
    pub leading_byte: Option<u8>,
    /// UTF-16 leading surrogate: "Null or a leading surrogate, initially
    /// null."
    pub leading_surrogate: Option<u32>,
    /// is UTF-16BE decoder: "A boolean, initially false."
    pub is_utf16be: bool,
}

/// A new decoder: UTF-16BE's decoder "is shared UTF-16 decoder with its is
/// UTF-16BE decoder set to true" (§14.3.1); UTF-16LE's "is shared UTF-16
/// decoder" (§14.4.1).
pub open spec fn initial_decoder(is_utf16be: bool) -> Utf16Decoder {
    Utf16Decoder { leading_byte: None, leading_surrogate: None, is_utf16be }
}

/// A leading surrogate: a code point in the range U+D800 to U+DBFF,
/// inclusive (Infra §4.5).
pub open spec fn is_leading_surrogate(c: u32) -> bool {
    0xD800 <= c <= 0xDBFF
}

/// A trailing surrogate: a code point in the range U+DC00 to U+DFFF,
/// inclusive (Infra §4.5).
pub open spec fn is_trailing_surrogate(c: u32) -> bool {
    0xDC00 <= c <= 0xDFFF
}

/// "Scalar value from surrogates" (§3,
/// <https://encoding.spec.whatwg.org/#scalar-value-from-surrogates>):
/// "return 0x10000 + ((leading − 0xD800) << 10) + (trailing − 0xDC00)".
pub open spec fn scalar_value_from_surrogates(leading: u32, trailing: u32) -> u32 {
    (0x10000 + (((leading - 0xD800) as u32) << 10u32) + (trailing - 0xDC00)) as u32
}

/// One handler invocation: the new state, the result, and whether the
/// handler restored the two bytes it read.
pub struct Step {
    /// Decoder state after the handler ran.
    pub decoder: Utf16Decoder,
    /// What the handler returned.
    pub result: crate::utf8::spec::HandlerResult,
    /// True if the handler ran step 6.7's "Restore bytes to ioQueue".
    pub restored: bool,
}

/// A step that does not restore.
pub open spec fn step(decoder: Utf16Decoder, result: crate::utf8::spec::HandlerResult) -> Step {
    Step { decoder, result, restored: false }
}

/// The shared UTF-16 decoder's handler (§14.2.1,
/// <https://encoding.spec.whatwg.org/#shared-utf-16-decoder>), given
/// `byte`.
pub open spec fn handler(d: Utf16Decoder, byte: crate::utf8::spec::Item) -> Step {
    match byte {
        crate::utf8::spec::Item::EndOfQueue => {
            if d.leading_byte is Some || d.leading_surrogate is Some {
                // 1. "If byte is end-of-queue and either UTF-16 leading byte
                //    or UTF-16 leading surrogate is non-null, then set UTF-16
                //    leading byte and UTF-16 leading surrogate to null, and
                //    return error."
                step(Utf16Decoder { leading_byte: None, leading_surrogate: None, ..d }, crate::utf8::spec::HandlerResult::Error)
            } else {
                // 2. "If byte is end-of-queue and UTF-16 leading byte and
                //    UTF-16 leading surrogate are null, then return finished."
                step(d, crate::utf8::spec::HandlerResult::Finished)
            }
        },
        crate::utf8::spec::Item::Byte(byte) => match d.leading_byte {
            // 3. "If UTF-16 leading byte is null, then set UTF-16 leading
            //    byte to byte and return continue."
            None => step(Utf16Decoder { leading_byte: Some(byte), ..d }, crate::utf8::spec::HandlerResult::Continue),
            Some(leading_byte) => {
                // 4. "Let codeUnit be the result of:" is UTF-16BE decoder
                //    true: "(UTF-16 leading byte << 8) + byte"; false:
                //    "(byte << 8) + UTF-16 leading byte".
                let code_unit: u32 = if d.is_utf16be {
                    ((leading_byte as u32) << 8u32) + byte as u32
                } else {
                    ((byte as u32) << 8u32) + leading_byte as u32
                } as u32;
                // 5. "Set UTF-16 leading byte to null."
                let d = Utf16Decoder { leading_byte: None, ..d };
                match d.leading_surrogate {
                    // 6. "If UTF-16 leading surrogate is non-null:"
                    Some(leading_surrogate) => {
                        // 6.1 "Let leadingSurrogate be UTF-16 leading
                        //     surrogate." 6.2 "Set UTF-16 leading surrogate
                        //     to null."
                        let d = Utf16Decoder { leading_surrogate: None, ..d };
                        if is_trailing_surrogate(code_unit) {
                            // 6.3 "If codeUnit is a trailing surrogate, then
                            //     return a scalar value from surrogates given
                            //     leadingSurrogate and codeUnit."
                            step(d, crate::utf8::spec::HandlerResult::CodePoint(scalar_value_from_surrogates(leading_surrogate, code_unit)))
                        } else {
                            // 6.4 byte1 = codeUnit >> 8; 6.5 byte2 = codeUnit
                            // & 0x00FF; 6.6 bytes = « byte1, byte2 » or
                            // « byte2, byte1 »; 6.7 "Restore bytes to ioQueue
                            // and return error." (The bytes are the two last
                            // read; see the modelling choices.)
                            Step { decoder: d, result: crate::utf8::spec::HandlerResult::Error, restored: true }
                        }
                    },
                    None => {
                        if is_leading_surrogate(code_unit) {
                            // 7. "If codeUnit is a leading surrogate, then set
                            //    UTF-16 leading surrogate to codeUnit and return
                            //    continue."
                            step(Utf16Decoder { leading_surrogate: Some(code_unit), ..d }, crate::utf8::spec::HandlerResult::Continue)
                        } else if is_trailing_surrogate(code_unit) {
                            // 8. "If codeUnit is a trailing surrogate, then
                            //    return error."
                            step(d, crate::utf8::spec::HandlerResult::Error)
                        } else {
                            // 9. "Return code point codeUnit."
                            step(d, crate::utf8::spec::HandlerResult::CodePoint(code_unit))
                        }
                    },
                }
            },
        },
    }
}

/// Where reading continues after a step: back to the first restored byte;
/// otherwise the next byte, or the end-of-queue that read never removes.
pub open spec fn next_position(input: Seq<u8>, i: nat, s: Step) -> nat {
    if s.restored && i >= 1 {
        (i - 1) as nat
    } else if i < input.len() {
        i + 1
    } else {
        i
    }
}

/// The termination measure of [`process_queue`]: each byte read is worth
/// 4, a held leading surrogate 6 and a held leading byte 3, so every step
/// that does not finish lowers it (a restore reads one byte back but drops
/// both held values).
pub open spec fn measure(d: Utf16Decoder, input: Seq<u8>, i: nat) -> int {
    4 * (input.len() - i) + (if d.leading_surrogate is Some { 6int } else { 0 }) + (if d.leading_byte is Some {
        3int
    } else {
        0
    })
}

/// "Process a queue" (§4.1, #concept-encoding-run), with "process an item"
/// inlined, for a UTF-16 decoder in state `d` reading `input` from `i`.
/// `None` is the error returned in "fatal" mode.
pub open spec fn process_queue(mode: crate::utf8::spec::ErrorMode, d: Utf16Decoder, input: Seq<u8>, i: nat) -> Option<Seq<u32>>
    decreases measure(d, input, i),
    when i <= input.len()
{
    // 1.1 process an item, 4: run the handler on the item read.
    let s = handler(d, crate::utf8::spec::item_at(input, i));
    let j = next_position(input, i, s);
    match s.result {
        // process an item, 5: finished.
        crate::utf8::spec::HandlerResult::Finished => Some(seq![]),
        // 6: push the code point.
        crate::utf8::spec::HandlerResult::CodePoint(c) => crate::utf8::spec::cons(c, process_queue(mode, s.decoder, input, j)),
        // 7: error, switch on mode.
        crate::utf8::spec::HandlerResult::Error => match mode {
            // "replacement": "Push U+FFFD (�) to output."
            crate::utf8::spec::ErrorMode::Replacement => crate::utf8::spec::cons(0xFFFD, process_queue(mode, s.decoder, input, j)),
            // "fatal": "Return result."
            crate::utf8::spec::ErrorMode::Fatal => None,
        },
        // 1.2 "If result is not continue, then return result." Continue loops.
        crate::utf8::spec::HandlerResult::Continue => process_queue(mode, s.decoder, input, j),
    }
}

/// "Process a queue" with an instance of UTF-16BE's (`is_utf16be`) or
/// UTF-16LE's decoder over all of `input`, in "replacement" mode. The
/// result is never `None` in that mode (`lemmas::lemma_replacement_total`);
/// `seq![]` is unreachable.
pub open spec fn decode(is_utf16be: bool, input: Seq<u8>) -> Seq<u32> {
    match process_queue(crate::utf8::spec::ErrorMode::Replacement, initial_decoder(is_utf16be), input, 0) {
        Some(out) => out,
        None => seq![],
    }
}

/// The same in "fatal" mode. `None` is the error.
pub open spec fn decode_or_fail(is_utf16be: bool, input: Seq<u8>) -> Option<Seq<u32>> {
    process_queue(crate::utf8::spec::ErrorMode::Fatal, initial_decoder(is_utf16be), input, 0)
}

} // verus!
