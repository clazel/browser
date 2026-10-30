//! Executable-style specification of the legacy single-byte encodings
//! (Encoding §9), transcribed from the standard: index single-byte, "index
//! code point" and "index pointer" (§5), the single-byte decoder and
//! encoder, and "process a queue" (§4.1) running them.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - "Index single-byte" for an encoding is its table in the generated
//!   [`super::data`], read from the standard's own `indexes.json` (the
//!   index files of §5 in the form the standard publishes for machines;
//!   the derivation is stated in that file's header). Entry `p` is the
//!   code point for pointer `p`, or `NULL` where the index has none.
//!   ISO-8859-8-I reads ISO-8859-8's index, as §9's table says. An index
//!   has pointers 0 to 127 only, so a pointer outside that range is "not
//!   in index".
//! - A decoder's I/O queue is `input: Seq<u8>` plus a read position, with
//!   end-of-queue at `input.len()`, and its output a `Seq<u32>` of code
//!   points; `None` is the error "process a queue" returns in "fatal"
//!   mode. The single-byte decoder has no state and never restores, so
//!   the position advances by one after every byte (as in `utf8::spec`).
//! - The encoder's I/O queue is `input: Seq<u32>` of scalar values plus a
//!   read position, and its output a `Seq<u8>`. Only the "html" error mode
//!   is modelled for the encoder: it is the mode of the "encode" hook (§6),
//!   the encoder's only use in this browser (HTML forms, Phase 6).
//! - Items, handler results and error modes are those of `utf8::spec`
//!   (§3 and §4.1 define them once for every encoding).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The generated tables' entry for a pointer the index does not have.
pub open spec fn null_entry() -> u32 {
    0xFFFF_FFFFu32
}

/// "A single-byte encoding" (§9): the encodings of §9's table, numbered 1
/// to 28 in the order of §4.2 (IBM866 to x-mac-cyrillic).
pub open spec fn is_single_byte(e: crate::labels::spec::Encoding) -> bool {
    1 <= crate::labels::spec::encoding_number(e) <= 28
}

/// Index single-byte (§9): entry `pointer` of `e`'s index, as the table
/// in §9 assigns indexes to single-byte encodings.
pub open spec fn index_entry(e: crate::labels::spec::Encoding, pointer: int) -> u32 {
    match e {
        crate::labels::spec::Encoding::Ibm866 => super::data::index_ibm866_at(pointer),
        crate::labels::spec::Encoding::Iso8859_2 => super::data::index_iso_8859_2_at(pointer),
        crate::labels::spec::Encoding::Iso8859_3 => super::data::index_iso_8859_3_at(pointer),
        crate::labels::spec::Encoding::Iso8859_4 => super::data::index_iso_8859_4_at(pointer),
        crate::labels::spec::Encoding::Iso8859_5 => super::data::index_iso_8859_5_at(pointer),
        crate::labels::spec::Encoding::Iso8859_6 => super::data::index_iso_8859_6_at(pointer),
        crate::labels::spec::Encoding::Iso8859_7 => super::data::index_iso_8859_7_at(pointer),
        crate::labels::spec::Encoding::Iso8859_8 => super::data::index_iso_8859_8_at(pointer),
        // §9: "ISO-8859-8-I | index-iso-8859-8.txt"
        crate::labels::spec::Encoding::Iso8859_8I => super::data::index_iso_8859_8_at(pointer),
        crate::labels::spec::Encoding::Iso8859_10 => super::data::index_iso_8859_10_at(pointer),
        crate::labels::spec::Encoding::Iso8859_13 => super::data::index_iso_8859_13_at(pointer),
        crate::labels::spec::Encoding::Iso8859_14 => super::data::index_iso_8859_14_at(pointer),
        crate::labels::spec::Encoding::Iso8859_15 => super::data::index_iso_8859_15_at(pointer),
        crate::labels::spec::Encoding::Iso8859_16 => super::data::index_iso_8859_16_at(pointer),
        crate::labels::spec::Encoding::Koi8R => super::data::index_koi8_r_at(pointer),
        crate::labels::spec::Encoding::Koi8U => super::data::index_koi8_u_at(pointer),
        crate::labels::spec::Encoding::Macintosh => super::data::index_macintosh_at(pointer),
        crate::labels::spec::Encoding::Windows874 => super::data::index_windows_874_at(pointer),
        crate::labels::spec::Encoding::Windows1250 => super::data::index_windows_1250_at(pointer),
        crate::labels::spec::Encoding::Windows1251 => super::data::index_windows_1251_at(pointer),
        crate::labels::spec::Encoding::Windows1252 => super::data::index_windows_1252_at(pointer),
        crate::labels::spec::Encoding::Windows1253 => super::data::index_windows_1253_at(pointer),
        crate::labels::spec::Encoding::Windows1254 => super::data::index_windows_1254_at(pointer),
        crate::labels::spec::Encoding::Windows1255 => super::data::index_windows_1255_at(pointer),
        crate::labels::spec::Encoding::Windows1256 => super::data::index_windows_1256_at(pointer),
        crate::labels::spec::Encoding::Windows1257 => super::data::index_windows_1257_at(pointer),
        crate::labels::spec::Encoding::Windows1258 => super::data::index_windows_1258_at(pointer),
        crate::labels::spec::Encoding::XMacCyrillic => super::data::index_x_mac_cyrillic_at(pointer),
        // Not a single-byte encoding: no index.
        _ => null_entry(),
    }
}

/// "The index code point for pointer in index is the code point
/// corresponding to pointer in index, or null if pointer is not in index"
/// (§5, <https://encoding.spec.whatwg.org/#index-code-point>). `None` is
/// null.
pub open spec fn index_code_point(e: crate::labels::spec::Encoding, pointer: int) -> Option<u32> {
    if 0 <= pointer < 128 && index_entry(e, pointer) != null_entry() {
        Some(index_entry(e, pointer))
    } else {
        None
    }
}

/// The first pointer at or after `pointer` corresponding to `code_point`
/// in `e`'s index.
pub open spec fn index_pointer_from(e: crate::labels::spec::Encoding, code_point: u32, pointer: nat) -> Option<nat>
    decreases 128 - pointer,
{
    if pointer >= 128 {
        None
    } else if index_code_point(e, pointer as int) == Some(code_point) {
        Some(pointer)
    } else {
        index_pointer_from(e, code_point, pointer + 1)
    }
}

/// "The index pointer for codePoint in index is the first pointer
/// corresponding to codePoint in index, or null if codePoint is not in
/// index" (§5, <https://encoding.spec.whatwg.org/#index-pointer>).
pub open spec fn index_pointer(e: crate::labels::spec::Encoding, code_point: u32) -> Option<nat> {
    index_pointer_from(e, code_point, 0)
}

/// The single-byte decoder's handler (§9,
/// <https://encoding.spec.whatwg.org/#single-byte-decoder>), given `byte`.
pub open spec fn handler(e: crate::labels::spec::Encoding, byte: crate::utf8::spec::Item) -> crate::utf8::spec::HandlerResult {
    match byte {
        // 1. "If byte is end-of-queue, then return finished."
        crate::utf8::spec::Item::EndOfQueue => crate::utf8::spec::HandlerResult::Finished,
        crate::utf8::spec::Item::Byte(byte) => {
            if byte <= 0x7F {
                // 2. "If byte is an ASCII byte, then return a code point
                //    whose value is byte." (Infra: an ASCII byte is 0x00 to
                //    0x7F, inclusive.)
                crate::utf8::spec::HandlerResult::CodePoint(byte as u32)
            } else {
                // 3. "Let codePoint be the index code point for byte − 0x80
                //    in index single-byte."
                match index_code_point(e, byte - 0x80) {
                    // 4. "If codePoint is null, then return error."
                    None => crate::utf8::spec::HandlerResult::Error,
                    // 5. "Return a code point whose value is codePoint."
                    Some(code_point) => crate::utf8::spec::HandlerResult::CodePoint(code_point),
                }
            }
        },
    }
}

/// "Process a queue" (§4.1, #concept-encoding-run), with "process an item"
/// inlined, for the single-byte decoder of `e` reading `input` from
/// position `i`. `None` is the error returned in "fatal" mode.
pub open spec fn process_queue(mode: crate::utf8::spec::ErrorMode, e: crate::labels::spec::Encoding, input: Seq<u8>, i: nat) -> Option<Seq<u32>>
    decreases input.len() - i,
    when i <= input.len()
{
    // 1.1 process an item, 4: run the handler on the item read.
    match handler(e, crate::utf8::spec::item_at(input, i)) {
        // process an item, 5: finished.
        crate::utf8::spec::HandlerResult::Finished => Some(seq![]),
        // 6: push the code point. (A code point is only returned for a
        // byte, so i < input.len() here.)
        crate::utf8::spec::HandlerResult::CodePoint(c) => crate::utf8::spec::cons(c, process_queue(mode, e, input, i + 1)),
        // 7: error, switch on mode.
        crate::utf8::spec::HandlerResult::Error => match mode {
            // "replacement": "Push U+FFFD (�) to output."
            crate::utf8::spec::ErrorMode::Replacement => crate::utf8::spec::cons(0xFFFD, process_queue(mode, e, input, i + 1)),
            // "fatal": "Return result."
            crate::utf8::spec::ErrorMode::Fatal => None,
        },
        // The handler never returns continue.
        crate::utf8::spec::HandlerResult::Continue => process_queue(mode, e, input, i + 1),
    }
}

/// "Process a queue" with an instance of `e`'s decoder over all of
/// `input`, in "replacement" mode (the mode of the "decode" hook, §6). In
/// that mode the result is never `None` (`lemmas::lemma_replacement_total`);
/// `seq![]` is unreachable.
pub open spec fn decode(e: crate::labels::spec::Encoding, input: Seq<u8>) -> Seq<u32> {
    match process_queue(crate::utf8::spec::ErrorMode::Replacement, e, input, 0) {
        Some(out) => out,
        None => seq![],
    }
}

/// "Process a queue" with an instance of `e`'s decoder over all of
/// `input`, in "fatal" mode. `None` is the error.
pub open spec fn decode_or_fail(e: crate::labels::spec::Encoding, input: Seq<u8>) -> Option<Seq<u32>> {
    process_queue(crate::utf8::spec::ErrorMode::Fatal, e, input, 0)
}

/// What the single-byte encoder's handler returns (§4.1, handler):
/// finished, one byte, or an error with a code point.
pub enum EncoderResult {
    /// finished
    Finished,
    /// "a byte whose value is" the payload
    Byte(u8),
    /// "error with" the code point
    Error(u32),
}

/// The single-byte encoder's handler (§9,
/// <https://encoding.spec.whatwg.org/#single-byte-encoder>), given
/// `code_point`.
pub open spec fn encoder_handler(e: crate::labels::spec::Encoding, code_point: crate::utf8::spec::ScalarItem) -> EncoderResult {
    match code_point {
        // 1. "If codePoint is end-of-queue, then return finished."
        crate::utf8::spec::ScalarItem::EndOfQueue => EncoderResult::Finished,
        crate::utf8::spec::ScalarItem::ScalarValue(code_point) => {
            if code_point <= 0x7F {
                // 2. "If codePoint is an ASCII code point, then return a byte
                //    whose value is codePoint."
                EncoderResult::Byte(code_point as u8)
            } else {
                // 3. "Let pointer be the index pointer for codePoint in
                //    index single-byte."
                match index_pointer(e, code_point) {
                    // 4. "If pointer is null, then return error with
                    //    codePoint."
                    None => EncoderResult::Error(code_point),
                    // 5. "Return a byte whose value is pointer + 0x80."
                    Some(pointer) => EncoderResult::Byte((pointer + 0x80) as u8),
                }
            }
        },
    }
}

/// "The shortest sequence of 0x30 (0) to 0x39 (9), inclusive, representing
/// [n] in base ten" (§4.1, process an item, step 7, "html").
pub open spec fn decimal(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(0x30 + n) as u8]
    } else {
        decimal(n / 10).push((0x30 + n % 10) as u8)
    }
}

/// "Process a queue" (§4.1) with `e`'s single-byte encoder reading `input`
/// from position `i`, in "html" mode.
pub open spec fn encoder_process_queue(e: crate::labels::spec::Encoding, input: Seq<u32>, i: nat) -> Seq<u8>
    decreases input.len() - i,
    when i <= input.len()
{
    // 1.1 process an item, 4: run the handler on the item read.
    match encoder_handler(e, crate::utf8::spec::scalar_item_at(input, i)) {
        // process an item, 5: finished.
        EncoderResult::Finished => seq![],
        // 6.2: push the byte; 8: continue.
        EncoderResult::Byte(b) => seq![b] + encoder_process_queue(e, input, i + 1),
        // 7, "html": "Push 0x26 (&), 0x23 (#), followed by the shortest
        // sequence of 0x30 (0) to 0x39 (9), inclusive, representing result's
        // code point's value in base ten, followed by 0x3B (;) to output."
        // 8: continue.
        EncoderResult::Error(c) => seq![0x26u8, 0x23u8] + decimal(c as nat) + seq![0x3Bu8]
            + encoder_process_queue(e, input, i + 1),
    }
}

/// "Encode" (§6, #encode) with single-byte encoding `e`: "1. Let encoder be
/// the result of getting an encoder from encoding" (get an encoder's
/// assertion holds: `e` is neither replacement nor UTF-16BE/LE), "2.
/// Process a queue with encoder, ioQueue, output, and "html". 3. Return
/// output."
pub open spec fn encode(e: crate::labels::spec::Encoding, input: Seq<u32>) -> Seq<u8> {
    encoder_process_queue(e, input, 0)
}

} // verus!
