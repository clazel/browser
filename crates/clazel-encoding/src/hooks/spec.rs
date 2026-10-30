//! Executable-style specification of two of the Encoding Standard's hooks
//! for standards (§6): "BOM sniff" and "decode", transcribed from the
//! standard.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - An I/O queue of bytes is `input: Seq<u8>`, whole; "read n bytes" is
//!   dropping the first n.
//! - "Peeking 3 bytes" gives the first three bytes, or all of `input` when
//!   it is shorter (§3 "peek": "If ioQueue[n] is end-of-queue, break"),
//!   with the off-by-one erratum of `utf8::spec::starts_with_bom` (ERRATA.md,
//!   "Encoding §3 peek") read as its evident intent.
//! - "An instance of encoding's decoder" exists here for the encodings
//!   whose decoders this crate ships ([`has_decoder`]): UTF-8, the
//!   single-byte encodings, replacement, UTF-16BE, UTF-16LE and
//!   x-user-defined. For the others (the multi-byte encodings of Phase 4
//!   item 4.4) [`decode`] is `None`: this crate does not claim a result
//!   for them, and its caller shows that the encoding is unsupported
//!   (Phase 4 item 4.0(b)).
//! - The output is a `Seq<u32>` of code points.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Byte sequence `s` starts with `prefix`" (Infra §4.4: `prefix` is a
/// prefix of `s`).
pub open spec fn starts_with(s: Seq<u8>, prefix: Seq<u8>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}

/// "BOM sniff" (§6, <https://encoding.spec.whatwg.org/#bom-sniff>) `input`.
/// `None` is null.
pub open spec fn bom_sniff(input: Seq<u8>) -> Option<crate::labels::spec::Encoding> {
    // 1. "Let BOM be the result of peeking 3 bytes from ioQueue, converted
    //    to a byte sequence."
    let bom = input.subrange(0, if input.len() < 3 { input.len() as int } else { 3 });
    // 2. "For each of the rows in the table below, starting with the first
    //    one and going down, if BOM starts with the bytes given in the first
    //    column, then return the encoding given in the cell in the second
    //    column of that row. Otherwise, return null."
    if starts_with(bom, seq![0xEFu8, 0xBBu8, 0xBFu8]) {
        Some(crate::labels::spec::Encoding::Utf8)
    } else if starts_with(bom, seq![0xFEu8, 0xFFu8]) {
        Some(crate::labels::spec::Encoding::Utf16Be)
    } else if starts_with(bom, seq![0xFFu8, 0xFEu8]) {
        Some(crate::labels::spec::Encoding::Utf16Le)
    } else {
        None
    }
}

/// The encodings whose decoders this crate ships.
pub open spec fn has_decoder(e: crate::labels::spec::Encoding) -> bool {
    e == crate::labels::spec::Encoding::Utf8 || crate::single_byte::spec::is_single_byte(e) || e == crate::labels::spec::Encoding::Replacement || e
        == crate::labels::spec::Encoding::Utf16Be || e == crate::labels::spec::Encoding::Utf16Le || e == crate::labels::spec::Encoding::XUserDefined
}

/// "Process a queue with an instance of encoding's decoder, ioQueue,
/// output, and "replacement"" (§6 decode, step 3), for an encoding with a
/// decoder here.
pub open spec fn run_decoder(e: crate::labels::spec::Encoding, input: Seq<u8>) -> Seq<u32> {
    if e == crate::labels::spec::Encoding::Utf8 {
        crate::utf8::spec::utf8_decode_without_bom(input)
    } else if e == crate::labels::spec::Encoding::Replacement {
        crate::replacement::spec::decode(input)
    } else if e == crate::labels::spec::Encoding::Utf16Be {
        crate::utf16::spec::decode(true, input)
    } else if e == crate::labels::spec::Encoding::Utf16Le {
        crate::utf16::spec::decode(false, input)
    } else if e == crate::labels::spec::Encoding::XUserDefined {
        crate::x_user_defined::spec::decode(input)
    } else {
        crate::single_byte::spec::decode(e, input)
    }
}

/// "Decode" (§6, <https://encoding.spec.whatwg.org/#decode>) `input` given
/// the fallback encoding `encoding`. `None`: the encoding it would use has
/// no decoder in this crate (see the modelling choices).
pub open spec fn decode(input: Seq<u8>, encoding: crate::labels::spec::Encoding) -> Option<Seq<u32>> {
    // 1. "Let BOMEncoding be the result of BOM sniffing ioQueue."
    let bom_encoding = bom_sniff(input);
    let (encoding, input) = match bom_encoding {
        // 2. "If BOMEncoding is non-null:" 2.1 "Set encoding to BOMEncoding."
        //    2.2 "Read three bytes from ioQueue, if BOMEncoding is UTF-8;
        //    otherwise read two bytes."
        Some(bom) => (bom, input.subrange(if bom == crate::labels::spec::Encoding::Utf8 { 3 } else { 2 }, input.len() as int)),
        None => (encoding, input),
    };
    if has_decoder(encoding) {
        // 3. "Process a queue with an instance of encoding's decoder,
        //    ioQueue, output, and "replacement"." 4. "Return output."
        Some(run_decoder(encoding, input))
    } else {
        None
    }
}

} // verus!
