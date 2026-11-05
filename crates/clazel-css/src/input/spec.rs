//! Executable-style specification of a style sheet's input byte stream, transcribed from
//! CSS Syntax Module Level 3 §3.2. Nothing here runs; it defines what "correct" means.
//!
//! Source: CSS Syntax Module Level 3, Editor's Draft, `css-syntax-3/Overview.bs` of
//! `w3c/csswg-drafts` at commit `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`
//! (2026-10-20), <https://drafts.csswg.org/css-syntax-3/#input-byte-stream>, the commit
//! [`crate::tokenizer::spec`] pins.
//!
//! Modelling choices (each one a deliberate difference in form, never in meaning):
//! - A style sheet's "stream of bytes" is `stylesheet: Seq<u8>`, whole.
//! - What the text reads from around the style sheet is passed in: `protocol_label` is
//!   the "encoding label" from "HTTP or equivalent protocol", as a string, and
//!   `environment_encoding` is the "environment encoding" the referring document gives.
//!   `None` is that none is provided. A label is a `Seq<u32>`, as "get an encoding" takes.
//! - The pattern `40 63 68 61 72 73 65 74 20 22 XX* 22 3B` is [`declared_label`], which
//!   gives the `XX` bytes. An `XX` byte is never 22, so the first 22 after the opening
//!   one ends them and there is only one way to match: reading as many as there are is
//!   the same as the pattern.
//! - "If the first 1024 bytes of the stream begin with" is matching in
//!   [`first_1024_bytes`], so all of the pattern has to fall within those bytes.
//! - "A string formed out of the sequence of `XX` bytes, interpreted as `ASCII`" is
//!   [`ascii_string`]: every `XX` byte is at most 7F, so each is the code point of its
//!   value.
//! - The "Otherwise"s of steps 2 and 3 read as "if the step before returned nothing".
//!   Step 2 can match the pattern and get failure, and then step 3 is next, as for no
//!   match at all.
//! - [`decode_bytes`] is `None` when [`clazel_encoding::hooks::spec::decode`] is: that
//!   crate has no decoder yet for the encoding the bytes need, and says so rather than
//!   guess (see its modelling choices). The text has no such case.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `40 63 68 61 72 73 65 74 20 22`, which is `@charset "` in ASCII.
pub open spec fn charset_prefix() -> Seq<u8> {
    seq![0x40u8, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x20, 0x22]
}

/// "the first 1024 bytes of the stream", or all of it if it is shorter.
pub open spec fn first_1024_bytes(stylesheet: Seq<u8>) -> Seq<u8> {
    if stylesheet.len() <= 1024 {
        stylesheet
    } else {
        stylesheet.subrange(0, 1024)
    }
}

/// "each `XX` byte is a value between 0₁₆ and 21₁₆ inclusive or a value between 23₁₆ and
/// 7F₁₆ inclusive".
pub open spec fn is_xx_byte(b: u8) -> bool {
    b <= 0x21 || 0x23 <= b <= 0x7F
}

/// The position after the `XX` bytes at `pos`.
pub open spec fn skip_xx_bytes(bytes: Seq<u8>, pos: int) -> int
    decreases bytes.len() - pos,
{
    if 0 <= pos < bytes.len() && is_xx_byte(bytes[pos]) {
        skip_xx_bytes(bytes, pos + 1)
    } else {
        pos
    }
}

/// The `XX` bytes, if `bytes` begin with "the hex sequence".
pub open spec fn declared_label(bytes: Seq<u8>) -> Option<Seq<u8>> {
    if clazel_encoding::hooks::spec::starts_with(bytes, charset_prefix()) {
        let start = charset_prefix().len() as int;
        let end = skip_xx_bytes(bytes, start);
        // `22 3B`
        if end + 2 <= bytes.len() && bytes[end] == 0x22 && bytes[end + 1] == 0x3B {
            Some(bytes.subrange(start, end))
        } else {
            None
        }
    } else {
        None
    }
}

/// "a string formed out of the sequence of `XX` bytes, interpreted as `ASCII`".
pub open spec fn ascii_string(bytes: Seq<u8>) -> Seq<u32> {
    bytes.map_values(|b: u8| b as u32)
}

/// §3.2 <https://drafts.csswg.org/css-syntax-3/#determine-the-fallback-encoding>.
pub open spec fn determine_the_fallback_encoding(
    stylesheet: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment_encoding: Option<clazel_encoding::labels::spec::Encoding>,
) -> clazel_encoding::labels::spec::Encoding {
    // 1. "If HTTP or equivalent protocol provides an encoding label … get an encoding from
    // encoding label. If that does not return failure, return it."
    let from_protocol = match protocol_label {
        Some(label) => clazel_encoding::labels::spec::get_an_encoding(label),
        None => None,
    };
    // 2. "Otherwise, check stylesheet's byte stream. If the first 1024 bytes of the stream
    // begin with the hex sequence … then get an encoding from a string formed out of the
    // sequence of XX bytes, interpreted as ASCII."
    let from_declaration = match declared_label(first_1024_bytes(stylesheet)) {
        Some(label) => clazel_encoding::labels::spec::get_an_encoding(ascii_string(label)),
        None => None,
    };
    match from_protocol {
        Some(encoding) => encoding,
        None => match from_declaration {
            // "If the return value was utf-16be or utf-16le, return utf-8; if it was
            // anything else except failure, return it."
            Some(encoding) => if encoding == clazel_encoding::labels::spec::Encoding::Utf16Be
                || encoding == clazel_encoding::labels::spec::Encoding::Utf16Le {
                clazel_encoding::labels::spec::Encoding::Utf8
            } else {
                encoding
            },
            None => match environment_encoding {
                // 3. "Otherwise, if an environment encoding is provided by the referring
                // document, return it."
                Some(encoding) => encoding,
                // 4. "Otherwise, return utf-8."
                None => clazel_encoding::labels::spec::Encoding::Utf8,
            },
        },
    }
}

/// §3.2 "decode" a stylesheet's stream of bytes,
/// <https://drafts.csswg.org/css-syntax-3/#decode-bytes>.
pub open spec fn decode_bytes(
    stylesheet: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment_encoding: Option<clazel_encoding::labels::spec::Encoding>,
) -> Option<Seq<u32>> {
    // 1. "Determine the fallback encoding of stylesheet, and let fallback be the result."
    let fallback = determine_the_fallback_encoding(
        stylesheet,
        protocol_label,
        environment_encoding,
    );
    // 2. "Decode stylesheet's stream of bytes with fallback encoding fallback, and return
    // the result."
    clazel_encoding::hooks::spec::decode(stylesheet, fallback)
}

} // verus!
