//! The input byte stream of CSS Syntax Level 3 (§3.2 "The input byte stream"),
//! transcribed from the standard alone; see the header of [`super`] for the text
//! and the modelling choices that this file shares.
//!
//! ## Modelling choices
//!
//! - The bytes are a `Seq<u8>`. The "encoding label" that "HTTP or equivalent
//!   protocol provides" is `Option<Seq<u32>>` (a string of code points, `None`
//!   for none provided). The "environment encoding" is an `Option<Encoding>`.
//! - "get an encoding" and "decode" are the Encoding Standard's algorithms; they
//!   are not part of CSS Syntax, so this file uses the specification of
//!   `clazel-encoding` for both (`labels::spec::get_an_encoding` and
//!   `hooks::spec::decode`, the latter being the Encoding Standard's "decode",
//!   which "gives precedence to a byte order mark"). Where that crate has no
//!   decoder for an encoding, "decode" has no result here either (`None`).
//! - The pattern `40 63 68 61 72 73 65 74 20 22 XX* 22 3B` is matched against the
//!   first 1024 bytes only, and all of it must lie inside them. `XX*` is the
//!   longest run of bytes that are not 22, which is what the pattern means,
//!   since 22 is not an `XX` byte.

#[cfg(verus_only)]
use super::*;

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use clazel_encoding::hooks::spec::decode;
#[cfg(verus_only)]
use clazel_encoding::labels::spec::{get_an_encoding, Encoding};

verus! {

/// An `XX` byte of the encoding declaration: "a value between 0 and 21
/// (hexadecimal) inclusive or a value between 23 and 7F inclusive".
pub open spec fn i_xx(b: u8) -> bool { b <= 0x21 || (0x23 <= b && b <= 0x7F) }

/// The index of the first byte of `h` from `p` on that is not an `XX` byte
/// (the length of `h` if there is none).
pub open spec fn i_xx_end(h: Seq<u8>, p: nat) -> nat
    decreases (if h.len() > p { h.len() - p } else { 0 }),
{
    if p < h.len() && i_xx(h[p as int]) { i_xx_end(h, p + 1) } else { p }
}

/// The bytes `@charset "`, as the first ten of the hex sequence.
pub open spec fn i_charset_prefix() -> Seq<u8> {
    seq![0x40u8, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x20, 0x22]
}

/// "the first 1024 bytes of the stream".
pub open spec fn i_first_1024(bytes: Seq<u8>) -> Seq<u8> {
    if bytes.len() > 1024 { bytes.subrange(0, 1024) } else { bytes }
}

/// The `XX` bytes of an encoding declaration at the start of the stream, "interpreted
/// as ASCII" (so each byte is the code point of the same value): `Some` when the
/// first 1024 bytes begin with the hex sequence, `None` otherwise.
pub open spec fn i_declared_label(bytes: Seq<u8>) -> Option<Seq<u32>> {
    let h = i_first_1024(bytes);
    if h.len() >= 10 && h.subrange(0, 10) == i_charset_prefix() {
        let e = i_xx_end(h, 10);
        if e + 1 < h.len() && h[e as int] == 0x22 && h[(e + 1) as int] == 0x3B {
            Some(h.subrange(10, e as int).map_values(|b: u8| b as u32))
        } else {
            None
        }
    } else {
        None
    }
}

/// "determine the fallback encoding" of a stylesheet, with |encoding label| the
/// label of the protocol and the stylesheet's byte stream `bytes`.
///
/// 1. "If HTTP or equivalent protocol provides an |encoding label| ..., get an
///    encoding from |encoding label|. If that does not return failure, return it."
/// 2. "Otherwise, check |stylesheet|'s byte stream. ... then get an encoding from a
///    string formed out of the sequence of XX bytes ... If the return value was
///    utf-16be or utf-16le, return utf-8; if it was anything else except failure,
///    return it."
/// 3. "Otherwise, if an environment encoding is provided by the referring
///    document, return it."
/// 4. "Otherwise, return utf-8."
pub open spec fn i_fallback_encoding(
    bytes: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment: Option<Encoding>,
) -> Encoding {
    let from_protocol = match protocol_label {
        Some(l) => get_an_encoding(l),
        None => None,
    };
    let from_declaration = match i_declared_label(bytes) {
        Some(l) => match get_an_encoding(l) {
            Some(e) => if e == Encoding::Utf16Be || e == Encoding::Utf16Le { Some(Encoding::Utf8) } else { Some(e) },
            None => None,
        },
        None => None,
    };
    match from_protocol {
        Some(e) => e,
        None => match from_declaration {
            Some(e) => e,
            None => match environment {
                Some(e) => e,
                None => Encoding::Utf8,
            },
        },
    }
}

/// "decode" a stylesheet's stream of bytes into a stream of code points: "1.
/// Determine the fallback encoding of |stylesheet|, and let |fallback| be the
/// result. 2. Decode |stylesheet|'s stream of bytes with fallback encoding
/// |fallback|, and return the result."
pub open spec fn i_decode_bytes(
    bytes: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment: Option<Encoding>,
) -> Option<Seq<int>> {
    match decode(bytes, i_fallback_encoding(bytes, protocol_label, environment)) {
        Some(s) => Some(s.map_values(|c: u32| c as int)),
        None => None,
    }
}

} // verus!
