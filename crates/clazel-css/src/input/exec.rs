//! The executable input byte stream, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_encoding::labels::spec::Encoding;

verus! {

/// The label a caller passes, as the spec takes it.
pub open spec fn view_label(label: Option<&[u32]>) -> Option<Seq<u32>> {
    match label {
        Some(l) => Some(l@),
        None => None,
    }
}

/// The byte at `i`, or 0x100, which no byte is.
fn peek(bytes: &[u8], i: usize) -> (r: u32)
    ensures
        i < bytes.len() ==> r == bytes@[i as int] as u32,
        i >= bytes.len() ==> r == 0x100,
{
    match bytes.get(i) {
        Some(b) => *b as u32,
        None => 0x100,
    }
}

/// True if `bytes` start with [`charset_prefix`].
fn starts_with_charset_prefix(bytes: &[u8]) -> (r: bool)
    ensures
        r == clazel_encoding::hooks::spec::starts_with(bytes@, charset_prefix()),
{
    let r = peek(bytes, 0) == 0x40 && peek(bytes, 1) == 0x63 && peek(bytes, 2) == 0x68 && peek(
        bytes,
        3,
    ) == 0x61 && peek(bytes, 4) == 0x72 && peek(bytes, 5) == 0x73 && peek(bytes, 6) == 0x65 && peek(
        bytes,
        7,
    ) == 0x74 && peek(bytes, 8) == 0x20 && peek(bytes, 9) == 0x22;
    proof {
        let p = charset_prefix();
        assert(p.len() == 10);
        if r {
            assert(bytes@.subrange(0, 10) =~= p);
        } else if clazel_encoding::hooks::spec::starts_with(bytes@, p) {
            let s = bytes@.subrange(0, 10);
            assert(s == p);
            assert(s[0] == bytes@[0] && s[1] == bytes@[1] && s[2] == bytes@[2] && s[3] == bytes@[3]
                && s[4] == bytes@[4]);
            assert(s[5] == bytes@[5] && s[6] == bytes@[6] && s[7] == bytes@[7] && s[8] == bytes@[8]
                && s[9] == bytes@[9]);
        }
    }
    r
}

/// [`skip_xx_bytes`] from `start`.
fn read_xx_bytes(bytes: &[u8], start: usize) -> (r: usize)
    requires
        start <= bytes.len(),
    ensures
        r as int == skip_xx_bytes(bytes@, start as int),
        start <= r <= bytes.len(),
{
    let mut pos = start;
    loop
        invariant
            start <= pos <= bytes.len(),
            skip_xx_bytes(bytes@, pos as int) == skip_xx_bytes(bytes@, start as int),
        decreases bytes.len() - pos,
    {
        if pos >= bytes.len() {
            return pos;
        }
        let b = peek(bytes, pos);
        if !(b <= 0x21 || (0x23 <= b && b <= 0x7F)) {
            return pos;
        }
        // Never saturates: `pos` is below the length.
        pos = pos.saturating_add(1);
    }
}

/// [`ascii_string`] of the bytes from `start` up to `end`.
fn read_ascii_string(bytes: &[u8], start: usize, end: usize) -> (r: Vec<u32>)
    requires
        start <= end <= bytes.len(),
    ensures
        r@ == ascii_string(bytes@.subrange(start as int, end as int)),
{
    let mut out: Vec<u32> = Vec::new();
    let mut pos = start;
    while pos < end
        invariant
            start <= pos <= end <= bytes.len(),
            out@.len() == pos - start,
            forall|k: int|
                0 <= k < out@.len() ==> #[trigger] out@[k] == bytes@[start + k] as u32,
        decreases end - pos,
    {
        out.push(peek(bytes, pos));
        // Never saturates: `pos` is below `end`.
        pos = pos.saturating_add(1);
    }
    assert(out@ =~= ascii_string(bytes@.subrange(start as int, end as int)));
    out
}

/// [`declared_label`] of `bytes`, as [`ascii_string`] reads it.
fn read_declared_label(bytes: &[u8]) -> (r: Option<Vec<u32>>)
    ensures
        match declared_label(bytes@) {
            Some(label) => r is Some && r->0@ == ascii_string(label),
            None => r is None,
        },
{
    if !starts_with_charset_prefix(bytes) {
        return None;
    }
    assert(charset_prefix().len() == 10);
    let end = read_xx_bytes(bytes, 10);
    // Never saturates: `end` is at most the length of a slice.
    if peek(bytes, end) == 0x22 && peek(bytes, end.saturating_add(1)) == 0x3B {
        Some(read_ascii_string(bytes, 10, end))
    } else {
        None
    }
}

/// Contract for `fallback_encoding`: "determine the fallback encoding".
pub fn fallback_encoding(
    stylesheet: &[u8],
    protocol_label: Option<&[u32]>,
    environment_encoding: Option<Encoding>,
) -> (r: Encoding)
    ensures
        super::contract::fallback_encoding_ensures(
            stylesheet@,
            view_label(protocol_label),
            environment_encoding,
            r,
        ),
{
    let from_protocol = match protocol_label {
        Some(label) => clazel_encoding::labels::exec::get_an_encoding(label),
        None => None,
    };
    let window = match stylesheet.split_at_checked(1024) {
        Some((first, _)) => first,
        None => stylesheet,
    };
    assert(window@ =~= first_1024_bytes(stylesheet@));
    let from_declaration = match read_declared_label(window) {
        Some(label) => clazel_encoding::labels::exec::get_an_encoding(label.as_slice()),
        None => None,
    };
    match from_protocol {
        Some(encoding) => encoding,
        None => match from_declaration {
            Some(Encoding::Utf16Be) | Some(Encoding::Utf16Le) => Encoding::Utf8,
            Some(encoding) => encoding,
            None => match environment_encoding {
                Some(encoding) => encoding,
                None => Encoding::Utf8,
            },
        },
    }
}

/// Contract for `decode_stylesheet`: "decode" a style sheet's bytes into code points, for
/// [`crate::tokenizer::exec::filter`]. `None` when `clazel-encoding` has no decoder for
/// the encoding the bytes need.
pub fn decode_stylesheet(
    stylesheet: &[u8],
    protocol_label: Option<&[u32]>,
    environment_encoding: Option<Encoding>,
) -> (r: Option<Vec<u32>>)
    ensures
        super::contract::decode_stylesheet_ensures(
            stylesheet@,
            view_label(protocol_label),
            environment_encoding,
            match r {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    let fallback = fallback_encoding(stylesheet, protocol_label, environment_encoding);
    clazel_encoding::hooks::decode::decode(stylesheet, fallback)
}

} // verus!
