//! Facts proven about the sniffing spec. They are evidence that the
//! transcription is right, not part of what the implementation must meet.
//!
//! - [`lemma_attribute_advances`] and [`lemma_find_gt`] (with the other
//!   searches): the guards of the spec's recursions always hold, so the
//!   branches marked "Unreachable" are never taken.
//! - [`lemma_meta_never_utf16`]: a `<meta>` never yields UTF-16BE/LE or
//!   x-user-defined (steps 14 and 15; the standard notes that "change the
//!   encoding" repeats them).
//! - [`lemma_prescan_input_bounded`]: the prescan reads at most 1024 bytes.
//! - [`lemma_change_the_encoding`]: "change the encoding" never restarts
//!   from UTF-16BE/LE, never restarts into UTF-16BE/LE or x-user-defined,
//!   and never restarts into the encoding already used, so a second change
//!   cannot happen.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

proof fn lemma_attr_unquoted(b: Seq<u8>, pos: nat, name: Seq<u8>, value: Seq<u8>)
    ensures
        match attr_unquoted(b, pos, name, value) {
            Attr::Some(_, _, p) => pos <= p <= b.len(),
            Attr::None(_) => false,
            Attr::Abort => true,
        },
    decreases b.len() - pos,
{
    if pos < b.len() && !(is_space(b[pos as int]) || b[pos as int] == 0x3E) {
        lemma_attr_unquoted(b, pos + 1, name, value.push(lower(b[pos as int])));
    }
}

proof fn lemma_attr_quoted(b: Seq<u8>, pos: nat, name: Seq<u8>, value: Seq<u8>, quote: u8)
    ensures
        match attr_quoted(b, pos, name, value, quote) {
            Attr::Some(_, _, p) => pos < p <= b.len(),
            Attr::None(_) => false,
            Attr::Abort => true,
        },
    decreases b.len() - pos,
{
    if pos < b.len() && b[pos as int] != quote {
        lemma_attr_quoted(b, pos + 1, name, value.push(lower(b[pos as int])), quote);
    }
}

proof fn lemma_attr_value(b: Seq<u8>, pos: nat, name: Seq<u8>)
    ensures
        match attr_value(b, pos, name) {
            Attr::Some(_, _, p) => pos <= p <= b.len(),
            Attr::None(_) => false,
            Attr::Abort => true,
        },
    decreases b.len() - pos,
{
    if pos < b.len() {
        let c = b[pos as int];
        if is_space(c) {
            lemma_attr_value(b, pos + 1, name);
        } else if c == 0x22 || c == 0x27 {
            lemma_attr_quoted(b, pos + 1, name, seq![], c);
        } else if c != 0x3E {
            lemma_attr_unquoted(b, pos + 1, name, seq![lower(c)]);
        }
    }
}

proof fn lemma_attr_spaces(b: Seq<u8>, pos: nat, name: Seq<u8>)
    ensures
        match attr_spaces(b, pos, name) {
            Attr::Some(_, _, p) => pos <= p <= b.len(),
            Attr::None(_) => false,
            Attr::Abort => true,
        },
    decreases b.len() - pos,
{
    if pos < b.len() {
        if is_space(b[pos as int]) {
            lemma_attr_spaces(b, pos + 1, name);
        } else if b[pos as int] == 0x3D {
            lemma_attr_value(b, pos + 1, name);
        }
    }
}

proof fn lemma_attr_name(b: Seq<u8>, pos: nat, name: Seq<u8>, start: nat)
    requires
        start <= pos,
        pos > start || (pos < b.len() && !is_space(b[pos as int]) && b[pos as int] != 0x2F && b[pos as int]
            != 0x3E),
    ensures
        match attr_name(b, pos, name) {
            Attr::Some(_, _, p) => start < p <= b.len(),
            Attr::None(_) => false,
            Attr::Abort => true,
        },
    decreases b.len() - pos,
{
    if pos < b.len() {
        let c = b[pos as int];
        if c == 0x3D && name.len() > 0 {
            lemma_attr_value(b, pos + 1, name);
        } else if is_space(c) {
            lemma_attr_spaces(b, pos, name);
        } else if !(c == 0x2F || c == 0x3E) {
            lemma_attr_name(b, pos + 1, name.push(lower(c)), start);
        }
    }
}

/// "Get an attribute" moves the position when it finds an attribute, and
/// stays within the bytes; "there isn't one" is at a byte of `b`.
pub proof fn lemma_attribute_advances(b: Seq<u8>, pos: nat)
    ensures
        match get_attribute(b, pos) {
            Attr::Some(_, _, p) => pos < p <= b.len(),
            Attr::None(p) => pos <= p < b.len(),
            Attr::Abort => true,
        },
    decreases b.len() - pos,
{
    if pos < b.len() {
        if is_space(b[pos as int]) || b[pos as int] == 0x2F {
            lemma_attribute_advances(b, pos + 1);
        } else if b[pos as int] != 0x3E {
            lemma_attr_name(b, pos, seq![], pos);
        }
    }
}

/// A search for 0x3E finds a byte at or after where it started.
pub proof fn lemma_find_gt(b: Seq<u8>, q: nat)
    ensures
        match find_gt(b, q) {
            Some(p) => q <= p < b.len(),
            None => true,
        },
    decreases b.len() - q,
{
    if q < b.len() && b[q as int] != 0x3E {
        lemma_find_gt(b, q + 1);
    }
}

/// The same for the end of a comment.
pub proof fn lemma_find_comment_end(b: Seq<u8>, q: nat)
    ensures
        match find_comment_end(b, q) {
            Some(p) => q <= p < b.len(),
            None => true,
        },
    decreases b.len() - q,
{
    if q < b.len() && !(q >= 2 && b[q as int] == 0x3E && b[q - 1] == 0x2D && b[q - 2] == 0x2D) {
        lemma_find_comment_end(b, q + 1);
    }
}

/// A `<meta>`'s processing never yields UTF-16BE/LE or x-user-defined.
pub proof fn lemma_meta_never_utf16(m: Meta, pos: nat)
    ensures
        match meta_processing(m, pos) {
            MetaResult::Return(e) => e != clazel_encoding::labels::spec::Encoding::Utf16Be && e
                != clazel_encoding::labels::spec::Encoding::Utf16Le && e
                != clazel_encoding::labels::spec::Encoding::XUserDefined,
            _ => true,
        },
{
}

/// The prescan reads at most the first 1024 bytes.
pub proof fn lemma_prescan_input_bounded(bytes: Seq<u8>)
    ensures
        prescan_input(bytes).len() <= 1024,
        prescan_input(bytes) =~= bytes.subrange(0, prescan_input(bytes).len() as int),
{
}

/// "Change the encoding" keeps UTF-16BE/LE, never moves to UTF-16BE/LE or
/// x-user-defined, and never restarts with the encoding already used, so
/// the restarted parse, asked again with the same `<meta>`, does not
/// restart a second time.
pub proof fn lemma_change_the_encoding(
    current: clazel_encoding::labels::spec::Encoding,
    new: clazel_encoding::labels::spec::Encoding,
)
    ensures
        (current == clazel_encoding::labels::spec::Encoding::Utf16Be || current
            == clazel_encoding::labels::spec::Encoding::Utf16Le) ==> change_the_encoding(current, new) is None,
        match change_the_encoding(current, new) {
            Some(e) => e != current && e != clazel_encoding::labels::spec::Encoding::Utf16Be && e
                != clazel_encoding::labels::spec::Encoding::Utf16Le && e
                != clazel_encoding::labels::spec::Encoding::XUserDefined && change_the_encoding(e, new) is None,
            None => true,
        },
{
}

} // verus!
