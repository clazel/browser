//! Concrete inputs, evaluated on the spec, each stating what the standard's text says it
//! gives. Kept apart from [`super::lemmas`] so that a mutant that breaks one of them does
//! not stop Verus before it checks a kill certificate there. Labels are early in the
//! sorted labels table (`866`, `ascii`, `csunicode`), which the evaluator reaches quickly.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The label `866`, for IBM866.
pub open spec fn label_866() -> Seq<u8> {
    seq![0x38u8, 0x36, 0x36]
}

/// The label `ascii`, for windows-1252.
pub open spec fn label_ascii() -> Seq<u8> {
    seq![0x61u8, 0x73, 0x63, 0x69, 0x69]
}

/// The label `csunicode`, for UTF-16LE.
pub open spec fn label_csunicode() -> Seq<u8> {
    seq![0x63u8, 0x73, 0x75, 0x6E, 0x69, 0x63, 0x6F, 0x64, 0x65]
}

/// `@charset "label";`.
pub open spec fn declaration(label: Seq<u8>) -> Seq<u8> {
    charset_prefix() + label + seq![0x22u8, 0x3B]
}

/// `n` spaces.
pub open spec fn spaces(n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        spaces((n - 1) as nat).push(0x20u8)
    }
}

/// `@charset "   866";`, 15 bytes long with no spaces. "Get an encoding" strips the
/// spaces, so this moves where the declaration ends and nothing else.
pub open spec fn padded(n: nat) -> Seq<u8> {
    declaration(spaces(n) + label_866())
}

/// The fallback encoding of bytes with nothing around them.
pub open spec fn alone(stylesheet: Seq<u8>) -> clazel_encoding::labels::spec::Encoding {
    determine_the_fallback_encoding(stylesheet, None, None)
}

/// A string for a label given from outside.
pub open spec fn given(label: Seq<u8>) -> Option<Seq<u32>> {
    Some(ascii_string(label))
}

/// Step 4: nothing at all is UTF-8.
pub proof fn lemma_example_default()
    ensures
        alone(Seq::empty()) == clazel_encoding::labels::spec::Encoding::Utf8,
{
    assert(alone(Seq::empty()) == clazel_encoding::labels::spec::Encoding::Utf8) by (compute_only);
}

/// Step 2: the declaration gives the encoding.
pub proof fn lemma_example_declaration()
    ensures
        alone(declaration(label_866())) == clazel_encoding::labels::spec::Encoding::Ibm866,
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(alone(declaration(label_866())) == clazel_encoding::labels::spec::Encoding::Ibm866)
        by (compute_only);
}

/// Step 2: the pattern is exact. Bytes from 80 up are not `XX` bytes, and without the
/// closing `22 3B` nothing matches.
pub proof fn lemma_example_pattern()
    ensures
        declared_label(declaration(seq![0x7Fu8])) == Some(seq![0x7Fu8]),
        declared_label(declaration(seq![0x80u8])) == None::<Seq<u8>>,
        declared_label(declaration(seq![0x00u8])) == Some(seq![0x00u8]),
        declared_label(charset_prefix() + label_866() + seq![0x22u8, 0x20]) == None::<Seq<u8>>,
        declared_label(charset_prefix() + label_866() + seq![0x22u8]) == None::<Seq<u8>>,
        declared_label(seq![0x40u8, 0x43, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x20, 0x22, 0x22, 0x3B])
            == None::<Seq<u8>>,
{
    assert(declared_label(declaration(seq![0x7Fu8])) == Some(seq![0x7Fu8])) by (compute_only);
    assert(declared_label(declaration(seq![0x80u8])) == None::<Seq<u8>>) by (compute_only);
    assert(declared_label(declaration(seq![0x00u8])) == Some(seq![0x00u8])) by (compute_only);
    assert(declared_label(charset_prefix() + label_866() + seq![0x22u8, 0x20]) == None::<Seq<u8>>)
        by (compute_only);
    assert(declared_label(charset_prefix() + label_866() + seq![0x22u8]) == None::<Seq<u8>>)
        by (compute_only);
    assert(declared_label(
        seq![0x40u8, 0x43, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x20, 0x22, 0x22, 0x3B],
    ) == None::<Seq<u8>>) by (compute_only);
}

/// "The first 1024 bytes": a declaration ending on byte 1024 counts, and one ending on
/// byte 1025 does not.
pub proof fn lemma_example_window()
    ensures
        alone(padded(1009)) == clazel_encoding::labels::spec::Encoding::Ibm866,
        alone(padded(1010)) == clazel_encoding::labels::spec::Encoding::Utf8,
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(alone(padded(1009)) == clazel_encoding::labels::spec::Encoding::Ibm866)
        by (compute_only);
    assert(alone(padded(1010)) == clazel_encoding::labels::spec::Encoding::Utf8) by (compute_only);
}

/// Step 2: a declaration of UTF-16 is UTF-8, in either byte order.
pub proof fn lemma_example_declared_utf16()
    ensures
        alone(declaration(label_csunicode())) == clazel_encoding::labels::spec::Encoding::Utf8,
        fallback_from_steps(None, Some(clazel_encoding::labels::spec::Encoding::Utf16Be), None)
            == clazel_encoding::labels::spec::Encoding::Utf8,
        fallback_from_steps(None, Some(clazel_encoding::labels::spec::Encoding::Utf16Le), None)
            == clazel_encoding::labels::spec::Encoding::Utf8,
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(alone(declaration(label_csunicode())) == clazel_encoding::labels::spec::Encoding::Utf8)
        by (compute_only);
    assert(fallback_from_steps(None, Some(clazel_encoding::labels::spec::Encoding::Utf16Be), None)
        == clazel_encoding::labels::spec::Encoding::Utf8) by (compute_only);
    assert(fallback_from_steps(None, Some(clazel_encoding::labels::spec::Encoding::Utf16Le), None)
        == clazel_encoding::labels::spec::Encoding::Utf8) by (compute_only);
}

/// Step 1 comes before step 2, step 2 before step 3, and failure at either moves on.
pub proof fn lemma_example_order()
    ensures
        determine_the_fallback_encoding(declaration(label_866()), given(label_ascii()), None)
            == clazel_encoding::labels::spec::Encoding::Windows1252,
        fallback_from_steps(
            None,
            Some(clazel_encoding::labels::spec::Encoding::Ibm866),
            Some(clazel_encoding::labels::spec::Encoding::Iso8859_2),
        ) == clazel_encoding::labels::spec::Encoding::Ibm866,
        fallback_from_steps(None, None, Some(clazel_encoding::labels::spec::Encoding::Iso8859_2))
            == clazel_encoding::labels::spec::Encoding::Iso8859_2,
        fallback_from_steps(None, None, None) == clazel_encoding::labels::spec::Encoding::Utf8,
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(determine_the_fallback_encoding(declaration(label_866()), given(label_ascii()), None)
        == clazel_encoding::labels::spec::Encoding::Windows1252) by (compute_only);
    assert(fallback_from_steps(
        None,
        Some(clazel_encoding::labels::spec::Encoding::Ibm866),
        Some(clazel_encoding::labels::spec::Encoding::Iso8859_2),
    ) == clazel_encoding::labels::spec::Encoding::Ibm866) by (compute_only);
    assert(fallback_from_steps(None, None, Some(clazel_encoding::labels::spec::Encoding::Iso8859_2))
        == clazel_encoding::labels::spec::Encoding::Iso8859_2) by (compute_only);
    assert(fallback_from_steps(None, None, None) == clazel_encoding::labels::spec::Encoding::Utf8)
        by (compute_only);
}

/// "Decode" uses the fallback: UTF-16LE from the protocol reads two bytes as one code
/// point, where UTF-8 would give two.
pub proof fn lemma_example_decode()
    ensures
        decode_bytes(seq![0x41u8, 0x00], given(label_csunicode()), None) == Some(seq![0x41u32]),
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(decode_bytes(seq![0x41u8, 0x00], given(label_csunicode()), None) == Some(seq![0x41u32]))
        by (compute_only);
}

} // verus!
