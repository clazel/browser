//! Concrete inputs, evaluated on the spec, each stating what the standard's text says it
//! gives. Kept apart from [`super::lemmas`] so that a mutant that breaks one of them does
//! not stop Verus before it checks a kill certificate here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first token of `input`.
pub open spec fn first(input: Seq<u32>) -> Token {
    consume_a_token(input, 0, false).0
}

/// The position after the first token of `input`.
pub open spec fn after(input: Seq<u32>) -> int {
    consume_a_token(input, 0, false).1
}

/// A number with no sign or exponent.
pub open spec fn plain(number_part: Seq<u32>, is_integer: bool) -> Number {
    Number { number_part, exponent_part: Seq::empty(), is_integer, sign_character: None }
}

/// "9" is a digit, and "12" an integer.
pub proof fn lemma_example_digits()
    ensures
        first(seq![0x39u32]) == (Token::Number { number: plain(seq![0x39u32], true) }),
        first(seq![0x31u32, 0x32]) == (Token::Number { number: plain(seq![0x31u32, 0x32], true) }),
{
    assert(first(seq![0x39u32]) == (Token::Number { number: plain(seq![0x39u32], true) }))
        by (compute_only);
    assert(first(seq![0x31u32, 0x32]) == (Token::Number { number: plain(seq![0x31u32, 0x32], true) }))
        by (compute_only);
}

/// "1.5" and "1e2" are not integers, and "E" works as "e" does.
pub proof fn lemma_example_numbers()
    ensures
        first(seq![0x31u32, 0x2E, 0x35]) == (Token::Number {
            number: plain(seq![0x31u32, 0x2E, 0x35], false),
        }),
        first(seq![0x31u32, 0x65, 0x32]) == (Token::Number {
            number: Number {
                number_part: seq![0x31u32],
                exponent_part: seq![0x32u32],
                is_integer: false,
                sign_character: None,
            },
        }),
        first(seq![0x31u32, 0x45, 0x32]) == (Token::Number {
            number: Number {
                number_part: seq![0x31u32],
                exponent_part: seq![0x32u32],
                is_integer: false,
                sign_character: None,
            },
        }),
{
    assert(first(seq![0x31u32, 0x2E, 0x35]) == (Token::Number {
        number: plain(seq![0x31u32, 0x2E, 0x35], false),
    })) by (compute_only);
    assert(first(seq![0x31u32, 0x65, 0x32]) == (Token::Number {
        number: Number {
            number_part: seq![0x31u32],
            exponent_part: seq![0x32u32],
            is_integer: false,
            sign_character: None,
        },
    })) by (compute_only);
    assert(first(seq![0x31u32, 0x45, 0x32]) == (Token::Number {
        number: Number {
            number_part: seq![0x31u32],
            exponent_part: seq![0x32u32],
            is_integer: false,
            sign_character: None,
        },
    })) by (compute_only);
}

/// A tab is whitespace.
pub proof fn lemma_example_whitespace()
    ensures
        first(seq![0x09u32]) == Token::Whitespace,
{
    assert(first(seq![0x09u32]) == Token::Whitespace) by (compute_only);
}

/// "\10FFFF" takes all six hex digits, and "\D800" is a surrogate, so U+FFFD.
pub proof fn lemma_example_escapes()
    ensures
        consume_escaped_code_point(seq![0x31u32, 0x30, 0x46, 0x46, 0x46, 0x46], 0).0 == 0x10_FFFFu32,
        consume_escaped_code_point(seq![0x44u32, 0x38, 0x30, 0x30], 0).0 == REPLACEMENT,
{
    assert(consume_escaped_code_point(seq![0x31u32, 0x30, 0x46, 0x46, 0x46, 0x46], 0).0
        == 0x10_FFFFu32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x44u32, 0x38, 0x30, 0x30], 0).0 == REPLACEMENT)
        by (compute_only);
}

/// "URL(a)" is a url token: the name matches in any case.
pub proof fn lemma_example_urls()
    ensures
        first(seq![0x55u32, 0x52, 0x4C, 0x28, 0x61, 0x29]) == (Token::Url { value: seq![0x61u32] }),
{
    assert(first(seq![0x55u32, 0x52, 0x4C, 0x28, 0x61, 0x29]) == (Token::Url {
        value: seq![0x61u32],
    })) by (compute_only);
}

/// "-->" is a CDC token.
pub proof fn lemma_example_cdc()
    ensures
        first(seq![0x2Du32, 0x2D, 0x3E]) == Token::Cdc,
{
    assert(first(seq![0x2Du32, 0x2D, 0x3E]) == Token::Cdc) by (compute_only);
}

/// A newline ends a string badly, and stays in the input.
pub proof fn lemma_example_bad_string()
    ensures
        after(seq![0x22u32, 0x61, 0x0A]) == 2,
{
    assert(after(seq![0x22u32, 0x61, 0x0A]) == 2) by (compute_only);
}

/// "#1" is unrestricted, since a digit cannot start an ident sequence.
pub proof fn lemma_example_hash()
    ensures
        first(seq![0x23u32, 0x31]) == (Token::Hash { value: seq![0x31u32], is_id: false }),
{
    assert(first(seq![0x23u32, 0x31]) == (Token::Hash { value: seq![0x31u32], is_id: false }))
        by (compute_only);
}

/// CR LF is one newline.
pub proof fn lemma_example_filter()
    ensures
        filter_code_points(seq![0x0Du32, 0x0A]) == seq![0x0Au32],
{
    assert(filter_code_points(seq![0x0Du32, 0x0A]) == seq![0x0Au32]) by (compute_only);
}

/// "/*/" does not close itself.
pub proof fn lemma_example_comments()
    ensures
        consume_comments(seq![0x2Fu32, 0x2A, 0x2F, 0x61], 0) == 4,
{
    assert(consume_comments(seq![0x2Fu32, 0x2A, 0x2F, 0x61], 0) == 4) by (compute_only);
}

/// "U+4?" is U+40 to U+4F.
pub proof fn lemma_example_unicode_range()
    ensures
        consume_a_token(seq![0x55u32, 0x2B, 0x34, 0x3F], 0, true).0 == (Token::UnicodeRange {
            start: 0x40,
            end: 0x4F,
        }),
{
    assert(consume_a_token(seq![0x55u32, 0x2B, 0x34, 0x3F], 0, true).0 == (Token::UnicodeRange {
        start: 0x40,
        end: 0x4F,
    })) by (compute_only);
}

/// U+0080 is not an ident code point in the pinned text, and U+00B7 is.
pub proof fn lemma_example_non_ascii()
    ensures
        first(seq![0x80u32]) == (Token::Delim { value: 0x80u32 }),
        first(seq![0xB7u32]) == (Token::Ident { value: seq![0xB7u32] }),
{
    assert(first(seq![0x80u32]) == (Token::Delim { value: 0x80u32 })) by (compute_only);
    assert(first(seq![0xB7u32]) == (Token::Ident { value: seq![0xB7u32] })) by (compute_only);
}

/// The value of the number at the start of `input`, as (numerator, denominator).
pub open spec fn value_of(input: Seq<u32>) -> (int, nat) {
    number_value(consume_a_number(input, 0).0)
}

/// §4.3.12 step 6: "12" is 12, "-1.50" is -150/100, "+.5" is 5/10, "1e2" is 100 and
/// "1.5e-1" is 15/100. The fractions are not reduced.
pub proof fn lemma_example_number_value()
    ensures
        value_of(seq![0x31u32, 0x32]) == (12int, 1nat),
        value_of(seq![0x2Du32, 0x31, 0x2E, 0x35, 0x30]) == (-150int, 100nat),
        value_of(seq![0x2Bu32, 0x2E, 0x35]) == (5int, 10nat),
        value_of(seq![0x31u32, 0x65, 0x32]) == (100int, 1nat),
        value_of(seq![0x31u32, 0x2E, 0x35, 0x65, 0x2D, 0x31]) == (15int, 100nat),
{
    assert(value_of(seq![0x31u32, 0x32]) == (12int, 1nat)) by (compute_only);
    assert(value_of(seq![0x2Du32, 0x31, 0x2E, 0x35, 0x30]) == (-150int, 100nat)) by (compute_only);
    assert(value_of(seq![0x2Bu32, 0x2E, 0x35]) == (5int, 10nat)) by (compute_only);
    assert(value_of(seq![0x31u32, 0x65, 0x32]) == (100int, 1nat)) by (compute_only);
    assert(value_of(seq![0x31u32, 0x2E, 0x35, 0x65, 0x2D, 0x31]) == (15int, 100nat))
        by (compute_only);
}

/// §4.3.3 and §4.3.12: a unit makes a dimension and "%" a percentage, and a "." or an
/// exponent needs a digit after it.
pub proof fn lemma_example_numeric_tokens()
    ensures
        first(seq![0x31u32, 0x70, 0x78]) == (Token::Dimension { number: plain(seq![0x31u32], true), unit: seq![0x70u32, 0x78] }),
        first(seq![0x31u32, 0x25]) == (Token::Percentage { number: plain(seq![0x31u32], true) }),
        after(seq![0x31u32, 0x25]) == 2,
        first(seq![0x31u32, 0x2E]) == (Token::Number { number: plain(seq![0x31u32], true) }),
        after(seq![0x31u32, 0x2E]) == 1,
        after(seq![0x31u32, 0x65, 0x2B]) == 2,
        first(seq![0x2Bu32, 0x31]) == (Token::Number { number: Number { number_part: seq![0x2Bu32, 0x31], exponent_part: Seq::<u32>::empty(), is_integer: true, sign_character: Some(0x2Bu32) } }),
{
    assert(first(seq![0x31u32, 0x70, 0x78]) == (Token::Dimension { number: plain(seq![0x31u32], true), unit: seq![0x70u32, 0x78] })) by (compute_only);
    assert(first(seq![0x31u32, 0x25]) == (Token::Percentage { number: plain(seq![0x31u32], true) })) by (compute_only);
    assert(after(seq![0x31u32, 0x25]) == 2) by (compute_only);
    assert(first(seq![0x31u32, 0x2E]) == (Token::Number { number: plain(seq![0x31u32], true) })) by (compute_only);
    assert(after(seq![0x31u32, 0x2E]) == 1) by (compute_only);
    assert(after(seq![0x31u32, 0x65, 0x2B]) == 2) by (compute_only);
    assert(first(seq![0x2Bu32, 0x31]) == (Token::Number { number: Number { number_part: seq![0x2Bu32, 0x31], exponent_part: Seq::<u32>::empty(), is_integer: true, sign_character: Some(0x2Bu32) } })) by (compute_only);
}

/// §4.3.9, §4.3.10 and what they decide in §4.3.1.
pub proof fn lemma_example_starts()
    ensures
        first(seq![0x2Bu32, 0x2E]) == (Token::Delim { value: 0x2Bu32 }),
        first(seq![0x2Eu32, 0x61]) == (Token::Delim { value: 0x2Eu32 }),
        first(seq![0x2Du32, 0x2D]) == (Token::Ident { value: seq![0x2Du32, 0x2D] }),
        first(seq![0x2Du32, 0x5C, 0x34, 0x31]) == (Token::Ident { value: seq![0x2Du32, 0x41] }),
        first(seq![0x5Cu32, 0x0A]) == (Token::Delim { value: 0x5Cu32 }),
        first(seq![0x61u32, 0x28]) == (Token::Function { value: seq![0x61u32] }),
        after(seq![0x61u32, 0x28]) == 2,
        first(seq![0x3Cu32, 0x21, 0x2D, 0x61]) == (Token::Delim { value: 0x3Cu32 }),
        first(seq![0x40u32, 0x31]) == (Token::Delim { value: 0x40u32 }),
{
    assert(first(seq![0x2Bu32, 0x2E]) == (Token::Delim { value: 0x2Bu32 })) by (compute_only);
    assert(first(seq![0x2Eu32, 0x61]) == (Token::Delim { value: 0x2Eu32 })) by (compute_only);
    assert(first(seq![0x2Du32, 0x2D]) == (Token::Ident { value: seq![0x2Du32, 0x2D] })) by (compute_only);
    assert(first(seq![0x2Du32, 0x5C, 0x34, 0x31]) == (Token::Ident { value: seq![0x2Du32, 0x41] })) by (compute_only);
    assert(first(seq![0x5Cu32, 0x0A]) == (Token::Delim { value: 0x5Cu32 })) by (compute_only);
    assert(first(seq![0x61u32, 0x28]) == (Token::Function { value: seq![0x61u32] })) by (compute_only);
    assert(after(seq![0x61u32, 0x28]) == 2) by (compute_only);
    assert(first(seq![0x3Cu32, 0x21, 0x2D, 0x61]) == (Token::Delim { value: 0x3Cu32 })) by (compute_only);
    assert(first(seq![0x40u32, 0x31]) == (Token::Delim { value: 0x40u32 })) by (compute_only);
}

/// §4.3.7: one whitespace after hex digits goes with them, and what is not a code point
/// is U+FFFD.
pub proof fn lemma_example_escaped()
    ensures
        after(seq![0x5Cu32, 0x34, 0x31, 0x20]) == 4,
        first(seq![0x5Cu32, 0x30]) == (Token::Ident { value: seq![0xFFFDu32] }),
        first(seq![0x5Cu32, 0x31, 0x31, 0x30, 0x30, 0x30, 0x30]) == (Token::Ident { value: seq![0xFFFDu32] }),
        after(seq![0x5Cu32]) == 1,
{
    assert(after(seq![0x5Cu32, 0x34, 0x31, 0x20]) == 4) by (compute_only);
    assert(first(seq![0x5Cu32, 0x30]) == (Token::Ident { value: seq![0xFFFDu32] })) by (compute_only);
    assert(first(seq![0x5Cu32, 0x31, 0x31, 0x30, 0x30, 0x30, 0x30]) == (Token::Ident { value: seq![0xFFFDu32] })) by (compute_only);
    assert(after(seq![0x5Cu32]) == 1) by (compute_only);
}

/// §4.3.5: an escaped newline and a backslash at EOF add nothing, and the other quote is
/// just a code point.
pub proof fn lemma_example_strings()
    ensures
        first(seq![0x22u32, 0x5C, 0x0A, 0x62, 0x22]) == (Token::String { value: seq![0x62u32] }),
        first(seq![0x22u32, 0x5C]) == (Token::String { value: Seq::<u32>::empty() }),
        first(seq![0x22u32, 0x27, 0x22]) == (Token::String { value: seq![0x27u32] }),
{
    assert(first(seq![0x22u32, 0x5C, 0x0A, 0x62, 0x22]) == (Token::String { value: seq![0x62u32] })) by (compute_only);
    assert(first(seq![0x22u32, 0x5C]) == (Token::String { value: Seq::<u32>::empty() })) by (compute_only);
    assert(first(seq![0x22u32, 0x27, 0x22]) == (Token::String { value: seq![0x27u32] })) by (compute_only);
}

/// §4.3.4 and §4.3.6: a quote after "url(" makes a function, leaving one whitespace,
/// and an unquoted url ends at ")".
pub proof fn lemma_example_url_tokens()
    ensures
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x22, 0x61, 0x22, 0x29]) == (Token::Function { value: seq![0x75u32, 0x72, 0x6C] }),
        after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x22, 0x61, 0x22, 0x29]) == 4,
        after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x20, 0x20, 0x22, 0x61, 0x22, 0x29]) == 5,
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x29]) == (Token::Url { value: seq![0x61u32] }),
        after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x29]) == 7,
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x5C, 0x29, 0x62, 0x29]) == (Token::Url { value: seq![0x61u32, 0x29, 0x62] }),
{
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x22, 0x61, 0x22, 0x29]) == (Token::Function { value: seq![0x75u32, 0x72, 0x6C] })) by (compute_only);
    assert(after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x22, 0x61, 0x22, 0x29]) == 4) by (compute_only);
    assert(after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x20, 0x20, 0x22, 0x61, 0x22, 0x29]) == 5) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x29]) == (Token::Url { value: seq![0x61u32] })) by (compute_only);
    assert(after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x29]) == 7) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x5C, 0x29, 0x62, 0x29]) == (Token::Url { value: seq![0x61u32, 0x29, 0x62] })) by (compute_only);
}

/// §4.3.6 and §4.3.14: what makes a bad url, and where its remnants end.
pub proof fn lemma_example_bad_url()
    ensures
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x62, 0x29]) == (Token::BadUrl),
        after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x62, 0x29]) == 8,
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x22]) == (Token::BadUrl),
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x27]) == (Token::BadUrl),
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x28]) == (Token::BadUrl),
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x01]) == (Token::BadUrl),
        first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x5C, 0x0A, 0x29]) == (Token::BadUrl),
        after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x62, 0x5C, 0x29, 0x29]) == 10,
{
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x62, 0x29]) == (Token::BadUrl)) by (compute_only);
    assert(after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x62, 0x29]) == 8) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x22]) == (Token::BadUrl)) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x27]) == (Token::BadUrl)) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x28]) == (Token::BadUrl)) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x01]) == (Token::BadUrl)) by (compute_only);
    assert(first(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x5C, 0x0A, 0x29]) == (Token::BadUrl)) by (compute_only);
    assert(after(seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, 0x20, 0x62, 0x5C, 0x29, 0x29]) == 10) by (compute_only);
}

/// "unicode ranges allowed" decides, and a range needs what the text says.
pub proof fn lemma_example_unicode_ranges()
    ensures
        first(seq![0x55u32, 0x2B, 0x31]) == (Token::Ident { value: seq![0x55u32] }),
        consume_a_token(seq![0x55u32, 0x2B, 0x31, 0x2D, 0x32], 0, true).0 == (Token::UnicodeRange { start: 1, end: 2 }),
        consume_a_token(seq![0x55u32, 0x2B, 0x67], 0, true).0 == (Token::Ident { value: seq![0x55u32] }),
{
    assert(first(seq![0x55u32, 0x2B, 0x31]) == (Token::Ident { value: seq![0x55u32] })) by (compute_only);
    assert(consume_a_token(seq![0x55u32, 0x2B, 0x31, 0x2D, 0x32], 0, true).0 == (Token::UnicodeRange { start: 1, end: 2 })) by (compute_only);
    assert(consume_a_token(seq![0x55u32, 0x2B, 0x67], 0, true).0 == (Token::Ident { value: seq![0x55u32] })) by (compute_only);
}

/// `url(a` and the code point `c`.
pub open spec fn url_with(c: u32) -> Seq<u32> {
    seq![0x75u32, 0x72, 0x6C, 0x28, 0x61, c]
}

/// §4.2 non-printable code point: "between U+0000 NULL and U+0008 BACKSPACE inclusive, or
/// U+000B LINE TABULATION, or a code point between U+000E SHIFT OUT and U+001F INFORMATION
/// SEPARATOR ONE inclusive, or U+007F DELETE". In an unquoted url (§4.3.6) one is "a parse
/// error": remnants, and a bad url. The code points at the edges of those ranges that are
/// not in them are ordinary: U+000C and U+000D, and U+0080 above them, and U+0020, which
/// is whitespace, and ends the url.
pub proof fn lemma_example_non_printable()
    ensures
        first(url_with(0x08)) == Token::BadUrl,
        first(url_with(0x0B)) == Token::BadUrl,
        first(url_with(0x0E)) == Token::BadUrl,
        first(url_with(0x1F)) == Token::BadUrl,
        first(url_with(0x7F)) == Token::BadUrl,
        first(url_with(0x0C)) == (Token::Url { value: seq![0x61u32, 0x0C] }),
        first(url_with(0x0D)) == (Token::Url { value: seq![0x61u32, 0x0D] }),
        first(url_with(0x80)) == (Token::Url { value: seq![0x61u32, 0x80] }),
        first(url_with(0x20)) == (Token::Url { value: seq![0x61u32] }),
{
    assert(first(url_with(0x08)) == Token::BadUrl) by (compute_only);
    assert(first(url_with(0x0B)) == Token::BadUrl) by (compute_only);
    assert(first(url_with(0x0E)) == Token::BadUrl) by (compute_only);
    assert(first(url_with(0x1F)) == Token::BadUrl) by (compute_only);
    assert(first(url_with(0x7F)) == Token::BadUrl) by (compute_only);
    assert(first(url_with(0x0C)) == (Token::Url { value: seq![0x61u32, 0x0C] })) by (compute_only);
    assert(first(url_with(0x0D)) == (Token::Url { value: seq![0x61u32, 0x0D] })) by (compute_only);
    assert(first(url_with(0x80)) == (Token::Url { value: seq![0x61u32, 0x80] })) by (compute_only);
    assert(first(url_with(0x20)) == (Token::Url { value: seq![0x61u32] })) by (compute_only);
}

/// §4.3.2: a comment ends at the first `*` followed by `/`, and what follows is not part
/// of it: `/*a*/b` is five code points, and in `/*a/b*/c` the first `/` is inside.
pub proof fn lemma_example_comment_ends()
    ensures
        consume_comments(seq![0x2Fu32, 0x2A, 0x61, 0x2A, 0x2F, 0x62], 0) == 5,
        consume_comments(seq![0x2Fu32, 0x2A, 0x61, 0x2F, 0x62, 0x2A, 0x2F, 0x63], 0) == 7,
{
    assert(consume_comments(seq![0x2Fu32, 0x2A, 0x61, 0x2A, 0x2F, 0x62], 0) == 5)
        by (compute_only);
    assert(consume_comments(seq![0x2Fu32, 0x2A, 0x61, 0x2F, 0x62, 0x2A, 0x2F, 0x63], 0) == 7)
        by (compute_only);
}

/// §4.3.7: the value of a hex digit is its digit value, `a` to `f` in either case ten to
/// fifteen, and the digits are read in base 16: `\9` is U+0009, `\a` and `\A` are U+000A,
/// `\f` and `\F` are U+000F, `\10` is U+0010 and `\100` is U+0100.
pub proof fn lemma_example_hex_values()
    ensures
        consume_escaped_code_point(seq![0x39u32], 0).0 == 0x09u32,
        consume_escaped_code_point(seq![0x61u32], 0).0 == 0x0Au32,
        consume_escaped_code_point(seq![0x41u32], 0).0 == 0x0Au32,
        consume_escaped_code_point(seq![0x66u32], 0).0 == 0x0Fu32,
        consume_escaped_code_point(seq![0x46u32], 0).0 == 0x0Fu32,
        consume_escaped_code_point(seq![0x31u32, 0x30], 0).0 == 0x10u32,
        consume_escaped_code_point(seq![0x31u32, 0x30, 0x30], 0).0 == 0x100u32,
{
    assert(consume_escaped_code_point(seq![0x39u32], 0).0 == 0x09u32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x61u32], 0).0 == 0x0Au32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x41u32], 0).0 == 0x0Au32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x66u32], 0).0 == 0x0Fu32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x46u32], 0).0 == 0x0Fu32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x31u32, 0x30], 0).0 == 0x10u32) by (compute_only);
    assert(consume_escaped_code_point(seq![0x31u32, 0x30, 0x30], 0).0 == 0x100u32)
        by (compute_only);
}

/// §4.3.11: digits and hyphens continue an ident (`a1`, `a-`), an escape does too and
/// appends what it stands for (`a\g` is `ag`, `a\62 c` is `abc`), and a backslash and a
/// newline are not an escape, so the ident stops before them.
pub proof fn lemma_example_ident_sequence()
    ensures
        first(seq![0x61u32, 0x31]) == (Token::Ident { value: seq![0x61u32, 0x31] }),
        first(seq![0x61u32, 0x2D]) == (Token::Ident { value: seq![0x61u32, 0x2D] }),
        first(seq![0x61u32, 0x5C, 0x67]) == (Token::Ident { value: seq![0x61u32, 0x67] }),
        first(seq![0x61u32, 0x5C, 0x36, 0x32, 0x20, 0x63]) == (Token::Ident {
            value: seq![0x61u32, 0x62, 0x63],
        }),
        first(seq![0x61u32, 0x5C, 0x0A]) == (Token::Ident { value: seq![0x61u32] }),
        after(seq![0x61u32, 0x5C, 0x0A]) == 1,
        after(seq![0x61u32, 0x5C, 0x67]) == 3,
{
    assert(first(seq![0x61u32, 0x31]) == (Token::Ident { value: seq![0x61u32, 0x31] }))
        by (compute_only);
    assert(first(seq![0x61u32, 0x2D]) == (Token::Ident { value: seq![0x61u32, 0x2D] }))
        by (compute_only);
    assert(first(seq![0x61u32, 0x5C, 0x67]) == (Token::Ident { value: seq![0x61u32, 0x67] }))
        by (compute_only);
    assert(first(seq![0x61u32, 0x5C, 0x36, 0x32, 0x20, 0x63]) == (Token::Ident {
        value: seq![0x61u32, 0x62, 0x63],
    })) by (compute_only);
    assert(first(seq![0x61u32, 0x5C, 0x0A]) == (Token::Ident { value: seq![0x61u32] }))
        by (compute_only);
    assert(after(seq![0x61u32, 0x5C, 0x0A]) == 1) by (compute_only);
    assert(after(seq![0x61u32, 0x5C, 0x67]) == 3) by (compute_only);
}

/// §4.2 "non-ASCII ident code point", on both sides of each of its 15 ranges: an ident
/// code point alone is an ident (it is an ident-start code point too), any other
/// non-ASCII code point a delim. The ranges are inclusive: U+00B7; U+00C0 to U+00D6;
/// U+00D8 to U+00F6; U+00F8 to U+037D; U+037F to U+1FFF; U+200C; U+200D; U+203F; U+2040;
/// U+2070 to U+218F; U+2C00 to U+2FEF; U+3001 to U+D7FF; U+F900 to U+FDCF; U+FDF0 to
/// U+FFFD; and U+10000 up (here to U+10FFFF).
pub proof fn lemma_example_non_ascii_boundaries()
    ensures
        first(seq![0xB6u32]) == (Token::Delim { value: 0xB6u32 }),
        first(seq![0xB7u32]) == (Token::Ident { value: seq![0xB7u32] }),
        first(seq![0xB8u32]) == (Token::Delim { value: 0xB8u32 }),
        first(seq![0xBFu32]) == (Token::Delim { value: 0xBFu32 }),
        first(seq![0xC0u32]) == (Token::Ident { value: seq![0xC0u32] }),
        first(seq![0xD6u32]) == (Token::Ident { value: seq![0xD6u32] }),
        first(seq![0xD7u32]) == (Token::Delim { value: 0xD7u32 }),
        first(seq![0xD8u32]) == (Token::Ident { value: seq![0xD8u32] }),
        first(seq![0xF6u32]) == (Token::Ident { value: seq![0xF6u32] }),
        first(seq![0xF7u32]) == (Token::Delim { value: 0xF7u32 }),
        first(seq![0xF8u32]) == (Token::Ident { value: seq![0xF8u32] }),
        first(seq![0x37Du32]) == (Token::Ident { value: seq![0x37Du32] }),
        first(seq![0x37Eu32]) == (Token::Delim { value: 0x37Eu32 }),
        first(seq![0x37Fu32]) == (Token::Ident { value: seq![0x37Fu32] }),
        first(seq![0x1FFFu32]) == (Token::Ident { value: seq![0x1FFFu32] }),
        first(seq![0x2000u32]) == (Token::Delim { value: 0x2000u32 }),
        first(seq![0x200Bu32]) == (Token::Delim { value: 0x200Bu32 }),
        first(seq![0x200Cu32]) == (Token::Ident { value: seq![0x200Cu32] }),
        first(seq![0x200Du32]) == (Token::Ident { value: seq![0x200Du32] }),
        first(seq![0x200Eu32]) == (Token::Delim { value: 0x200Eu32 }),
        first(seq![0x203Eu32]) == (Token::Delim { value: 0x203Eu32 }),
        first(seq![0x203Fu32]) == (Token::Ident { value: seq![0x203Fu32] }),
        first(seq![0x2040u32]) == (Token::Ident { value: seq![0x2040u32] }),
        first(seq![0x2041u32]) == (Token::Delim { value: 0x2041u32 }),
        first(seq![0x206Fu32]) == (Token::Delim { value: 0x206Fu32 }),
        first(seq![0x2070u32]) == (Token::Ident { value: seq![0x2070u32] }),
        first(seq![0x218Fu32]) == (Token::Ident { value: seq![0x218Fu32] }),
        first(seq![0x2190u32]) == (Token::Delim { value: 0x2190u32 }),
        first(seq![0x2BFFu32]) == (Token::Delim { value: 0x2BFFu32 }),
        first(seq![0x2C00u32]) == (Token::Ident { value: seq![0x2C00u32] }),
        first(seq![0x2FEFu32]) == (Token::Ident { value: seq![0x2FEFu32] }),
        first(seq![0x2FF0u32]) == (Token::Delim { value: 0x2FF0u32 }),
        first(seq![0x3000u32]) == (Token::Delim { value: 0x3000u32 }),
        first(seq![0x3001u32]) == (Token::Ident { value: seq![0x3001u32] }),
        first(seq![0xD7FFu32]) == (Token::Ident { value: seq![0xD7FFu32] }),
        first(seq![0xD800u32]) == (Token::Delim { value: 0xD800u32 }),
        first(seq![0xF8FFu32]) == (Token::Delim { value: 0xF8FFu32 }),
        first(seq![0xF900u32]) == (Token::Ident { value: seq![0xF900u32] }),
        first(seq![0xFDCFu32]) == (Token::Ident { value: seq![0xFDCFu32] }),
        first(seq![0xFDD0u32]) == (Token::Delim { value: 0xFDD0u32 }),
        first(seq![0xFDEFu32]) == (Token::Delim { value: 0xFDEFu32 }),
        first(seq![0xFDF0u32]) == (Token::Ident { value: seq![0xFDF0u32] }),
        first(seq![0xFFFDu32]) == (Token::Ident { value: seq![0xFFFDu32] }),
        first(seq![0xFFFEu32]) == (Token::Delim { value: 0xFFFEu32 }),
        first(seq![0xFFFFu32]) == (Token::Delim { value: 0xFFFFu32 }),
        first(seq![0x1_0000u32]) == (Token::Ident { value: seq![0x1_0000u32] }),
        first(seq![0x10_FFFFu32]) == (Token::Ident { value: seq![0x10_FFFFu32] }),
{
    assert(first(seq![0xB6u32]) == (Token::Delim { value: 0xB6u32 })) by (compute_only);
    assert(first(seq![0xB7u32]) == (Token::Ident { value: seq![0xB7u32] })) by (compute_only);
    assert(first(seq![0xB8u32]) == (Token::Delim { value: 0xB8u32 })) by (compute_only);
    assert(first(seq![0xBFu32]) == (Token::Delim { value: 0xBFu32 })) by (compute_only);
    assert(first(seq![0xC0u32]) == (Token::Ident { value: seq![0xC0u32] })) by (compute_only);
    assert(first(seq![0xD6u32]) == (Token::Ident { value: seq![0xD6u32] })) by (compute_only);
    assert(first(seq![0xD7u32]) == (Token::Delim { value: 0xD7u32 })) by (compute_only);
    assert(first(seq![0xD8u32]) == (Token::Ident { value: seq![0xD8u32] })) by (compute_only);
    assert(first(seq![0xF6u32]) == (Token::Ident { value: seq![0xF6u32] })) by (compute_only);
    assert(first(seq![0xF7u32]) == (Token::Delim { value: 0xF7u32 })) by (compute_only);
    assert(first(seq![0xF8u32]) == (Token::Ident { value: seq![0xF8u32] })) by (compute_only);
    assert(first(seq![0x37Du32]) == (Token::Ident { value: seq![0x37Du32] })) by (compute_only);
    assert(first(seq![0x37Eu32]) == (Token::Delim { value: 0x37Eu32 })) by (compute_only);
    assert(first(seq![0x37Fu32]) == (Token::Ident { value: seq![0x37Fu32] })) by (compute_only);
    assert(first(seq![0x1FFFu32]) == (Token::Ident { value: seq![0x1FFFu32] })) by (compute_only);
    assert(first(seq![0x2000u32]) == (Token::Delim { value: 0x2000u32 })) by (compute_only);
    assert(first(seq![0x200Bu32]) == (Token::Delim { value: 0x200Bu32 })) by (compute_only);
    assert(first(seq![0x200Cu32]) == (Token::Ident { value: seq![0x200Cu32] })) by (compute_only);
    assert(first(seq![0x200Du32]) == (Token::Ident { value: seq![0x200Du32] })) by (compute_only);
    assert(first(seq![0x200Eu32]) == (Token::Delim { value: 0x200Eu32 })) by (compute_only);
    assert(first(seq![0x203Eu32]) == (Token::Delim { value: 0x203Eu32 })) by (compute_only);
    assert(first(seq![0x203Fu32]) == (Token::Ident { value: seq![0x203Fu32] })) by (compute_only);
    assert(first(seq![0x2040u32]) == (Token::Ident { value: seq![0x2040u32] })) by (compute_only);
    assert(first(seq![0x2041u32]) == (Token::Delim { value: 0x2041u32 })) by (compute_only);
    assert(first(seq![0x206Fu32]) == (Token::Delim { value: 0x206Fu32 })) by (compute_only);
    assert(first(seq![0x2070u32]) == (Token::Ident { value: seq![0x2070u32] })) by (compute_only);
    assert(first(seq![0x218Fu32]) == (Token::Ident { value: seq![0x218Fu32] })) by (compute_only);
    assert(first(seq![0x2190u32]) == (Token::Delim { value: 0x2190u32 })) by (compute_only);
    assert(first(seq![0x2BFFu32]) == (Token::Delim { value: 0x2BFFu32 })) by (compute_only);
    assert(first(seq![0x2C00u32]) == (Token::Ident { value: seq![0x2C00u32] })) by (compute_only);
    assert(first(seq![0x2FEFu32]) == (Token::Ident { value: seq![0x2FEFu32] })) by (compute_only);
    assert(first(seq![0x2FF0u32]) == (Token::Delim { value: 0x2FF0u32 })) by (compute_only);
    assert(first(seq![0x3000u32]) == (Token::Delim { value: 0x3000u32 })) by (compute_only);
    assert(first(seq![0x3001u32]) == (Token::Ident { value: seq![0x3001u32] })) by (compute_only);
    assert(first(seq![0xD7FFu32]) == (Token::Ident { value: seq![0xD7FFu32] })) by (compute_only);
    assert(first(seq![0xD800u32]) == (Token::Delim { value: 0xD800u32 })) by (compute_only);
    assert(first(seq![0xF8FFu32]) == (Token::Delim { value: 0xF8FFu32 })) by (compute_only);
    assert(first(seq![0xF900u32]) == (Token::Ident { value: seq![0xF900u32] })) by (compute_only);
    assert(first(seq![0xFDCFu32]) == (Token::Ident { value: seq![0xFDCFu32] })) by (compute_only);
    assert(first(seq![0xFDD0u32]) == (Token::Delim { value: 0xFDD0u32 })) by (compute_only);
    assert(first(seq![0xFDEFu32]) == (Token::Delim { value: 0xFDEFu32 })) by (compute_only);
    assert(first(seq![0xFDF0u32]) == (Token::Ident { value: seq![0xFDF0u32] })) by (compute_only);
    assert(first(seq![0xFFFDu32]) == (Token::Ident { value: seq![0xFFFDu32] })) by (compute_only);
    assert(first(seq![0xFFFEu32]) == (Token::Delim { value: 0xFFFEu32 })) by (compute_only);
    assert(first(seq![0xFFFFu32]) == (Token::Delim { value: 0xFFFFu32 })) by (compute_only);
    assert(first(seq![0x1_0000u32]) == (Token::Ident { value: seq![0x1_0000u32] }))
        by (compute_only);
    assert(first(seq![0x10_FFFFu32]) == (Token::Ident { value: seq![0x10_FFFFu32] }))
        by (compute_only);
}

} // verus!
