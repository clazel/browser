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

} // verus!
