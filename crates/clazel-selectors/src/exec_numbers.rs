//! What the tokenizer makes of a number, which `<an+b>` needs to read an integer token's
//! value: an integer token's number part is its sign, if any, and digits, and it has no
//! exponent. `clazel-css`'s tokenizer spec states how a token is made (`consume_a_token`)
//! and not this, so each branch is followed here.

#[allow(unused_imports)]
use super::spec::*;
use clazel_css::tokenizer::spec::{
    at, consume_a_number, consume_a_numeric_token, consume_a_string_token, consume_a_token,
    consume_a_unicode_range_token, consume_a_url_token, consume_an_ident_like_token, consume_comments,
    consume_digits, consume_string_loop, consume_url_loop, is_digit, is_newline, is_non_printable_code_point,
    is_whitespace, number_step_2, number_step_4, remaining, would_start_a_number,
    would_start_an_ident_sequence, EOF,
};
use clazel_css::tokenizer::termination::lemma_escape_advances;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every code point of `s` is a digit.
pub open spec fn digits_only(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> is_digit(#[trigger] s[k])
}

/// A number the way the tokenizer makes an integer: no exponent, and digits after the
/// sign.
pub open spec fn num_ok(n: Number) -> bool {
    n.is_integer ==> n.exponent_part.len() == 0 && digits_only(unsigned(n.number_part))
}

/// A token whose numbers, if any, are as the tokenizer makes them.
pub open spec fn token_ok(t: Token) -> bool {
    match t {
        Token::Number { number } => num_ok(number),
        Token::Percentage { number } => num_ok(number),
        Token::Dimension { number, .. } => num_ok(number),
        _ => true,
    }
}

/// Consuming digits onto digits gives digits.
proof fn lemma_digits_only(input: Seq<u32>, pos: int, part: Seq<u32>)
    requires
        digits_only(part),
    ensures
        digits_only(consume_digits(input, pos, part).0),
    decreases remaining(input, pos),
{
    if is_digit(at(input, pos)) {
        let p = part.push(at(input, pos));
        assert forall|k: int| 0 <= k < p.len() implies is_digit(p[k]) by {
            if k < part.len() {
                assert(p[k] == part[k]);
            }
        }
        lemma_digits_only(input, pos + 1, p);
    }
}

/// "consume a number" makes an integer as the tokenizer does.
proof fn lemma_number_ok(input: Seq<u32>, pos: int)
    ensures
        num_ok(consume_a_number(input, pos).0),
{
    let (signed, sign_character, after_sign) = number_step_2(input, pos);
    let (integer, after_integer) = consume_digits(input, after_sign, signed);
    let c = at(input, pos);
    if c == 0x2B || c == 0x2D {
        assert(signed.len() == 1 && signed[0] == c);
        let (part, _) = consume_digits(input, after_sign, signed);
        lemma_digits_only(input, after_sign, Seq::empty());
        lemma_consume_digits_prefix(input, after_sign, signed);
        // The digits are the part after its sign.
        assert(unsigned(part) =~= part.drop_first());
    } else {
        lemma_digits_only(input, after_sign, Seq::empty());
        let (part, _) = consume_digits(input, after_sign, Seq::empty());
        assert(signed =~= Seq::<u32>::empty());
        assert(unsigned(part) =~= part) by {
            if part.len() > 0 {
                assert(is_digit(part[0]));
            }
        }
    }
    let (number_part, no_fraction, after_fraction) = number_step_4(input, after_integer, integer);
    if no_fraction {
        assert(number_part == integer);
    }
}

/// Consuming digits onto `part` keeps `part` and adds digits.
proof fn lemma_consume_digits_prefix(input: Seq<u32>, pos: int, part: Seq<u32>)
    ensures
        consume_digits(input, pos, part).0.len() >= part.len(),
        forall|k: int| 0 <= k < part.len() ==> consume_digits(input, pos, part).0[k] == part[k],
        digits_only(consume_digits(input, pos, part).0.skip(part.len() as int)),
    decreases remaining(input, pos),
{
    if is_digit(at(input, pos)) {
        let p = part.push(at(input, pos));
        lemma_consume_digits_prefix(input, pos + 1, p);
        let r = consume_digits(input, pos + 1, p).0;
        assert forall|k: int| 0 <= k < part.len() implies r[k] == part[k] by {
            assert(p[k] == part[k]);
        }
        assert forall|k: int| 0 <= k < r.skip(part.len() as int).len() implies is_digit(
            r.skip(part.len() as int)[k],
        ) by {
            let j = part.len() as int + k;
            if j >= p.len() {
                assert(r.skip(p.len() as int)[j - p.len()] == r[j]);
            } else {
                assert(j == part.len());
                assert(r[j] == p[j]);
            }
        }
    }
}

/// A numeric token's numbers are as the tokenizer makes them.
proof fn lemma_numeric_token_ok(input: Seq<u32>, pos: int)
    ensures
        token_ok(consume_a_numeric_token(input, pos).0),
{
    lemma_number_ok(input, pos);
}

/// A string token is not a number.
proof fn lemma_string_ok(input: Seq<u32>, pos: int, ending: u32, value: Seq<u32>)
    ensures
        token_ok(consume_string_loop(input, pos, ending, value).0),
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c != ending && c != EOF && !is_newline(c) {
        if c == 0x5C {
            if at(input, pos + 1) == EOF {
                lemma_string_ok(input, pos + 1, ending, value);
            } else if is_newline(at(input, pos + 1)) {
                lemma_string_ok(input, pos + 2, ending, value);
            } else {
                lemma_escape_advances(input, pos + 1);
                let (code_point, next) = clazel_css::tokenizer::spec::consume_escaped_code_point(
                    input,
                    pos + 1,
                );
                lemma_string_ok(input, next, ending, value.push(code_point));
            }
        } else {
            lemma_string_ok(input, pos + 1, ending, value.push(c));
        }
    }
}

/// A url token is not a number.
proof fn lemma_url_ok(input: Seq<u32>, pos: int, value: Seq<u32>)
    ensures
        token_ok(consume_url_loop(input, pos, value).0),
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c == 0x29 || c == EOF {
    } else if is_whitespace(c) {
    } else if c == 0x22 || c == 0x27 || c == 0x28 || is_non_printable_code_point(c) {
    } else if c == 0x5C {
        if clazel_css::tokenizer::spec::are_a_valid_escape(c, at(input, pos + 1)) {
            lemma_escape_advances(input, pos + 1);
            let (code_point, next) = clazel_css::tokenizer::spec::consume_escaped_code_point(
                input,
                pos + 1,
            );
            lemma_url_ok(input, next, value.push(code_point));
        }
    } else {
        lemma_url_ok(input, pos + 1, value.push(c));
    }
}

/// An ident-like token is not a number.
proof fn lemma_ident_like_ok(input: Seq<u32>, pos: int)
    ensures
        token_ok(consume_an_ident_like_token(input, pos).0),
{
    let (string, after) = clazel_css::tokenizer::spec::consume_ident_sequence(input, pos);
    if clazel_css::tokenizer::spec::is_url(string) && at(input, after) == 0x28 {
        let next = clazel_css::tokenizer::spec::consume_whitespace_but_one(input, after + 1);
        if !(clazel_css::tokenizer::spec::is_quote(at(input, next)) || (is_whitespace(at(input, next))
            && clazel_css::tokenizer::spec::is_quote(at(input, next + 1)))) {
            lemma_url_ok(
                input,
                clazel_css::tokenizer::spec::consume_whitespace(input, next),
                Seq::empty(),
            );
        }
    }
}

/// Every token the tokenizer makes has its numbers as the tokenizer makes them.
pub proof fn lemma_token_ok(input: Seq<u32>, start: int, unicode_ranges_allowed: bool)
    ensures
        token_ok(consume_a_token(input, start, unicode_ranges_allowed).0),
{
    let current = consume_comments(input, start);
    let c = at(input, current);
    let pos = current + 1;
    let next = at(input, pos);
    let next2 = at(input, pos + 1);
    if is_whitespace(c) {
    } else if c == 0x22 || c == 0x27 {
        lemma_string_ok(input, pos, c, Seq::empty());
    } else if c == 0x2B || c == 0x2E {
        if would_start_a_number(c, next, next2) {
            lemma_numeric_token_ok(input, current);
        }
    } else if c == 0x2D {
        if would_start_a_number(c, next, next2) {
            lemma_numeric_token_ok(input, current);
        } else if !(next == 0x2D && next2 == 0x3E) && would_start_an_ident_sequence(c, next, next2) {
            lemma_ident_like_ok(input, current);
        }
    } else if c == 0x5C {
        if clazel_css::tokenizer::spec::are_a_valid_escape(c, next) {
            lemma_ident_like_ok(input, current);
        }
    } else if is_digit(c) {
        lemma_numeric_token_ok(input, current);
    } else if c == 0x55 || c == 0x75 {
        if !(unicode_ranges_allowed && clazel_css::tokenizer::spec::would_start_a_unicode_range(
            c,
            next,
            next2,
        )) {
            lemma_ident_like_ok(input, current);
        }
    } else if clazel_css::tokenizer::spec::is_ident_start_code_point(c) {
        lemma_ident_like_ok(input, current);
    }
}

} // verus!
