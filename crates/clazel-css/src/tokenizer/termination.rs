//! Why the recursive functions of [`super::spec`] end: each one calls itself at a later
//! position. These are facts Verus needs to accept the spec, not claims about it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`consume_hex_digits`] does not move backwards.
pub proof fn lemma_hex_digits_advance(input: Seq<u32>, pos: int, limit: nat, value: nat)
    ensures
        consume_hex_digits(input, pos, limit, value).1 >= pos,
    decreases limit,
{
    if limit > 0 && is_hex_digit(at(input, pos)) {
        lemma_hex_digits_advance(
            input,
            pos + 1,
            (limit - 1) as nat,
            value * 16 + hex_value(at(input, pos)),
        );
    }
}

/// [`consume_escaped_code_point`] does not move backwards.
pub proof fn lemma_escape_advances(input: Seq<u32>, pos: int)
    ensures
        consume_escaped_code_point(input, pos).1 >= pos,
{
    let c = at(input, pos);
    if is_hex_digit(c) {
        lemma_hex_digits_advance(input, pos + 1, 5, hex_value(c));
    }
}

/// [`end_of_comment`] does not move backwards.
pub proof fn lemma_end_of_comment_advances(input: Seq<u32>, pos: int)
    ensures
        end_of_comment(input, pos) >= pos,
    decreases remaining(input, pos),
{
    if pos < input.len() && !(at(input, pos) == 0x2A && at(input, pos + 1) == 0x2F) {
        lemma_end_of_comment_advances(input, pos + 1);
    }
}

/// [`consume_comments`] does not move backwards.
pub proof fn lemma_comments_advance(input: Seq<u32>, pos: int)
    ensures
        consume_comments(input, pos) >= pos,
    decreases remaining(input, pos),
{
    if at(input, pos) == 0x2F && at(input, pos + 1) == 0x2A {
        lemma_end_of_comment_advances(input, pos + 2);
        lemma_comments_advance(input, end_of_comment(input, pos + 2));
    }
}

/// [`consume_whitespace`] does not move backwards.
pub proof fn lemma_whitespace_advances(input: Seq<u32>, pos: int)
    ensures
        consume_whitespace(input, pos) >= pos,
    decreases remaining(input, pos),
{
    if is_whitespace(at(input, pos)) {
        lemma_whitespace_advances(input, pos + 1);
    }
}

/// [`consume_whitespace_but_one`] does not move backwards.
pub proof fn lemma_whitespace_but_one_advances(input: Seq<u32>, pos: int)
    ensures
        consume_whitespace_but_one(input, pos) >= pos,
    decreases remaining(input, pos),
{
    if is_whitespace(at(input, pos)) && is_whitespace(at(input, pos + 1)) {
        lemma_whitespace_but_one_advances(input, pos + 1);
    }
}

/// [`consume_digits`] does not move backwards.
pub proof fn lemma_digits_advance(input: Seq<u32>, pos: int, part: Seq<u32>)
    ensures
        consume_digits(input, pos, part).1 >= pos,
    decreases remaining(input, pos),
{
    if is_digit(at(input, pos)) {
        lemma_digits_advance(input, pos + 1, part.push(at(input, pos)));
    }
}

/// [`consume_ident_sequence_loop`] does not move backwards.
pub proof fn lemma_ident_sequence_advances(input: Seq<u32>, pos: int, result: Seq<u32>)
    ensures
        consume_ident_sequence_loop(input, pos, result).1 >= pos,
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if is_ident_code_point(c) {
        lemma_ident_sequence_advances(input, pos + 1, result.push(c));
    } else if are_a_valid_escape(c, at(input, pos + 1)) {
        lemma_escape_advances(input, pos + 1);
        let (code_point, next) = consume_escaped_code_point(input, pos + 1);
        lemma_ident_sequence_advances(input, next, result.push(code_point));
    }
}

/// [`consume_string_loop`] does not move backwards.
pub proof fn lemma_string_advances(input: Seq<u32>, pos: int, ending: u32, value: Seq<u32>)
    ensures
        consume_string_loop(input, pos, ending, value).1 >= pos,
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c != ending && c != EOF && !is_newline(c) {
        if c == 0x5C {
            if at(input, pos + 1) == EOF {
                lemma_string_advances(input, pos + 1, ending, value);
            } else if is_newline(at(input, pos + 1)) {
                lemma_string_advances(input, pos + 2, ending, value);
            } else {
                lemma_escape_advances(input, pos + 1);
                let (code_point, next) = consume_escaped_code_point(input, pos + 1);
                lemma_string_advances(input, next, ending, value.push(code_point));
            }
        } else {
            lemma_string_advances(input, pos + 1, ending, value.push(c));
        }
    }
}

/// [`consume_remnants_of_a_bad_url`] does not move backwards.
pub proof fn lemma_remnants_advance(input: Seq<u32>, pos: int)
    ensures
        consume_remnants_of_a_bad_url(input, pos) >= pos,
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c != 0x29 && c != EOF {
        if are_a_valid_escape(c, at(input, pos + 1)) {
            lemma_escape_advances(input, pos + 1);
            let (_, next) = consume_escaped_code_point(input, pos + 1);
            lemma_remnants_advance(input, next);
        } else {
            lemma_remnants_advance(input, pos + 1);
        }
    }
}

/// [`consume_url_loop`] does not move backwards.
pub proof fn lemma_url_advances(input: Seq<u32>, pos: int, value: Seq<u32>)
    ensures
        consume_url_loop(input, pos, value).1 >= pos,
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c == 0x29 || c == EOF {
    } else if is_whitespace(c) {
        lemma_whitespace_advances(input, pos + 1);
        let after = consume_whitespace(input, pos + 1);
        lemma_remnants_advance(input, after);
    } else if c == 0x22 || c == 0x27 || c == 0x28 || is_non_printable_code_point(c) {
        lemma_remnants_advance(input, pos + 1);
    } else if c == 0x5C {
        if are_a_valid_escape(c, at(input, pos + 1)) {
            lemma_escape_advances(input, pos + 1);
            let (code_point, next) = consume_escaped_code_point(input, pos + 1);
            lemma_url_advances(input, next, value.push(code_point));
        } else {
            lemma_remnants_advance(input, pos + 1);
        }
    } else {
        lemma_url_advances(input, pos + 1, value.push(c));
    }
}

/// [`consume_a_number`] consumes at least what starts a number.
pub proof fn lemma_number_advances(input: Seq<u32>, pos: int)
    requires
        would_start_a_number(at(input, pos), at(input, pos + 1), at(input, pos + 2)),
    ensures
        consume_a_number(input, pos).1 > pos,
{
    let (signed, sign_character, after_sign) = number_step_2(input, pos);
    lemma_digits_advance(input, after_sign, signed);
    let (integer, after_integer) = consume_digits(input, after_sign, signed);
    let (number_part, no_fraction, after_fraction) = number_step_4(input, after_integer, integer);
    if at(input, after_integer) == 0x2E && is_digit(at(input, after_integer + 1)) {
        lemma_digits_advance(input, after_integer + 1, integer.push(0x2E));
    }
    let e = at(input, after_fraction);
    let second = at(input, after_fraction + 1);
    if (e == 0x45 || e == 0x65) && (is_digit(second) || ((second == 0x2D || second == 0x2B)
        && is_digit(at(input, after_fraction + 2)))) {
        let (start, after) = if second == 0x2B || second == 0x2D {
            (seq![second], after_fraction + 2)
        } else {
            (Seq::empty(), after_fraction + 1)
        };
        lemma_digits_advance(input, after, start);
    }
    // The digit that makes it a number is consumed by step 3 or by step 4.
    if is_digit(at(input, after_sign)) {
        assert(consume_digits(input, after_sign, signed) == consume_digits(
            input,
            after_sign + 1,
            signed.push(at(input, after_sign)),
        ));
        lemma_digits_advance(input, after_sign + 1, signed.push(at(input, after_sign)));
    }
}

/// [`consume_a_numeric_token`] consumes at least what starts a number.
pub proof fn lemma_numeric_token_advances(input: Seq<u32>, pos: int)
    requires
        would_start_a_number(at(input, pos), at(input, pos + 1), at(input, pos + 2)),
    ensures
        consume_a_numeric_token(input, pos).1 > pos,
{
    lemma_number_advances(input, pos);
    let (number, after) = consume_a_number(input, pos);
    lemma_ident_sequence_advances(input, after, Seq::empty());
}

/// [`consume_an_ident_like_token`] does not move backwards, and moves on from a code
/// point that consuming an ident sequence would take.
pub proof fn lemma_ident_like_token_advances(input: Seq<u32>, pos: int)
    requires
        is_ident_code_point(at(input, pos)) || are_a_valid_escape(
            at(input, pos),
            at(input, pos + 1),
        ),
    ensures
        consume_an_ident_like_token(input, pos).1 > pos,
{
    let c = at(input, pos);
    // The first step of the loop always moves on here.
    if is_ident_code_point(c) {
        lemma_ident_sequence_advances(input, pos + 1, Seq::empty().push(c));
    } else {
        lemma_escape_advances(input, pos + 1);
        let (code_point, next) = consume_escaped_code_point(input, pos + 1);
        lemma_ident_sequence_advances(input, next, Seq::empty().push(code_point));
    }
    let (string, after) = consume_ident_sequence(input, pos);
    assert(after > pos);
    if is_url(string) && at(input, after) == 0x28 {
        lemma_whitespace_but_one_advances(input, after + 1);
        let next = consume_whitespace_but_one(input, after + 1);
        lemma_whitespace_advances(input, next);
        lemma_url_advances(input, consume_whitespace(input, next), Seq::empty());
    }
}

/// [`consume_a_token`] moves on unless it returns the EOF token, which is what makes
/// tokenization end. (`theorem_tokenizer_total` states this for the crate.)
pub proof fn lemma_token_advances(input: Seq<u32>, start: int, unicode_ranges_allowed: bool)
    ensures
        !(consume_a_token(input, start, unicode_ranges_allowed).0 is Eof) ==> consume_a_token(
            input,
            start,
            unicode_ranges_allowed,
        ).1 > start,
        consume_a_token(input, start, unicode_ranges_allowed).1 >= start,
        start >= input.len() ==> consume_a_token(input, start, unicode_ranges_allowed).0 is Eof,
{
    lemma_comments_advance(input, start);
    let current = consume_comments(input, start);
    if start >= input.len() {
        assert(at(input, start) == EOF);
        assert(current == start);
    }
    let c = at(input, current);
    let pos = current + 1;
    let next = at(input, pos);
    let next2 = at(input, pos + 1);
    if is_whitespace(c) {
        lemma_whitespace_advances(input, pos);
    } else if c == 0x22 || c == 0x27 {
        lemma_string_advances(input, pos, c, Seq::empty());
    } else if c == 0x23 {
        if is_ident_code_point(next) || are_a_valid_escape(next, next2) {
            lemma_ident_sequence_advances(input, pos, Seq::empty());
        }
    } else if c == 0x2B || c == 0x2E {
        if would_start_a_number(c, next, next2) {
            lemma_numeric_token_advances(input, current);
        }
    } else if c == 0x2D {
        if would_start_a_number(c, next, next2) {
            lemma_numeric_token_advances(input, current);
        } else if !(next == 0x2D && next2 == 0x3E) && would_start_an_ident_sequence(
            c,
            next,
            next2,
        ) {
            lemma_ident_like_token_advances(input, current);
        }
    } else if c == 0x40 {
        if would_start_an_ident_sequence(next, next2, at(input, pos + 2)) {
            lemma_ident_sequence_advances(input, pos, Seq::empty());
        }
    } else if c == 0x5C {
        if are_a_valid_escape(c, next) {
            lemma_ident_like_token_advances(input, current);
        }
    } else if is_digit(c) {
        lemma_numeric_token_advances(input, current);
    } else if c == 0x55 || c == 0x75 {
        if unicode_ranges_allowed && would_start_a_unicode_range(c, next, next2) {
            lemma_hex_digits_advance(input, current + 2, 6, 0);
            let (first_segment, after_digits) = consume_hex_digits(input, current + 2, 6, 0);
            let marks = consume_question_marks(
                input,
                after_digits,
                (6 - (after_digits - (current + 2))) as nat,
            );
            let after_marks = after_digits + marks;
            lemma_hex_digits_advance(input, after_marks + 1, 6, 0);
        } else {
            lemma_ident_like_token_advances(input, current);
        }
    } else if is_ident_start_code_point(c) {
        lemma_ident_like_token_advances(input, current);
    }
}

} // verus!
