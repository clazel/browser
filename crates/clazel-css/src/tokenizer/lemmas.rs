//! Theorems about the tokenizer's spec. They are evidence that the transcription is
//! right, and what the parser relies on, not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Each call of "consume a token" consumes a code point or returns the EOF token, so
/// tokenization ends on every input.
pub proof fn theorem_tokenizer_total(input: Seq<u32>, pos: int, unicode_ranges_allowed: bool)
    ensures
        consume_a_token(input, pos, unicode_ranges_allowed).0 is Eof || consume_a_token(
            input,
            pos,
            unicode_ranges_allowed,
        ).1 > pos,
{
    super::termination::lemma_token_advances(input, pos, unicode_ranges_allowed);
}

/// [`tokenize_loop`] adds at most one token per code point left, and the EOF token, and
/// keeps what it was given.
pub proof fn lemma_loop_bounded(input: Seq<u32>, pos: int, flag: bool, tokens: Seq<Token>)
    ensures
        tokenize_loop(input, pos, flag, tokens).len() <= tokens.len() + remaining(input, pos) + 1,
        tokenize_loop(input, pos, flag, tokens).len() > tokens.len(),
        tokenize_loop(input, pos, flag, tokens).subrange(0, tokens.len() as int) == tokens,
        tokenize_loop(input, pos, flag, tokens).last() is Eof,
    decreases remaining(input, pos),
{
    super::termination::lemma_token_advances(input, pos, flag);
    let (token, next) = consume_a_token(input, pos, flag);
    if token is Eof {
        assert(tokens.push(token).subrange(0, tokens.len() as int) =~= tokens);
    } else {
        let pushed = tokens.push(token);
        lemma_loop_bounded(input, next, flag, pushed);
        let all = tokenize_loop(input, next, flag, pushed);
        assert(all.subrange(0, tokens.len() as int) =~= all.subrange(
            0,
            pushed.len() as int,
        ).subrange(0, tokens.len() as int));
        assert(pushed.subrange(0, tokens.len() as int) =~= tokens);
    }
}

/// Tokenizing gives at most one token per code point, and the EOF token, so everything
/// that walks the tokens is linear in the sheet.
pub proof fn theorem_tokens_bounded(input: Seq<u32>)
    ensures
        tokenize(input).len() <= input.len() + 1,
{
    lemma_loop_bounded(input, 0, false, Seq::empty());
}

/// The tokens always end in the EOF token, which the parser reads as the end.
pub proof fn theorem_tokens_end_in_eof(input: Seq<u32>)
    ensures
        tokenize(input).len() > 0,
        tokenize(input).last() is Eof,
{
    lemma_loop_bounded(input, 0, false, Seq::empty());
}

/// The two faces of the tokenizer agree: one step of "consume a token" and then the rest
/// is the whole, so a parser can call it "on-demand" (§4's note).
pub proof fn theorem_step_equals_whole(
    input: Seq<u32>,
    pos: int,
    unicode_ranges_allowed: bool,
    tokens: Seq<Token>,
)
    ensures
        tokenize_loop(input, pos, unicode_ranges_allowed, tokens) == ({
            let (token, next) = consume_a_token(input, pos, unicode_ranges_allowed);
            if token is Eof {
                tokens.push(token)
            } else {
                tokenize_loop(input, next, unicode_ranges_allowed, tokens.push(token))
            }
        }),
{
}


// ------------------------------------------------------------------------------------
// Nothing the tokenizer reads goes past the end of the input
// ------------------------------------------------------------------------------------

/// [`end_of_comment`] stays within the input.
pub proof fn lemma_end_of_comment_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        end_of_comment(input, pos) <= input.len(),
    decreases remaining(input, pos),
{
    if pos < input.len() && !(at(input, pos) == 0x2A && at(input, pos + 1) == 0x2F) {
        lemma_end_of_comment_within(input, pos + 1);
    }
}

/// [`consume_comments`] stays within the input.
pub proof fn lemma_comments_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_comments(input, pos) <= input.len(),
    decreases remaining(input, pos),
{
    if at(input, pos) == 0x2F && at(input, pos + 1) == 0x2A {
        lemma_end_of_comment_within(input, pos + 2);
        super::termination::lemma_end_of_comment_advances(input, pos + 2);
        lemma_comments_within(input, end_of_comment(input, pos + 2));
    }
}

/// [`consume_whitespace`] stays within the input.
pub proof fn lemma_whitespace_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_whitespace(input, pos) <= input.len(),
    decreases remaining(input, pos),
{
    if is_whitespace(at(input, pos)) {
        lemma_whitespace_within(input, pos + 1);
    }
}

/// [`consume_whitespace_but_one`] stays within the input.
pub proof fn lemma_whitespace_but_one_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_whitespace_but_one(input, pos) <= input.len(),
    decreases remaining(input, pos),
{
    if is_whitespace(at(input, pos)) && is_whitespace(at(input, pos + 1)) {
        lemma_whitespace_but_one_within(input, pos + 1);
    }
}

/// [`consume_hex_digits`] stays within the input.
pub proof fn lemma_hex_digits_within(input: Seq<u32>, pos: int, limit: nat, value: nat)
    requires
        pos <= input.len(),
    ensures
        consume_hex_digits(input, pos, limit, value).1 <= input.len(),
    decreases limit,
{
    if limit > 0 && is_hex_digit(at(input, pos)) {
        lemma_hex_digits_within(
            input,
            pos + 1,
            (limit - 1) as nat,
            value * 16 + hex_value(at(input, pos)),
        );
    }
}

/// [`consume_question_marks`] stays within the input.
pub proof fn lemma_question_marks_within(input: Seq<u32>, pos: int, limit: nat)
    requires
        pos <= input.len(),
    ensures
        pos + consume_question_marks(input, pos, limit) <= input.len(),
    decreases limit,
{
    if limit > 0 && at(input, pos) == 0x3F {
        lemma_question_marks_within(input, pos + 1, (limit - 1) as nat);
    }
}

/// [`consume_escaped_code_point`] stays within the input.
pub proof fn lemma_escape_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_escaped_code_point(input, pos).1 <= input.len(),
{
    let c = at(input, pos);
    if is_hex_digit(c) {
        lemma_hex_digits_within(input, pos + 1, 5, hex_value(c));
    }
}

/// [`consume_digits`] stays within the input.
pub proof fn lemma_digits_within(input: Seq<u32>, pos: int, part: Seq<u32>)
    requires
        pos <= input.len(),
    ensures
        consume_digits(input, pos, part).1 <= input.len(),
    decreases remaining(input, pos),
{
    if is_digit(at(input, pos)) {
        lemma_digits_within(input, pos + 1, part.push(at(input, pos)));
    }
}

/// [`consume_ident_sequence_loop`] stays within the input.
pub proof fn lemma_ident_sequence_within(input: Seq<u32>, pos: int, result: Seq<u32>)
    requires
        pos <= input.len(),
    ensures
        consume_ident_sequence_loop(input, pos, result).1 <= input.len(),
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if is_ident_code_point(c) {
        lemma_ident_sequence_within(input, pos + 1, result.push(c));
    } else if are_a_valid_escape(c, at(input, pos + 1)) {
        lemma_escape_within(input, pos + 1);
        super::termination::lemma_escape_advances(input, pos + 1);
        let (code_point, next) = consume_escaped_code_point(input, pos + 1);
        lemma_ident_sequence_within(input, next, result.push(code_point));
    }
}

/// [`consume_a_number`] stays within the input.
pub proof fn lemma_number_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_a_number(input, pos).1 <= input.len(),
{
    let (signed, sign_character, after_sign) = number_step_2(input, pos);
    lemma_digits_within(input, after_sign, signed);
    let (integer, after_integer) = consume_digits(input, after_sign, signed);
    if at(input, after_integer) == 0x2E && is_digit(at(input, after_integer + 1)) {
        lemma_digits_within(input, after_integer + 1, integer.push(0x2E));
    }
    let (number_part, no_fraction, after_fraction) = number_step_4(input, after_integer, integer);
    let e = at(input, after_fraction);
    let second = at(input, after_fraction + 1);
    if (e == 0x45 || e == 0x65) && (is_digit(second) || ((second == 0x2D || second == 0x2B)
        && is_digit(at(input, after_fraction + 2)))) {
        let (start, after) = if second == 0x2B || second == 0x2D {
            (seq![second], after_fraction + 2)
        } else {
            (Seq::empty(), after_fraction + 1)
        };
        lemma_digits_within(input, after, start);
    }
}

/// [`consume_a_numeric_token`] stays within the input.
pub proof fn lemma_numeric_token_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_a_numeric_token(input, pos).1 <= input.len(),
{
    lemma_number_within(input, pos);
    let (number, after) = consume_a_number(input, pos);
    lemma_ident_sequence_within(input, after, Seq::empty());
}

/// [`consume_string_loop`] stays within the input, if the ending code point is not EOF.
pub proof fn lemma_string_within(input: Seq<u32>, pos: int, ending: u32, value: Seq<u32>)
    requires
        pos <= input.len(),
        ending != EOF,
    ensures
        consume_string_loop(input, pos, ending, value).1 <= input.len(),
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c != ending && c != EOF && !is_newline(c) {
        if c == 0x5C {
            if at(input, pos + 1) == EOF {
                lemma_string_within(input, pos + 1, ending, value);
            } else if is_newline(at(input, pos + 1)) {
                lemma_string_within(input, pos + 2, ending, value);
            } else {
                lemma_escape_within(input, pos + 1);
                super::termination::lemma_escape_advances(input, pos + 1);
                let (code_point, next) = consume_escaped_code_point(input, pos + 1);
                lemma_string_within(input, next, ending, value.push(code_point));
            }
        } else {
            lemma_string_within(input, pos + 1, ending, value.push(c));
        }
    }
}

/// [`consume_remnants_of_a_bad_url`] stays within the input.
pub proof fn lemma_remnants_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_remnants_of_a_bad_url(input, pos) <= input.len(),
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c != 0x29 && c != EOF {
        if are_a_valid_escape(c, at(input, pos + 1)) {
            lemma_escape_within(input, pos + 1);
            super::termination::lemma_escape_advances(input, pos + 1);
            let (_, next) = consume_escaped_code_point(input, pos + 1);
            lemma_remnants_within(input, next);
        } else {
            lemma_remnants_within(input, pos + 1);
        }
    }
}

/// [`consume_url_loop`] stays within the input.
pub proof fn lemma_url_within(input: Seq<u32>, pos: int, value: Seq<u32>)
    requires
        pos <= input.len(),
    ensures
        consume_url_loop(input, pos, value).1 <= input.len(),
    decreases remaining(input, pos),
{
    let c = at(input, pos);
    if c == 0x29 || c == EOF {
    } else if is_whitespace(c) {
        lemma_whitespace_within(input, pos + 1);
        let after = consume_whitespace(input, pos + 1);
        lemma_remnants_within(input, after);
    } else if c == 0x22 || c == 0x27 || c == 0x28 || is_non_printable_code_point(c) {
        lemma_remnants_within(input, pos + 1);
    } else if c == 0x5C {
        if are_a_valid_escape(c, at(input, pos + 1)) {
            lemma_escape_within(input, pos + 1);
            super::termination::lemma_escape_advances(input, pos + 1);
            let (code_point, next) = consume_escaped_code_point(input, pos + 1);
            lemma_url_within(input, next, value.push(code_point));
        } else {
            lemma_remnants_within(input, pos + 1);
        }
    } else {
        lemma_url_within(input, pos + 1, value.push(c));
    }
}

/// [`consume_an_ident_like_token`] stays within the input.
pub proof fn lemma_ident_like_within(input: Seq<u32>, pos: int)
    requires
        pos <= input.len(),
    ensures
        consume_an_ident_like_token(input, pos).1 <= input.len(),
{
    lemma_ident_sequence_within(input, pos, Seq::empty());
    let (string, after) = consume_ident_sequence(input, pos);
    if is_url(string) && at(input, after) == 0x28 {
        lemma_whitespace_but_one_within(input, after + 1);
        let next = consume_whitespace_but_one(input, after + 1);
        lemma_whitespace_within(input, next);
        lemma_url_within(input, consume_whitespace(input, next), Seq::empty());
    }
}

/// [`consume_a_unicode_range_token`] stays within the input, from a code point that starts
/// one.
pub proof fn lemma_unicode_range_within(input: Seq<u32>, pos: int)
    requires
        pos + 2 <= input.len(),
    ensures
        consume_a_unicode_range_token(input, pos).1 <= input.len(),
{
    let start = pos + 2;
    lemma_hex_digits_within(input, start, 6, 0);
    super::termination::lemma_hex_digits_advance(input, start, 6, 0);
    let (first_segment, after_digits) = consume_hex_digits(input, start, 6, 0);
    lemma_question_marks_within(
        input,
        after_digits,
        (6 - (after_digits - start)) as nat,
    );
    let marks = consume_question_marks(input, after_digits, (6 - (after_digits - start)) as nat);
    let after_marks = after_digits + marks;
    if marks == 0 && at(input, after_marks) == 0x2D && is_hex_digit(at(input, after_marks + 1)) {
        lemma_hex_digits_within(input, after_marks + 1, 6, 0);
    }
}

/// [`consume_a_token`] from a position in the input, which is every one a stream reads
/// from, ends in the input. The EOF code point inside the input acts as the end, so
/// this holds for every string of `u32`, not only for code points.
#[verifier::rlimit(200)]
pub proof fn lemma_token_within(input: Seq<u32>, start: int, unicode_ranges_allowed: bool)
    requires
        start <= input.len(),
    ensures
        consume_a_token(input, start, unicode_ranges_allowed).1 <= input.len(),
{
    lemma_comments_within(input, start);
    let current = consume_comments(input, start);
    let c = at(input, current);
    let pos = current + 1;
    let next = at(input, pos);
    let next2 = at(input, pos + 1);
    if is_whitespace(c) {
        lemma_whitespace_within(input, pos);
    } else if c == 0x22 || c == 0x27 {
        lemma_string_within(input, pos, c, Seq::empty());
    } else if c == 0x23 {
        lemma_ident_sequence_within(input, pos, Seq::empty());
    } else if c == 0x2B || c == 0x2E {
        lemma_numeric_token_within(input, current);
    } else if c == 0x2D {
        lemma_numeric_token_within(input, current);
        lemma_ident_like_within(input, current);
    } else if c == 0x40 {
        lemma_ident_sequence_within(input, pos, Seq::empty());
    } else if c == 0x5C {
        lemma_ident_like_within(input, current);
    } else if is_digit(c) {
        lemma_numeric_token_within(input, current);
    } else if c == 0x55 || c == 0x75 {
        lemma_ident_like_within(input, current);
        if unicode_ranges_allowed && would_start_a_unicode_range(c, next, next2) {
            lemma_unicode_range_within(input, current);
        }
    } else if is_ident_start_code_point(c) {
        lemma_ident_like_within(input, current);
    }
}

} // verus!
