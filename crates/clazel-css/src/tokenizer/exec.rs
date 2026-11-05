//! The executable tokenizer, proven to meet [`super::contract`]. Each `read_` function is
//! one algorithm of [`super::spec`] as a loop, with no recursion: a style sheet is what a
//! page chose, and Verus proves no panics, not no stack overflow.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`Number`], in memory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecNumber {
    /// [`Number::number_part`].
    pub number_part: Vec<u32>,
    /// [`Number::exponent_part`].
    pub exponent_part: Vec<u32>,
    /// [`Number::is_integer`].
    pub is_integer: bool,
    /// [`Number::sign_character`].
    pub sign_character: Option<u32>,
}

/// [`Token`], in memory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecToken {
    /// [`Token::Ident`].
    Ident {
        /// The value.
        value: Vec<u32>,
    },
    /// [`Token::Function`].
    Function {
        /// The value.
        value: Vec<u32>,
    },
    /// [`Token::AtKeyword`].
    AtKeyword {
        /// The value.
        value: Vec<u32>,
    },
    /// [`Token::Hash`].
    Hash {
        /// The value.
        value: Vec<u32>,
        /// The type flag: true for "id", false for "unrestricted".
        is_id: bool,
    },
    /// [`Token::String`].
    String {
        /// The value.
        value: Vec<u32>,
    },
    /// [`Token::BadString`].
    BadString,
    /// [`Token::Url`].
    Url {
        /// The value.
        value: Vec<u32>,
    },
    /// [`Token::BadUrl`].
    BadUrl,
    /// [`Token::Delim`].
    Delim {
        /// The value.
        value: u32,
    },
    /// [`Token::Number`].
    Number {
        /// The number.
        number: ExecNumber,
    },
    /// [`Token::Percentage`].
    Percentage {
        /// The number.
        number: ExecNumber,
    },
    /// [`Token::Dimension`].
    Dimension {
        /// The number.
        number: ExecNumber,
        /// The unit.
        unit: Vec<u32>,
    },
    /// [`Token::UnicodeRange`].
    UnicodeRange {
        /// The starting code point.
        start: u32,
        /// The ending code point.
        end: u32,
    },
    /// [`Token::Whitespace`].
    Whitespace,
    /// [`Token::Cdo`].
    Cdo,
    /// [`Token::Cdc`].
    Cdc,
    /// [`Token::Colon`].
    Colon,
    /// [`Token::Semicolon`].
    Semicolon,
    /// [`Token::Comma`].
    Comma,
    /// [`Token::OpenSquare`].
    OpenSquare,
    /// [`Token::CloseSquare`].
    CloseSquare,
    /// [`Token::OpenParen`].
    OpenParen,
    /// [`Token::CloseParen`].
    CloseParen,
    /// [`Token::OpenCurly`].
    OpenCurly,
    /// [`Token::CloseCurly`].
    CloseCurly,
    /// [`Token::Eof`].
    Eof,
}

/// The number an [`ExecNumber`] holds.
pub open spec fn view_number(number: ExecNumber) -> Number {
    Number {
        number_part: number.number_part@,
        exponent_part: number.exponent_part@,
        is_integer: number.is_integer,
        sign_character: number.sign_character,
    }
}

/// The token an [`ExecToken`] holds.
pub open spec fn view_token(token: ExecToken) -> Token {
    match token {
        ExecToken::Ident { value } => Token::Ident { value: value@ },
        ExecToken::Function { value } => Token::Function { value: value@ },
        ExecToken::AtKeyword { value } => Token::AtKeyword { value: value@ },
        ExecToken::Hash { value, is_id } => Token::Hash { value: value@, is_id },
        ExecToken::String { value } => Token::String { value: value@ },
        ExecToken::BadString => Token::BadString,
        ExecToken::Url { value } => Token::Url { value: value@ },
        ExecToken::BadUrl => Token::BadUrl,
        ExecToken::Delim { value } => Token::Delim { value },
        ExecToken::Number { number } => Token::Number { number: view_number(number) },
        ExecToken::Percentage { number } => Token::Percentage { number: view_number(number) },
        ExecToken::Dimension { number, unit } => Token::Dimension {
            number: view_number(number),
            unit: unit@,
        },
        ExecToken::UnicodeRange { start, end } => Token::UnicodeRange {
            start: start as nat,
            end: end as nat,
        },
        ExecToken::Whitespace => Token::Whitespace,
        ExecToken::Cdo => Token::Cdo,
        ExecToken::Cdc => Token::Cdc,
        ExecToken::Colon => Token::Colon,
        ExecToken::Semicolon => Token::Semicolon,
        ExecToken::Comma => Token::Comma,
        ExecToken::OpenSquare => Token::OpenSquare,
        ExecToken::CloseSquare => Token::CloseSquare,
        ExecToken::OpenParen => Token::OpenParen,
        ExecToken::CloseParen => Token::CloseParen,
        ExecToken::OpenCurly => Token::OpenCurly,
        ExecToken::CloseCurly => Token::CloseCurly,
        ExecToken::Eof => Token::Eof,
    }
}

/// The tokens a slice holds.
pub open spec fn view_tokens(tokens: Seq<ExecToken>) -> Seq<Token> {
    tokens.map_values(|token: ExecToken| view_token(token))
}

/// The code point at `i`, or EOF.
pub fn peek(input: &[u32], i: usize) -> (c: u32)
    ensures
        c == at(input@, i as int),
{
    match input.get(i) {
        Some(c) => *c,
        None => EOF,
    }
}

/// True if `c` is between `low` and `high` inclusive.
fn between(c: u32, low: u32, high: u32) -> (r: bool)
    ensures
        r == (low <= c <= high),
{
    low <= c && c <= high
}

fn digit(c: u32) -> (r: bool)
    ensures
        r == is_digit(c),
{
    between(c, 0x30, 0x39)
}

fn hex_digit(c: u32) -> (r: bool)
    ensures
        r == is_hex_digit(c),
{
    digit(c) || between(c, 0x41, 0x46) || between(c, 0x61, 0x66)
}

fn ident_start_code_point(c: u32) -> (r: bool)
    ensures
        r == is_ident_start_code_point(c),
{
    between(c, 0x41, 0x5A) || between(c, 0x61, 0x7A) || c == 0xB7 || between(c, 0xC0, 0xD6)
        || between(c, 0xD8, 0xF6) || between(c, 0xF8, 0x37D) || between(c, 0x37F, 0x1FFF)
        || c == 0x200C || c == 0x200D || c == 0x203F || c == 0x2040 || between(c, 0x2070, 0x218F)
        || between(c, 0x2C00, 0x2FEF) || between(c, 0x3001, 0xD7FF) || between(c, 0xF900, 0xFDCF) || between(c, 0xFDF0, 0xFFFD) || between(c, 0x1_0000, 0x10_FFFF) || c == 0x5F
}

fn ident_code_point(c: u32) -> (r: bool)
    ensures
        r == is_ident_code_point(c),
{
    ident_start_code_point(c) || digit(c) || c == 0x2D
}

fn non_printable_code_point(c: u32) -> (r: bool)
    ensures
        r == is_non_printable_code_point(c),
{
    c <= 0x08 || c == 0x0B || between(c, 0x0E, 0x1F) || c == 0x7F
}

fn whitespace(c: u32) -> (r: bool)
    ensures
        r == is_whitespace(c),
{
    c == 0x0A || c == 0x09 || c == 0x20
}

fn valid_escape(first: u32, second: u32) -> (r: bool)
    ensures
        r == are_a_valid_escape(first, second),
{
    first == 0x5C && second != 0x0A
}

fn starts_ident_sequence(first: u32, second: u32, third: u32) -> (r: bool)
    ensures
        r == would_start_an_ident_sequence(first, second, third),
{
    if first == 0x2D {
        ident_start_code_point(second) || second == 0x2D || valid_escape(second, third)
    } else if ident_start_code_point(first) {
        true
    } else if first == 0x5C {
        valid_escape(first, second)
    } else {
        false
    }
}

fn starts_number(first: u32, second: u32, third: u32) -> (r: bool)
    ensures
        r == would_start_a_number(first, second, third),
{
    if first == 0x2B || first == 0x2D {
        digit(second) || (second == 0x2E && digit(third))
    } else if first == 0x2E {
        digit(second)
    } else {
        digit(first)
    }
}

fn starts_unicode_range(first: u32, second: u32, third: u32) -> (r: bool)
    ensures
        r == would_start_a_unicode_range(first, second, third),
{
    (first == 0x55 || first == 0x75) && second == 0x2B && (third == 0x3F || hex_digit(third))
}

/// Contract for `filter_code_points`: §3.3.
pub fn filter(input: &[u32]) -> (output: Vec<u32>)
    requires
        super::contract::input_requires(input@),
    ensures
        super::contract::filter_ensures(input@, output@),
{
    let mut output: Vec<u32> = Vec::new();
    let mut pos: usize = 0;
    loop
        invariant
            super::contract::input_requires(input@),
            pos <= input.len(),
            filter_loop(input@, pos as int, output@) == filter_code_points(input@),
        decreases input.len() - pos,
    {
        if pos >= input.len() {
            return output;
        }
        let c = peek(input, pos);
        // Never saturates here or below: the input's length leaves room.
        if c == 0x0D && peek(input, pos.saturating_add(1)) == 0x0A {
            output.push(0x0A);
            pos = pos.saturating_add(2);
        } else if c == 0x0D || c == 0x0C {
            output.push(0x0A);
            pos = pos.saturating_add(1);
        } else if c == 0 || between(c, 0xD800, 0xDFFF) {
            output.push(REPLACEMENT);
            pos = pos.saturating_add(1);
        } else {
            output.push(c);
            pos = pos.saturating_add(1);
        }
    }
}

/// [`end_of_comment`].
fn read_end_of_comment(input: &[u32], start: usize) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        r as int == end_of_comment(input@, start as int),
        start <= r <= input.len(),
{
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            end_of_comment(input@, pos as int) == end_of_comment(input@, start as int),
        decreases input.len() - pos,
    {
        if pos >= input.len() {
            return pos;
        }
        if peek(input, pos) == 0x2A && peek(input, pos.saturating_add(1)) == 0x2F {
            return pos.saturating_add(2);
        }
        pos = pos.saturating_add(1);
    }
}

/// [`consume_comments`].
pub fn read_comments(input: &[u32], start: usize) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        r as int == consume_comments(input@, start as int),
        start <= r <= input.len(),
{
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            consume_comments(input@, pos as int) == consume_comments(input@, start as int),
        decreases input.len() - pos,
    {
        if peek(input, pos) == 0x2F && peek(input, pos.saturating_add(1)) == 0x2A {
            pos = read_end_of_comment(input, pos.saturating_add(2));
        } else {
            return pos;
        }
    }
}

/// [`consume_whitespace`].
fn read_whitespace(input: &[u32], start: usize) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        r as int == consume_whitespace(input@, start as int),
        start <= r <= input.len(),
{
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            consume_whitespace(input@, pos as int) == consume_whitespace(input@, start as int),
        decreases input.len() - pos,
    {
        if whitespace(peek(input, pos)) {
            pos = pos.saturating_add(1);
        } else {
            return pos;
        }
    }
}

/// The value of a hex digit.
fn hex_digit_value(c: u32) -> (r: u32)
    requires
        is_hex_digit(c),
    ensures
        r as nat == hex_value(c),
        r < 16,
{
    if digit(c) {
        c.saturating_sub(0x30)
    } else if between(c, 0x41, 0x46) {
        c.saturating_sub(0x41).saturating_add(10)
    } else {
        c.saturating_sub(0x61).saturating_add(10)
    }
}

/// What a value can be with `limit` of six hex digits still to come: 16 to the power of
/// the digits it has had.
pub open spec fn hex_bound(limit: int) -> nat {
    if limit >= 6 {
        1
    } else if limit == 5 {
        0x10
    } else if limit == 4 {
        0x100
    } else if limit == 3 {
        0x1000
    } else if limit == 2 {
        0x1_0000
    } else if limit == 1 {
        0x10_0000
    } else {
        0x100_0000
    }
}

/// [`consume_hex_digits`].
fn read_hex_digits(input: &[u32], start: usize, limit: usize, value: u32) -> (r: (u32, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
        limit <= 6,
        value < hex_bound(limit as int),
    ensures
        (r.0 as nat, r.1 as int) == consume_hex_digits(
            input@,
            start as int,
            limit as nat,
            value as nat,
        ),
        start <= r.1 <= input.len(),
        r.1 - start <= limit,
        r.0 < hex_bound(limit - (r.1 - start)),
{
    let mut pos = start;
    let mut left = limit;
    let mut number = value;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            left <= limit <= 6,
            pos - start == limit - left,
            number < hex_bound(left as int),
            consume_hex_digits(input@, pos as int, left as nat, number as nat)
                == consume_hex_digits(input@, start as int, limit as nat, value as nat),
        decreases left,
    {
        if left > 0 && hex_digit(peek(input, pos)) {
            let d = hex_digit_value(peek(input, pos));
            assert(number * 16 + d < hex_bound(left - 1));
            number = number.saturating_mul(16).saturating_add(d);
            left = left.saturating_sub(1);
            pos = pos.saturating_add(1);
        } else {
            return (number, pos);
        }
    }
}

/// [`consume_escaped_code_point`].
fn read_escape(input: &[u32], pos: usize) -> (r: (u32, usize))
    requires
        super::contract::input_requires(input@),
        pos <= input.len(),
    ensures
        (r.0, r.1 as int) == consume_escaped_code_point(input@, pos as int),
        pos <= r.1 <= input.len(),
{
    let c = peek(input, pos);
    if hex_digit(c) {
        let (number, after) = read_hex_digits(
            input,
            pos.saturating_add(1),
            5,
            hex_digit_value(c),
        );
        let end = if whitespace(peek(input, after)) {
            after.saturating_add(1)
        } else {
            after
        };
        if number == 0 || between(number, 0xD800, 0xDFFF) || number
            > MAXIMUM_ALLOWED_CODE_POINT {
            (REPLACEMENT, end)
        } else {
            (number, end)
        }
    } else if c == EOF {
        (REPLACEMENT, pos)
    } else {
        (c, pos.saturating_add(1))
    }
}

/// [`consume_ident_sequence`].
fn read_ident_sequence(input: &[u32], start: usize) -> (r: (Vec<u32>, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        (r.0@, r.1 as int) == consume_ident_sequence(input@, start as int),
        start <= r.1 <= input.len(),
{
    let mut result: Vec<u32> = Vec::new();
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            consume_ident_sequence_loop(input@, pos as int, result@) == consume_ident_sequence(
                input@,
                start as int,
            ),
        decreases input.len() - pos,
    {
        let c = peek(input, pos);
        if ident_code_point(c) {
            result.push(c);
            pos = pos.saturating_add(1);
        } else if valid_escape(c, peek(input, pos.saturating_add(1))) {
            let (code_point, next) = read_escape(input, pos.saturating_add(1));
            result.push(code_point);
            pos = next;
        } else {
            return (result, pos);
        }
    }
}

/// [`consume_digits`], appending to `part`.
fn read_digits(input: &[u32], start: usize, part: &mut Vec<u32>) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        (final(part)@, r as int) == consume_digits(input@, start as int, old(part)@),
        start <= r <= input.len(),
{
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            consume_digits(input@, pos as int, part@) == consume_digits(
                input@,
                start as int,
                old(part)@,
            ),
        decreases input.len() - pos,
    {
        let c = peek(input, pos);
        if digit(c) {
            part.push(c);
            pos = pos.saturating_add(1);
        } else {
            return pos;
        }
    }
}

/// [`consume_a_number`].
fn read_number(input: &[u32], start: usize) -> (r: (ExecNumber, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        (view_number(r.0), r.1 as int) == consume_a_number(input@, start as int),
        start <= r.1 <= input.len(),
{
    // 2.
    let first = peek(input, start);
    let mut signed: Vec<u32> = Vec::new();
    let mut sign_character: Option<u32> = None;
    let mut after_sign = start;
    if first == 0x2B || first == 0x2D {
        signed.push(first);
        assert(signed@ =~= seq![first]);
        sign_character = Some(first);
        after_sign = start.saturating_add(1);
    } else {
        assert(signed@ =~= Seq::<u32>::empty());
    }
    // 3.
    let mut number_part = signed;
    let after_integer = read_digits(input, after_sign, &mut number_part);
    // 4.
    let mut no_fraction = true;
    let mut after_fraction = after_integer;
    if peek(input, after_integer) == 0x2E && digit(peek(input, after_integer.saturating_add(1))) {
        number_part.push(0x2E);
        after_fraction = read_digits(input, after_integer.saturating_add(1), &mut number_part);
        no_fraction = false;
    }
    // 5.
    let e = peek(input, after_fraction);
    let second = peek(input, after_fraction.saturating_add(1));
    let mut exponent_part: Vec<u32> = Vec::new();
    let mut has_exponent = false;
    let mut end = after_fraction;
    if (e == 0x45 || e == 0x65) && (digit(second) || ((second == 0x2D || second == 0x2B) && digit(
        peek(input, after_fraction.saturating_add(2)),
    ))) {
        let mut after = after_fraction.saturating_add(1);
        if second == 0x2B || second == 0x2D {
            exponent_part.push(second);
            assert(exponent_part@ =~= seq![second]);
            after = after_fraction.saturating_add(2);
        } else {
            assert(exponent_part@ =~= Seq::<u32>::empty());
        }
        end = read_digits(input, after, &mut exponent_part);
        has_exponent = true;
    } else {
        assert(exponent_part@ =~= Seq::<u32>::empty());
    }
    // 7.
    (
        ExecNumber {
            number_part,
            exponent_part,
            is_integer: no_fraction && !has_exponent,
            sign_character,
        },
        end,
    )
}

/// [`consume_a_numeric_token`].
fn read_numeric_token(input: &[u32], start: usize) -> (r: (ExecToken, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        (view_token(r.0), r.1 as int) == consume_a_numeric_token(input@, start as int),
        start <= r.1 <= input.len(),
{
    let (number, after) = read_number(input, start);
    if starts_ident_sequence(
        peek(input, after),
        peek(input, after.saturating_add(1)),
        peek(input, after.saturating_add(2)),
    ) {
        let (unit, end) = read_ident_sequence(input, after);
        (ExecToken::Dimension { number, unit }, end)
    } else if peek(input, after) == 0x25 {
        (ExecToken::Percentage { number }, after.saturating_add(1))
    } else {
        (ExecToken::Number { number }, after)
    }
}

/// [`consume_a_string_token`].
fn read_string_token(input: &[u32], start: usize, ending: u32) -> (r: (ExecToken, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
        ending != EOF,
    ensures
        (view_token(r.0), r.1 as int) == consume_a_string_token(input@, start as int, ending),
        start <= r.1 <= input.len(),
{
    let mut value: Vec<u32> = Vec::new();
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            ending != EOF,
            consume_string_loop(input@, pos as int, ending, value@) == consume_a_string_token(
                input@,
                start as int,
                ending,
            ),
        decreases input.len() - pos,
    {
        let c = peek(input, pos);
        if c == ending {
            return (ExecToken::String { value }, pos.saturating_add(1));
        } else if c == EOF {
            return (ExecToken::String { value }, pos);
        } else if c == 0x0A {
            return (ExecToken::BadString, pos);
        } else if c == 0x5C {
            let next = peek(input, pos.saturating_add(1));
            if next == EOF {
                pos = pos.saturating_add(1);
            } else if next == 0x0A {
                pos = pos.saturating_add(2);
            } else {
                let (code_point, after) = read_escape(input, pos.saturating_add(1));
                value.push(code_point);
                pos = after;
            }
        } else {
            value.push(c);
            pos = pos.saturating_add(1);
        }
    }
}

/// [`consume_remnants_of_a_bad_url`].
fn read_remnants_of_a_bad_url(input: &[u32], start: usize) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        r as int == consume_remnants_of_a_bad_url(input@, start as int),
        start <= r <= input.len(),
{
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            consume_remnants_of_a_bad_url(input@, pos as int) == consume_remnants_of_a_bad_url(
                input@,
                start as int,
            ),
        decreases input.len() - pos,
    {
        let c = peek(input, pos);
        if c == 0x29 {
            return pos.saturating_add(1);
        } else if c == EOF {
            return pos;
        } else if valid_escape(c, peek(input, pos.saturating_add(1))) {
            let (_, next) = read_escape(input, pos.saturating_add(1));
            pos = next;
        } else {
            pos = pos.saturating_add(1);
        }
    }
}

/// [`consume_a_url_token`].
fn read_url_token(input: &[u32], start: usize) -> (r: (ExecToken, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        (view_token(r.0), r.1 as int) == consume_a_url_token(input@, start as int),
        start <= r.1 <= input.len(),
{
    let mut value: Vec<u32> = Vec::new();
    let first = read_whitespace(input, start);
    let mut pos = first;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= first <= pos <= input.len(),
            first as int == consume_whitespace(input@, start as int),
            consume_url_loop(input@, pos as int, value@) == consume_a_url_token(
                input@,
                start as int,
            ),
        decreases input.len() - pos,
    {
        let c = peek(input, pos);
        if c == 0x29 {
            return (ExecToken::Url { value }, pos.saturating_add(1));
        } else if c == EOF {
            return (ExecToken::Url { value }, pos);
        } else if whitespace(c) {
            let after = read_whitespace(input, pos.saturating_add(1));
            let next = peek(input, after);
            if next == 0x29 {
                return (ExecToken::Url { value }, after.saturating_add(1));
            } else if next == EOF {
                return (ExecToken::Url { value }, after);
            } else {
                return (ExecToken::BadUrl, read_remnants_of_a_bad_url(input, after));
            }
        } else if c == 0x22 || c == 0x27 || c == 0x28 || non_printable_code_point(c) {
            return (
                ExecToken::BadUrl,
                read_remnants_of_a_bad_url(input, pos.saturating_add(1)),
            );
        } else if c == 0x5C {
            if valid_escape(c, peek(input, pos.saturating_add(1))) {
                let (code_point, next) = read_escape(input, pos.saturating_add(1));
                value.push(code_point);
                pos = next;
            } else {
                return (
                    ExecToken::BadUrl,
                    read_remnants_of_a_bad_url(input, pos.saturating_add(1)),
                );
            }
        } else {
            value.push(c);
            pos = pos.saturating_add(1);
        }
    }
}

/// [`consume_whitespace_but_one`].
fn read_whitespace_but_one(input: &[u32], start: usize) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        r as int == consume_whitespace_but_one(input@, start as int),
        start <= r <= input.len(),
{
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            consume_whitespace_but_one(input@, pos as int) == consume_whitespace_but_one(
                input@,
                start as int,
            ),
        decreases input.len() - pos,
    {
        if whitespace(peek(input, pos)) && whitespace(peek(input, pos.saturating_add(1))) {
            pos = pos.saturating_add(1);
        } else {
            return pos;
        }
    }
}

/// [`is_url`].
fn url_name(string: &Vec<u32>) -> (r: bool)
    ensures
        r == is_url(string@),
{
    if string.len() != 3 {
        return false;
    }
    let a = peek(string.as_slice(), 0);
    let b = peek(string.as_slice(), 1);
    let c = peek(string.as_slice(), 2);
    (a == 0x55 || a == 0x75) && (b == 0x52 || b == 0x72) && (c == 0x4C || c == 0x6C)
}

fn quote(c: u32) -> (r: bool)
    ensures
        r == is_quote(c),
{
    c == 0x22 || c == 0x27
}

/// [`consume_an_ident_like_token`].
fn read_ident_like_token(input: &[u32], start: usize) -> (r: (ExecToken, usize))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        (view_token(r.0), r.1 as int) == consume_an_ident_like_token(input@, start as int),
        start <= r.1 <= input.len(),
{
    let (string, after) = read_ident_sequence(input, start);
    if url_name(&string) && peek(input, after) == 0x28 {
        let next = read_whitespace_but_one(input, after.saturating_add(1));
        if quote(peek(input, next)) || (whitespace(peek(input, next)) && quote(
            peek(input, next.saturating_add(1)),
        )) {
            (ExecToken::Function { value: string }, next)
        } else {
            read_url_token(input, next)
        }
    } else if peek(input, after) == 0x28 {
        (ExecToken::Function { value: string }, after.saturating_add(1))
    } else {
        (ExecToken::Ident { value: string }, after)
    }
}

/// [`consume_question_marks`].
fn read_question_marks(input: &[u32], start: usize, limit: usize) -> (r: usize)
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
        limit <= 6,
    ensures
        r as nat == consume_question_marks(input@, start as int, limit as nat),
        r <= limit,
        start + r <= input.len(),
{
    let mut count: usize = 0;
    let mut pos = start;
    loop
        invariant
            super::contract::input_requires(input@),
            start <= pos <= input.len(),
            count <= limit <= 6,
            pos == start + count,
            count + consume_question_marks(input@, pos as int, (limit - count) as nat)
                == consume_question_marks(input@, start as int, limit as nat),
        decreases limit - count,
    {
        if count < limit && peek(input, pos) == 0x3F {
            count = count.saturating_add(1);
            pos = pos.saturating_add(1);
        } else {
            return count;
        }
    }
}

/// [`with_digits`].
fn replace_marks(value: u32, count: usize, digit_value: u32) -> (r: u32)
    requires
        count <= 6,
        digit_value <= 15,
        value < hex_bound(count as int),
    ensures
        r as nat == with_digits(value as nat, count as nat, digit_value as nat),
        r < 0x100_0000,
{
    let mut result = value;
    let mut left = count;
    loop
        invariant
            left <= 6,
            digit_value <= 15,
            result < hex_bound(left as int),
            with_digits(result as nat, left as nat, digit_value as nat) == with_digits(
                value as nat,
                count as nat,
                digit_value as nat,
            ),
        decreases left,
    {
        if left == 0 {
            return result;
        }
        assert(result * 16 + digit_value < hex_bound(left - 1));
        result = result.saturating_mul(16).saturating_add(digit_value);
        left = left.saturating_sub(1);
    }
}

/// [`consume_a_unicode_range_token`].
fn read_unicode_range_token(input: &[u32], pos: usize) -> (r: (ExecToken, usize))
    requires
        super::contract::input_requires(input@),
        pos + 2 <= input.len(),
    ensures
        (view_token(r.0), r.1 as int) == consume_a_unicode_range_token(input@, pos as int),
        pos <= r.1 <= input.len(),
{
    let start = pos.saturating_add(2);
    let (first_segment, after_digits) = read_hex_digits(input, start, 6, 0);
    let left = 6usize.saturating_sub(after_digits.saturating_sub(start));
    let marks = read_question_marks(input, after_digits, left);
    let after_marks = after_digits.saturating_add(marks);
    if marks > 0 {
        assert(first_segment < hex_bound(marks as int));
        (
            ExecToken::UnicodeRange {
                start: replace_marks(first_segment, marks, 0),
                end: replace_marks(first_segment, marks, 15),
            },
            after_marks,
        )
    } else if peek(input, after_marks) == 0x2D && hex_digit(
        peek(input, after_marks.saturating_add(1)),
    ) {
        let (end_of_range, end) = read_hex_digits(input, after_marks.saturating_add(1), 6, 0);
        (ExecToken::UnicodeRange { start: first_segment, end: end_of_range }, end)
    } else {
        (ExecToken::UnicodeRange { start: first_segment, end: first_segment }, after_marks)
    }
}

/// Contract for `next_token`: "consume a token" at `start`. Returns the token and the
/// position after it.
pub fn next_token(input: &[u32], start: usize, unicode_ranges_allowed: bool) -> (r: (
    ExecToken,
    usize,
))
    requires
        super::contract::input_requires(input@),
        start <= input.len(),
    ensures
        super::contract::next_token_ensures(
            input@,
            start as int,
            unicode_ranges_allowed,
            view_token(r.0),
            r.1 as int,
        ),
        start <= r.1 <= input.len(),
{
    let current = read_comments(input, start);
    let c = peek(input, current);
    let pos = current.saturating_add(1);
    let next = peek(input, pos);
    let next2 = peek(input, pos.saturating_add(1));
    if whitespace(c) {
        (ExecToken::Whitespace, read_whitespace(input, pos))
    } else if c == 0x22 {
        read_string_token(input, pos, c)
    } else if c == 0x23 {
        if ident_code_point(next) || valid_escape(next, next2) {
            let is_id = starts_ident_sequence(next, next2, peek(input, pos.saturating_add(2)));
            let (value, end) = read_ident_sequence(input, pos);
            (ExecToken::Hash { value, is_id }, end)
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x27 {
        read_string_token(input, pos, c)
    } else if c == 0x28 {
        (ExecToken::OpenParen, pos)
    } else if c == 0x29 {
        (ExecToken::CloseParen, pos)
    } else if c == 0x2B {
        if starts_number(c, next, next2) {
            read_numeric_token(input, current)
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x2C {
        (ExecToken::Comma, pos)
    } else if c == 0x2D {
        if starts_number(c, next, next2) {
            read_numeric_token(input, current)
        } else if next == 0x2D && next2 == 0x3E {
            (ExecToken::Cdc, pos.saturating_add(2))
        } else if starts_ident_sequence(c, next, next2) {
            read_ident_like_token(input, current)
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x2E {
        if starts_number(c, next, next2) {
            read_numeric_token(input, current)
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x3A {
        (ExecToken::Colon, pos)
    } else if c == 0x3B {
        (ExecToken::Semicolon, pos)
    } else if c == 0x3C {
        if next == 0x21 && next2 == 0x2D && peek(input, pos.saturating_add(2)) == 0x2D {
            (ExecToken::Cdo, pos.saturating_add(3))
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x40 {
        if starts_ident_sequence(next, next2, peek(input, pos.saturating_add(2))) {
            let (value, end) = read_ident_sequence(input, pos);
            (ExecToken::AtKeyword { value }, end)
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x5B {
        (ExecToken::OpenSquare, pos)
    } else if c == 0x5C {
        if valid_escape(c, next) {
            read_ident_like_token(input, current)
        } else {
            (ExecToken::Delim { value: c }, pos)
        }
    } else if c == 0x5D {
        (ExecToken::CloseSquare, pos)
    } else if c == 0x7B {
        (ExecToken::OpenCurly, pos)
    } else if c == 0x7D {
        (ExecToken::CloseCurly, pos)
    } else if digit(c) {
        read_numeric_token(input, current)
    } else if c == 0x55 || c == 0x75 {
        if unicode_ranges_allowed && starts_unicode_range(c, next, next2) {
            read_unicode_range_token(input, current)
        } else {
            read_ident_like_token(input, current)
        }
    } else if ident_start_code_point(c) {
        read_ident_like_token(input, current)
    } else if c == EOF {
        (ExecToken::Eof, current)
    } else {
        (ExecToken::Delim { value: c }, pos)
    }
}

/// Contract for `tokenize`: repeatedly "consume a token", up to and including the EOF
/// token.
pub fn tokenize_all(input: &[u32]) -> (tokens: Vec<ExecToken>)
    requires
        super::contract::input_requires(input@),
    ensures
        super::contract::tokenize_ensures(input@, view_tokens(tokens@)),
{
    let mut tokens: Vec<ExecToken> = Vec::new();
    let mut pos: usize = 0;
    assert(view_tokens(tokens@) =~= Seq::<Token>::empty());
    loop
        invariant
            super::contract::input_requires(input@),
            pos <= input.len(),
            tokenize_loop(input@, pos as int, false, view_tokens(tokens@)) == tokenize(input@),
        decreases input.len() - pos,
    {
        let (token, next) = next_token(input, pos, false);
        proof {
            super::termination::lemma_token_advances(input@, pos as int, false);
        }
        let ghost before = tokens@;
        let is_eof = matches!(token, ExecToken::Eof);
        tokens.push(token);
        assert(view_tokens(tokens@) =~= view_tokens(before).push(view_token(token)));
        if is_eof {
            return tokens;
        }
        pos = next;
    }
}

} // verus!
