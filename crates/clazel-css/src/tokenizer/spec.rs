//! Executable-style specification of CSS tokenization, transcribed from CSS Syntax
//! Module Level 3. Nothing here runs; it defines what "correct" means.
//!
//! Source: CSS Syntax Module Level 3, Editor's Draft, `css-syntax-3/Overview.bs` of
//! `w3c/csswg-drafts` at commit `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`
//! (2026-10-20), <https://drafts.csswg.org/css-syntax-3/>. Each function cites its
//! section by anchor. The algorithms' steps are mostly unnumbered prose and
//! definition lists, so a `// "…"` comment quotes the branch it stands for, and
//! `// N.` is used where the text numbers its steps.
//!
//! Modelling choices (each one a deliberate difference in form, never in meaning):
//! - The input stream is `input: Seq<u32>` plus a position, after [`filter_code_points`].
//!   "Consume the next input code point" moves the position on, and "reconsume the
//!   current input code point" is not moving it, since what is pushed back is exactly
//!   what was just read.
//! - The EOF code point is [`EOF`], a value above U+10FFFF, which [`at`] gives past
//!   either end. "Conceptual", in the text's word, so it is never in `input`. Consuming
//!   it does not move the position, so an algorithm that consumes EOF and returns
//!   leaves the position at the end. A value above U+10FFFF in `input` would act as
//!   EOF; [`filter_code_points`]'s input is a stream of code points, so none occurs.
//! - For the same reason "non-ASCII ident code point"'s last range, "greater than or
//!   equal to U+10000", is bounded by the maximum allowed code point.
//! - Each algorithm is a function of the input and a position that returns its result
//!   and the position after it. "Repeatedly consume" is a recursive function, named
//!   for the algorithm with `_loop`, that carries what the text builds up.
//! - A numeric token keeps [`Number`], the strings "consume a number" builds, instead
//!   of a value, so the spec has no floats. [`number_value`] is the exact rational
//!   they mean ("interpreting … as a base-10 number"). `clazel-style` rounds it, once.
//! - A percentage token keeps the type flag with the rest of [`Number`]. The text
//!   drops it, and nothing here reads it there.
//! - A number's sign is in its [`Number::number_part`], as the text builds it, and in
//!   [`Number::sign_character`].
//! - Parse errors change nothing about what is returned, so they are not modelled.
//! - "Consume a token"'s optional "unicode ranges allowed" is an explicit argument.
//!   [`tokenize`] passes false, the text's default.
//! - "Replace…" in [`filter_code_points`] is one pass over the input for both of the
//!   text's bullets. The first produces only U+000A and the second only U+FFFD, neither
//!   of which either bullet replaces, so the order does not matter.
//! - The "ending code point" of "consume a string token" is an argument. The text
//!   defaults it to the current input code point, and every call here passes that.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The EOF code point (§4.2): a conceptual code point above every real one.
pub const EOF: u32 = 0x11_0000;

/// U+FFFD REPLACEMENT CHARACTER.
pub const REPLACEMENT: u32 = 0xFFFD;

/// The code point at `i`, or EOF. "Whenever the input stream is empty, the next input
/// code point is always an EOF code point."
pub open spec fn at(input: Seq<u32>, i: int) -> u32 {
    if 0 <= i < input.len() {
        input[i]
    } else {
        EOF
    }
}

/// How many code points are left at `pos`, which is what falls as a recursive function
/// of this file moves on.
pub open spec fn remaining(input: Seq<u32>, pos: int) -> nat {
    if pos < input.len() {
        (input.len() - pos) as nat
    } else {
        0
    }
}

// ------------------------------------------------------------------------------------
// §3.3 Preprocessing the input stream
// ------------------------------------------------------------------------------------

/// A surrogate: a code point between U+D800 and U+DFFF inclusive (Infra).
pub open spec fn is_surrogate(c: nat) -> bool {
    0xD800 <= c <= 0xDFFF
}

/// §3.3 "filter code points", from position `pos`, with `output` built so far.
pub open spec fn filter_loop(input: Seq<u32>, pos: int, output: Seq<u32>) -> Seq<u32>
    decreases remaining(input, pos),
{
    if pos < 0 || pos >= input.len() {
        output
    } else {
        let c = input[pos];
        // "Replace any … pairs of U+000D CARRIAGE RETURN (CR) followed by U+000A LINE
        // FEED (LF) in input by a single U+000A LINE FEED (LF) code point."
        if c == 0x0D && at(input, pos + 1) == 0x0A {
            filter_loop(input, pos + 2, output.push(0x0A))
        // "Replace any U+000D CARRIAGE RETURN (CR) code points, U+000C FORM FEED (FF)
        // code points … by a single U+000A LINE FEED (LF) code point."
        } else if c == 0x0D || c == 0x0C {
            filter_loop(input, pos + 1, output.push(0x0A))
        // "Replace any U+0000 NULL or surrogate code points in input with U+FFFD
        // REPLACEMENT CHARACTER."
        } else if c == 0 || is_surrogate(c as nat) {
            filter_loop(input, pos + 1, output.push(REPLACEMENT))
        } else {
            filter_loop(input, pos + 1, output.push(c))
        }
    }
}

/// §3.3 <https://drafts.csswg.org/css-syntax-3/#css-filter-code-points>.
pub open spec fn filter_code_points(input: Seq<u32>) -> Seq<u32> {
    filter_loop(input, 0, Seq::empty())
}

// ------------------------------------------------------------------------------------
// §4 Tokenization: the tokens
// ------------------------------------------------------------------------------------

/// What "consume a number" returns, as the strings it builds.
pub ghost struct Number {
    /// "number part": the sign, the digits, and any "." and digits after it.
    pub number_part: Seq<u32>,
    /// "exponent part": any sign, and the digits. Empty if there is no exponent.
    pub exponent_part: Seq<u32>,
    /// "type": true for "integer", false for "number".
    pub is_integer: bool,
    /// "sign character": "+", "-" or missing.
    pub sign_character: Option<u32>,
}

/// §4 the output of tokenization.
pub ghost enum Token {
    /// `<ident-token>`.
    Ident { value: Seq<u32> },
    /// `<function-token>`.
    Function { value: Seq<u32> },
    /// `<at-keyword-token>`.
    AtKeyword { value: Seq<u32> },
    /// `<hash-token>`. `is_id` is the type flag: true for "id", false for "unrestricted".
    Hash { value: Seq<u32>, is_id: bool },
    /// `<string-token>`.
    String { value: Seq<u32> },
    /// `<bad-string-token>`.
    BadString,
    /// `<url-token>`.
    Url { value: Seq<u32> },
    /// `<bad-url-token>`.
    BadUrl,
    /// `<delim-token>`.
    Delim { value: u32 },
    /// `<number-token>`.
    Number { number: Number },
    /// `<percentage-token>`.
    Percentage { number: Number },
    /// `<dimension-token>`.
    Dimension { number: Number, unit: Seq<u32> },
    /// `<unicode-range-token>`.
    UnicodeRange { start: nat, end: nat },
    /// `<whitespace-token>`.
    Whitespace,
    /// `<CDO-token>`.
    Cdo,
    /// `<CDC-token>`.
    Cdc,
    /// `<colon-token>`.
    Colon,
    /// `<semicolon-token>`.
    Semicolon,
    /// `<comma-token>`.
    Comma,
    /// `<[-token>`.
    OpenSquare,
    /// `<]-token>`.
    CloseSquare,
    /// `<(-token>`.
    OpenParen,
    /// `<)-token>`.
    CloseParen,
    /// `<{-token>`.
    OpenCurly,
    /// `<}-token>`.
    CloseCurly,
    /// `<EOF-token>`.
    Eof,
}

// ------------------------------------------------------------------------------------
// §4.2 Definitions
// ------------------------------------------------------------------------------------

/// §4.2 digit.
pub open spec fn is_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// §4.2 hex digit.
pub open spec fn is_hex_digit(c: u32) -> bool {
    is_digit(c) || 0x41 <= c <= 0x46 || 0x61 <= c <= 0x66
}

/// §4.2 uppercase letter.
pub open spec fn is_uppercase_letter(c: u32) -> bool {
    0x41 <= c <= 0x5A
}

/// §4.2 lowercase letter.
pub open spec fn is_lowercase_letter(c: u32) -> bool {
    0x61 <= c <= 0x7A
}

/// §4.2 letter.
pub open spec fn is_letter(c: u32) -> bool {
    is_uppercase_letter(c) || is_lowercase_letter(c)
}

/// §4.2 non-ASCII ident code point. The last range is bounded (modelling choices).
pub open spec fn is_non_ascii_ident_code_point(c: u32) -> bool {
    c == 0xB7 || 0xC0 <= c <= 0xD6 || 0xD8 <= c <= 0xF6 || 0xF8 <= c <= 0x37D || 0x37F <= c
        <= 0x1FFF || c == 0x200C || c == 0x200D || c == 0x203F || c == 0x2040 || 0x2070 <= c
        <= 0x218F || 0x2C00 <= c <= 0x2FEF || 0x3001 <= c <= 0xD7FF || 0xF900 <= c <= 0xFDCF
        || 0xFDF0 <= c <= 0xFFFD || 0x1_0000 <= c <= 0x10_FFFF
}

/// §4.2 ident-start code point.
pub open spec fn is_ident_start_code_point(c: u32) -> bool {
    is_letter(c) || is_non_ascii_ident_code_point(c) || c == 0x5F
}

/// §4.2 ident code point.
pub open spec fn is_ident_code_point(c: u32) -> bool {
    is_ident_start_code_point(c) || is_digit(c) || c == 0x2D
}

/// §4.2 non-printable code point.
pub open spec fn is_non_printable_code_point(c: u32) -> bool {
    c <= 0x08 || c == 0x0B || 0x0E <= c <= 0x1F || c == 0x7F
}

/// §4.2 newline.
pub open spec fn is_newline(c: u32) -> bool {
    c == 0x0A
}

/// §4.2 whitespace.
pub open spec fn is_whitespace(c: u32) -> bool {
    is_newline(c) || c == 0x09 || c == 0x20
}

/// §4.2 maximum allowed code point.
pub const MAXIMUM_ALLOWED_CODE_POINT: u32 = 0x10_FFFF;

// ------------------------------------------------------------------------------------
// §4.3.8 to §4.3.10a the checks
// ------------------------------------------------------------------------------------

/// §4.3.8 "check if two code points are a valid escape".
pub open spec fn are_a_valid_escape(first: u32, second: u32) -> bool {
    // "If the first code point is not U+005C REVERSE SOLIDUS (\), return false."
    if first != 0x5C {
        false
    // "Otherwise, if the second code point is a newline, return false."
    } else if is_newline(second) {
        false
    // "Otherwise, return true."
    } else {
        true
    }
}

/// §4.3.9 "check if three code points would start an ident sequence".
pub open spec fn would_start_an_ident_sequence(first: u32, second: u32, third: u32) -> bool {
    // U+002D HYPHEN-MINUS
    if first == 0x2D {
        is_ident_start_code_point(second) || second == 0x2D || are_a_valid_escape(second, third)
    // ident-start code point
    } else if is_ident_start_code_point(first) {
        true
    // U+005C REVERSE SOLIDUS (\)
    } else if first == 0x5C {
        are_a_valid_escape(first, second)
    // anything else
    } else {
        false
    }
}

/// §4.3.10 "check if three code points would start a number".
pub open spec fn would_start_a_number(first: u32, second: u32, third: u32) -> bool {
    // U+002B PLUS SIGN (+), U+002D HYPHEN-MINUS (-)
    if first == 0x2B || first == 0x2D {
        if is_digit(second) {
            true
        } else if second == 0x2E && is_digit(third) {
            true
        } else {
            false
        }
    // U+002E FULL STOP (.)
    } else if first == 0x2E {
        is_digit(second)
    // digit
    } else if is_digit(first) {
        true
    // anything else
    } else {
        false
    }
}

/// "check if three code points would start a unicode-range".
pub open spec fn would_start_a_unicode_range(first: u32, second: u32, third: u32) -> bool {
    (first == 0x55 || first == 0x75) && second == 0x2B && (third == 0x3F || is_hex_digit(third))
}

// ------------------------------------------------------------------------------------
// §4.3.2 Consume comments
// ------------------------------------------------------------------------------------

/// The position after "the first U+002A ASTERISK (*) followed by a U+002F SOLIDUS (/),
/// or up to an EOF code point".
pub open spec fn end_of_comment(input: Seq<u32>, pos: int) -> int
    decreases remaining(input, pos),
{
    if pos >= input.len() {
        pos
    } else if at(input, pos) == 0x2A && at(input, pos + 1) == 0x2F {
        pos + 2
    } else {
        end_of_comment(input, pos + 1)
    }
}

/// §4.3.2 <https://drafts.csswg.org/css-syntax-3/#consume-comment>.
pub open spec fn consume_comments(input: Seq<u32>, pos: int) -> int
    decreases remaining(input, pos) via consume_comments_decreases
{
    // "If the next two input code point are U+002F SOLIDUS (/) followed by a U+002A
    // ASTERISK (*), consume them and all following code points up to and including the
    // first U+002A ASTERISK (*) followed by a U+002F SOLIDUS (/), or up to an EOF code
    // point. Return to the start of this step."
    if at(input, pos) == 0x2F && at(input, pos + 1) == 0x2A {
        consume_comments(input, end_of_comment(input, pos + 2))
    // "Return nothing."
    } else {
        pos
    }
}

// ------------------------------------------------------------------------------------
// Runs of code points that several algorithms consume
// ------------------------------------------------------------------------------------

/// "Consume as much whitespace as possible."
pub open spec fn consume_whitespace(input: Seq<u32>, pos: int) -> int
    decreases remaining(input, pos),
{
    if is_whitespace(at(input, pos)) {
        consume_whitespace(input, pos + 1)
    } else {
        pos
    }
}

/// The value of a hex digit.
pub open spec fn hex_value(c: u32) -> nat {
    if is_digit(c) {
        (c - 0x30) as nat
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as nat
    } else {
        (c - 0x61 + 10) as nat
    }
}

/// "Consume as many hex digits as possible, but no more than" `limit`, interpreting
/// them "as a hexadecimal number" after the digits that give `value`.
pub open spec fn consume_hex_digits(input: Seq<u32>, pos: int, limit: nat, value: nat) -> (nat, int)
    decreases limit,
{
    if limit > 0 && is_hex_digit(at(input, pos)) {
        consume_hex_digits(
            input,
            pos + 1,
            (limit - 1) as nat,
            value * 16 + hex_value(at(input, pos)),
        )
    } else {
        (value, pos)
    }
}

// ------------------------------------------------------------------------------------
// §4.3.7 Consume an escaped code point
// ------------------------------------------------------------------------------------

/// §4.3.7 <https://drafts.csswg.org/css-syntax-3/#consume-escaped-code-point>.
/// `pos` is after the U+005C REVERSE SOLIDUS.
pub open spec fn consume_escaped_code_point(input: Seq<u32>, pos: int) -> (u32, int) {
    // "Consume the next input code point."
    let c = at(input, pos);
    // hex digit
    if is_hex_digit(c) {
        // "Consume as many hex digits as possible, but no more than 5."
        let (number, after) = consume_hex_digits(input, pos + 1, 5, hex_value(c));
        // "If the next input code point is whitespace, consume it as well."
        let end = if is_whitespace(at(input, after)) {
            after + 1
        } else {
            after
        };
        // "If this number is zero, or is for a surrogate, or is greater than the maximum
        // allowed code point, return U+FFFD REPLACEMENT CHARACTER."
        if number == 0 || is_surrogate(number) || number > MAXIMUM_ALLOWED_CODE_POINT as nat {
            (REPLACEMENT, end)
        // "Otherwise, return the code point with that value."
        } else {
            (number as u32, end)
        }
    // EOF: "Return U+FFFD REPLACEMENT CHARACTER."
    } else if c == EOF {
        (REPLACEMENT, pos)
    // anything else: "Return the current input code point."
    } else {
        (c, pos + 1)
    }
}

// ------------------------------------------------------------------------------------
// §4.3.11 Consume an ident sequence
// ------------------------------------------------------------------------------------

/// "Repeatedly consume the next input code point from the stream" of §4.3.11.
pub open spec fn consume_ident_sequence_loop(input: Seq<u32>, pos: int, result: Seq<u32>) -> (
    Seq<u32>,
    int,
)
    decreases remaining(input, pos) via consume_ident_sequence_decreases
{
    let c = at(input, pos);
    // ident code point: "Append the code point to result."
    if is_ident_code_point(c) {
        consume_ident_sequence_loop(input, pos + 1, result.push(c))
    // "the stream starts with a valid escape": "Consume an escaped code point. Append the
    // returned code point to result."
    } else if are_a_valid_escape(c, at(input, pos + 1)) {
        let (code_point, next) = consume_escaped_code_point(input, pos + 1);
        consume_ident_sequence_loop(input, next, result.push(code_point))
    // anything else: "Reconsume the current input code point. Return result."
    } else {
        (result, pos)
    }
}

/// §4.3.11 <https://drafts.csswg.org/css-syntax-3/#consume-name>.
pub open spec fn consume_ident_sequence(input: Seq<u32>, pos: int) -> (Seq<u32>, int) {
    // "Let result initially be an empty string."
    consume_ident_sequence_loop(input, pos, Seq::empty())
}

// ------------------------------------------------------------------------------------
// §4.3.12 Consume a number
// ------------------------------------------------------------------------------------

/// "While the next input code point is a digit, consume it and append it to" `part`.
pub open spec fn consume_digits(input: Seq<u32>, pos: int, part: Seq<u32>) -> (Seq<u32>, int)
    decreases remaining(input, pos),
{
    if is_digit(at(input, pos)) {
        consume_digits(input, pos + 1, part.push(at(input, pos)))
    } else {
        (part, pos)
    }
}

/// §4.3.12 step 2, as the part so far, the sign character and the position.
pub open spec fn number_step_2(input: Seq<u32>, pos: int) -> (Seq<u32>, Option<u32>, int) {
    let c = at(input, pos);
    // 2. "If the next input code point is U+002B PLUS SIGN (+) or U+002D HYPHEN-MINUS (-),
    // consume it. Append it to number part and set sign character to it."
    if c == 0x2B || c == 0x2D {
        (seq![c], Some(c), pos + 1)
    } else {
        (Seq::empty(), None, pos)
    }
}

/// §4.3.12 step 4, as the part, whether "type" is still "integer", and the position.
pub open spec fn number_step_4(input: Seq<u32>, pos: int, part: Seq<u32>) -> (Seq<u32>, bool, int) {
    // 4. "If the next 2 input code points are U+002E FULL STOP (.) followed by a digit,
    // then:"
    if at(input, pos) == 0x2E && is_digit(at(input, pos + 1)) {
        // 4.1 "Consume the next input code point and append it to number part."
        // 4.2 "While the next input code point is a digit, consume it and append it to
        // number part."
        let (digits, end) = consume_digits(input, pos + 1, part.push(0x2E));
        // 4.3 "Set type to "number"."
        (digits, false, end)
    } else {
        (part, true, pos)
    }
}

/// §4.3.12 step 5, as the exponent part, whether there is one, and the position.
pub open spec fn number_step_5(input: Seq<u32>, pos: int) -> (Seq<u32>, bool, int) {
    let e = at(input, pos);
    let second = at(input, pos + 1);
    // 5. "If the next 2 or 3 input code points are U+0045 LATIN CAPITAL LETTER E (E) or
    // U+0065 LATIN SMALL LETTER E (e), optionally followed by U+002D HYPHEN-MINUS (-) or
    // U+002B PLUS SIGN (+), followed by a digit, then:"
    if (e == 0x45 || e == 0x65) && (is_digit(second) || ((second == 0x2D || second == 0x2B)
        && is_digit(at(input, pos + 2)))) {
        // 5.1 "Consume the next input code point."
        // 5.2 "If the next input code point is "+" or "-", consume it and append it to
        // exponent part."
        let (start, after) = if second == 0x2B || second == 0x2D {
            (seq![second], pos + 2)
        } else {
            (Seq::empty(), pos + 1)
        };
        // 5.3 "While the next input code point is a digit, consume it and append it to
        // exponent part."
        let (exponent, end) = consume_digits(input, after, start);
        // 5.4 "Set type to "number"."
        (exponent, true, end)
    } else {
        (Seq::empty(), false, pos)
    }
}

/// §4.3.12 <https://drafts.csswg.org/css-syntax-3/#consume-number>.
pub open spec fn consume_a_number(input: Seq<u32>, pos: int) -> (Number, int) {
    // 1. "Let type be the string "integer". Let number part and exponent part be the
    // empty string."
    // 2.
    let (signed, sign_character, after_sign) = number_step_2(input, pos);
    // 3. "While the next input code point is a digit, consume it and append it to number
    // part."
    let (integer, after_integer) = consume_digits(input, after_sign, signed);
    // 4.
    let (number_part, no_fraction, after_fraction) = number_step_4(input, after_integer, integer);
    // 5.
    let (exponent_part, has_exponent, end) = number_step_5(input, after_fraction);
    // 6. is number_value. 7. "Return value, type, and sign character."
    (
        Number {
            number_part,
            exponent_part,
            is_integer: no_fraction && !has_exponent,
            sign_character,
        },
        end,
    )
}

/// The value of a string of digits, after the digits that give `value`.
pub open spec fn digits_value(digits: Seq<u32>, value: nat) -> nat
    decreases digits.len(),
{
    if digits.len() == 0 {
        value
    } else {
        digits_value(digits.drop_first(), value * 10 + (digits[0] - 0x30) as nat)
    }
}

/// 10 to the power of `n`.
pub open spec fn power_of_ten(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        10 * power_of_ten((n - 1) as nat)
    }
}

/// The position of "." in `part`, or its length if it has none.
pub open spec fn point_of(part: Seq<u32>, i: nat) -> nat
    decreases part.len() - i,
{
    if i >= part.len() {
        part.len()
    } else if part[i as int] == 0x2E {
        i
    } else {
        point_of(part, i + 1)
    }
}

/// `part` without any sign at its start.
pub open spec fn unsigned(part: Seq<u32>) -> Seq<u32> {
    if part.len() > 0 && (part[0] == 0x2B || part[0] == 0x2D) {
        part.drop_first()
    } else {
        part
    }
}

/// True if `part` starts with "-".
pub open spec fn is_negative(part: Seq<u32>) -> bool {
    part.len() > 0 && part[0] == 0x2D
}

/// §4.3.12 step 6, as an exact rational (numerator, denominator): "Let value be the
/// result of interpreting number part as a base-10 number. If exponent part is
/// non-empty, interpret it as a base-10 integer, then raise 10 to the power of the
/// result, multiply it by value, and set value to that result."
pub open spec fn number_value(number: Number) -> (int, nat) {
    let part = unsigned(number.number_part);
    let point = point_of(part, 0);
    let integer = part.subrange(0, point as int);
    let fraction = if point < part.len() {
        part.subrange((point + 1) as int, part.len() as int)
    } else {
        Seq::empty()
    };
    let digits = digits_value(integer + fraction, 0);
    let magnitude = digits_value(unsigned(number.exponent_part), 0);
    let numerator = if is_negative(number.number_part) {
        -digits
    } else {
        digits as int
    };
    let denominator = power_of_ten(fraction.len());
    if number.exponent_part.len() == 0 {
        (numerator, denominator)
    } else if is_negative(number.exponent_part) {
        (numerator, denominator * power_of_ten(magnitude))
    } else {
        (numerator * power_of_ten(magnitude), denominator)
    }
}

// ------------------------------------------------------------------------------------
// §4.3.3 Consume a numeric token
// ------------------------------------------------------------------------------------

/// §4.3.3 <https://drafts.csswg.org/css-syntax-3/#consume-numeric-token>.
pub open spec fn consume_a_numeric_token(input: Seq<u32>, pos: int) -> (Token, int) {
    // "Consume a number and let number be the result."
    let (number, after) = consume_a_number(input, pos);
    // "If the next 3 input code points would start an ident sequence, then:"
    if would_start_an_ident_sequence(
        at(input, after),
        at(input, after + 1),
        at(input, after + 2),
    ) {
        // 1. to 3.
        let (unit, end) = consume_ident_sequence(input, after);
        (Token::Dimension { number, unit }, end)
    // "Otherwise, if the next input code point is U+0025 PERCENTAGE SIGN (%), consume it.
    // Create a <percentage-token> with the same value and sign character as number, and
    // return it."
    } else if at(input, after) == 0x25 {
        (Token::Percentage { number }, after + 1)
    // "Otherwise, create a <number-token> with the same value, type flag, and sign
    // character as number, and return it."
    } else {
        (Token::Number { number }, after)
    }
}

// ------------------------------------------------------------------------------------
// §4.3.5 Consume a string token
// ------------------------------------------------------------------------------------

/// "Repeatedly consume the next input code point from the stream" of §4.3.5.
pub open spec fn consume_string_loop(input: Seq<u32>, pos: int, ending: u32, value: Seq<u32>) -> (
    Token,
    int,
)
    decreases remaining(input, pos) via consume_string_decreases
{
    let c = at(input, pos);
    // ending code point: "Return the <string-token>."
    if c == ending {
        (Token::String { value }, pos + 1)
    // EOF: "Return the <string-token>."
    } else if c == EOF {
        (Token::String { value }, pos)
    // newline: "Reconsume the current input code point, create a <bad-string-token>, and
    // return it."
    } else if is_newline(c) {
        (Token::BadString, pos)
    // U+005C REVERSE SOLIDUS (\)
    } else if c == 0x5C {
        // "If the next input code point is EOF, do nothing."
        if at(input, pos + 1) == EOF {
            consume_string_loop(input, pos + 1, ending, value)
        // "Otherwise, if the next input code point is a newline, consume it."
        } else if is_newline(at(input, pos + 1)) {
            consume_string_loop(input, pos + 2, ending, value)
        // "Otherwise, (the stream starts with a valid escape) consume an escaped code
        // point and append the returned code point to the <string-token>'s value."
        } else {
            let (code_point, next) = consume_escaped_code_point(input, pos + 1);
            consume_string_loop(input, next, ending, value.push(code_point))
        }
    // anything else: "Append the current input code point to the <string-token>'s value."
    } else {
        consume_string_loop(input, pos + 1, ending, value.push(c))
    }
}

/// §4.3.5 <https://drafts.csswg.org/css-syntax-3/#consume-string-token>. `pos` is after
/// the opening quote, which is `ending`.
pub open spec fn consume_a_string_token(input: Seq<u32>, pos: int, ending: u32) -> (Token, int) {
    // "Initially create a <string-token> with its value set to the empty string."
    consume_string_loop(input, pos, ending, Seq::empty())
}

// ------------------------------------------------------------------------------------
// §4.3.14 Consume the remnants of a bad url
// ------------------------------------------------------------------------------------

/// §4.3.14 <https://drafts.csswg.org/css-syntax-3/#consume-remnants-of-bad-url>.
pub open spec fn consume_remnants_of_a_bad_url(input: Seq<u32>, pos: int) -> int
    decreases remaining(input, pos) via consume_remnants_decreases
{
    let c = at(input, pos);
    // U+0029 RIGHT PARENTHESIS ()): "Return."
    if c == 0x29 {
        pos + 1
    // EOF: "Return."
    } else if c == EOF {
        pos
    // "the input stream starts with a valid escape": "Consume an escaped code point."
    } else if are_a_valid_escape(c, at(input, pos + 1)) {
        let (_, next) = consume_escaped_code_point(input, pos + 1);
        consume_remnants_of_a_bad_url(input, next)
    // anything else: "Do nothing."
    } else {
        consume_remnants_of_a_bad_url(input, pos + 1)
    }
}

// ------------------------------------------------------------------------------------
// §4.3.6 Consume a url token
// ------------------------------------------------------------------------------------

/// §4.3.6 step 3, "Repeatedly consume the next input code point from the stream".
pub open spec fn consume_url_loop(input: Seq<u32>, pos: int, value: Seq<u32>) -> (Token, int)
    decreases remaining(input, pos) via consume_url_decreases
{
    let c = at(input, pos);
    // U+0029 RIGHT PARENTHESIS ()): "Return the <url-token>."
    if c == 0x29 {
        (Token::Url { value }, pos + 1)
    // EOF: "Return the <url-token>."
    } else if c == EOF {
        (Token::Url { value }, pos)
    // whitespace
    } else if is_whitespace(c) {
        // "Consume as much whitespace as possible."
        let after = consume_whitespace(input, pos + 1);
        // "If the next input code point is U+0029 RIGHT PARENTHESIS ()) or EOF, consume it
        // and return the <url-token>"
        if at(input, after) == 0x29 {
            (Token::Url { value }, after + 1)
        } else if at(input, after) == EOF {
            (Token::Url { value }, after)
        // "otherwise, consume the remnants of a bad url, create a <bad-url-token>, and
        // return it."
        } else {
            (Token::BadUrl, consume_remnants_of_a_bad_url(input, after))
        }
    // U+0022 QUOTATION MARK ("), U+0027 APOSTROPHE ('), U+0028 LEFT PARENTHESIS ((),
    // non-printable code point: "Consume the remnants of a bad url, create a
    // <bad-url-token>, and return it."
    } else if c == 0x22 || c == 0x27 || c == 0x28 || is_non_printable_code_point(c) {
        (Token::BadUrl, consume_remnants_of_a_bad_url(input, pos + 1))
    // U+005C REVERSE SOLIDUS (\)
    } else if c == 0x5C {
        // "If the stream starts with a valid escape, consume an escaped code point and
        // append the returned code point to the <url-token>'s value."
        if are_a_valid_escape(c, at(input, pos + 1)) {
            let (code_point, next) = consume_escaped_code_point(input, pos + 1);
            consume_url_loop(input, next, value.push(code_point))
        // "Otherwise, this is a parse error. Consume the remnants of a bad url, create a
        // <bad-url-token>, and return it."
        } else {
            (Token::BadUrl, consume_remnants_of_a_bad_url(input, pos + 1))
        }
    // anything else: "Append the current input code point to the <url-token>'s value."
    } else {
        consume_url_loop(input, pos + 1, value.push(c))
    }
}

/// §4.3.6 <https://drafts.csswg.org/css-syntax-3/#consume-url-token>.
pub open spec fn consume_a_url_token(input: Seq<u32>, pos: int) -> (Token, int) {
    // 1. "Initially create a <url-token> with its value set to the empty string."
    // 2. "Consume as much whitespace as possible."
    // 3.
    consume_url_loop(input, consume_whitespace(input, pos), Seq::empty())
}

// ------------------------------------------------------------------------------------
// §4.3.4 Consume an ident-like token
// ------------------------------------------------------------------------------------

/// True if `string` is an ASCII case-insensitive match for "url".
pub open spec fn is_url(string: Seq<u32>) -> bool {
    string.len() == 3 && (string[0] == 0x55 || string[0] == 0x75) && (string[1] == 0x52
        || string[1] == 0x72) && (string[2] == 0x4C || string[2] == 0x6C)
}

/// "While the next two input code points are whitespace, consume the next input code
/// point."
pub open spec fn consume_whitespace_but_one(input: Seq<u32>, pos: int) -> int
    decreases remaining(input, pos),
{
    if is_whitespace(at(input, pos)) && is_whitespace(at(input, pos + 1)) {
        consume_whitespace_but_one(input, pos + 1)
    } else {
        pos
    }
}

/// True for U+0022 QUOTATION MARK (") or U+0027 APOSTROPHE (').
pub open spec fn is_quote(c: u32) -> bool {
    c == 0x22 || c == 0x27
}

/// §4.3.4 <https://drafts.csswg.org/css-syntax-3/#consume-ident-like-token>.
pub open spec fn consume_an_ident_like_token(input: Seq<u32>, pos: int) -> (Token, int) {
    // "Consume an ident sequence, and let string be the result."
    let (string, after) = consume_ident_sequence(input, pos);
    // "If string's value is an ASCII case-insensitive match for "url", and the next input
    // code point is U+0028 LEFT PARENTHESIS ((), consume it."
    if is_url(string) && at(input, after) == 0x28 {
        // "While the next two input code points are whitespace, consume the next input
        // code point."
        let next = consume_whitespace_but_one(input, after + 1);
        // "If the next one or two input code points are U+0022 QUOTATION MARK ("), U+0027
        // APOSTROPHE ('), or whitespace followed by U+0022 QUOTATION MARK (") or U+0027
        // APOSTROPHE ('), then create a <function-token> with its value set to string and
        // return it."
        if is_quote(at(input, next)) || (is_whitespace(at(input, next)) && is_quote(
            at(input, next + 1),
        )) {
            (Token::Function { value: string }, next)
        // "Otherwise, consume a url token, and return it."
        } else {
            consume_a_url_token(input, next)
        }
    // "Otherwise, if the next input code point is U+0028 LEFT PARENTHESIS ((), consume it.
    // Create a <function-token> with its value set to string and return it."
    } else if at(input, after) == 0x28 {
        (Token::Function { value: string }, after + 1)
    // "Otherwise, create an <ident-token> with its value set to string and return it."
    } else {
        (Token::Ident { value: string }, after)
    }
}

// ------------------------------------------------------------------------------------
// Consume a unicode-range token
// ------------------------------------------------------------------------------------

/// "Consume as many U+003F QUESTION MARK (?) code points as possible, but no more than"
/// `limit`, as how many there were.
pub open spec fn consume_question_marks(input: Seq<u32>, pos: int, limit: nat) -> nat
    decreases limit,
{
    if limit > 0 && at(input, pos) == 0x3F {
        1 + consume_question_marks(input, pos + 1, (limit - 1) as nat)
    } else {
        0
    }
}

/// `value` with `count` more hex digits `digit` after it: what replacing the question
/// marks gives.
pub open spec fn with_digits(value: nat, count: nat, digit: nat) -> nat
    decreases count,
{
    if count == 0 {
        value
    } else {
        with_digits(value * 16 + digit, (count - 1) as nat, digit)
    }
}

/// <https://drafts.csswg.org/css-syntax-3/#consume-unicode-range-token>.
pub open spec fn consume_a_unicode_range_token(input: Seq<u32>, pos: int) -> (Token, int) {
    // 1. "Consume the next two input code points and discard them."
    let start = pos + 2;
    // 2. "Consume as many hex digits as possible, but no more than 6. If less than 6 hex
    // digits were consumed, consume as many U+003F QUESTION MARK (?) code points as
    // possible, but no more than enough to make the total of hex digits and U+003F
    // QUESTION MARK (?) code points equal to 6."
    let (first_segment, after_digits) = consume_hex_digits(input, start, 6, 0);
    let marks = consume_question_marks(input, after_digits, (6 - (after_digits - start)) as nat);
    let after_marks = after_digits + marks;
    // 3. "If first segment contains any question mark code points, then:"
    if marks > 0 {
        // 3.1 "Replace the question marks in first segment with U+0030 DIGIT ZERO (0) code
        // points, and interpret the result as a hexadecimal number."
        // 3.2 "Replace the question marks in first segment with U+0046 LATIN CAPITAL LETTER
        // F (F) code points, and interpret the result as a hexadecimal number."
        // 3.3 "Return a new <unicode-range-token> starting at start of range and ending at
        // end of range."
        (
            Token::UnicodeRange {
                start: with_digits(first_segment, marks, 0),
                end: with_digits(first_segment, marks, 15),
            },
            after_marks,
        )
    // 5. "If the next 2 input code points are U+002D HYPHEN-MINUS (-) followed by a hex
    // digit, then:" (4. is `first_segment`.)
    } else if at(input, after_marks) == 0x2D && is_hex_digit(at(input, after_marks + 1)) {
        // 5.1 "Consume the next input code point."
        // 5.2 "Consume as many hex digits as possible, but no more than 6. Interpret the
        // consumed code points as a hexadecimal number. Let this be end of range."
        let (end_of_range, end) = consume_hex_digits(input, after_marks + 1, 6, 0);
        // 5.3 "Return a new <unicode-range-token> starting at start of range and ending at
        // end of range."
        (Token::UnicodeRange { start: first_segment, end: end_of_range }, end)
    // 6. "Otherwise, return a new <unicode-range-token> both starting and ending at start
    // of range."
    } else {
        (Token::UnicodeRange { start: first_segment, end: first_segment }, after_marks)
    }
}

// ------------------------------------------------------------------------------------
// §4.3.1 Consume a token
// ------------------------------------------------------------------------------------

/// §4.3.1 <https://drafts.csswg.org/css-syntax-3/#consume-token>.
pub open spec fn consume_a_token(input: Seq<u32>, start: int, unicode_ranges_allowed: bool) -> (
    Token,
    int,
) {
    // "Consume comments."
    let current = consume_comments(input, start);
    // "Consume the next input code point."
    let c = at(input, current);
    let pos = current + 1;
    let next = at(input, pos);
    let next2 = at(input, pos + 1);
    // whitespace: "Consume as much whitespace as possible. Return a <whitespace-token>."
    if is_whitespace(c) {
        (Token::Whitespace, consume_whitespace(input, pos))
    // U+0022 QUOTATION MARK ("): "Consume a string token and return it."
    } else if c == 0x22 {
        consume_a_string_token(input, pos, c)
    // U+0023 NUMBER SIGN (#)
    } else if c == 0x23 {
        // "If the next input code point is an ident code point or the next two input code
        // points are a valid escape, then:"
        if is_ident_code_point(next) || are_a_valid_escape(next, next2) {
            // 1. "Create a <hash-token>."
            // 2. "If the next 3 input code points would start an ident sequence, set the
            // <hash-token>'s type flag to "id"."
            let is_id = would_start_an_ident_sequence(next, next2, at(input, pos + 2));
            // 3. "Consume an ident sequence, and set the <hash-token>'s value to the
            // returned string."
            let (value, end) = consume_ident_sequence(input, pos);
            // 4. "Return the <hash-token>."
            (Token::Hash { value, is_id }, end)
        // "Otherwise, return a <delim-token> with its value set to the current input code
        // point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+0027 APOSTROPHE ('): "Consume a string token and return it."
    } else if c == 0x27 {
        consume_a_string_token(input, pos, c)
    // U+0028 LEFT PARENTHESIS (()
    } else if c == 0x28 {
        (Token::OpenParen, pos)
    // U+0029 RIGHT PARENTHESIS ())
    } else if c == 0x29 {
        (Token::CloseParen, pos)
    // U+002B PLUS SIGN (+)
    } else if c == 0x2B {
        // "If the input stream starts with a number, reconsume the current input code
        // point, consume a numeric token, and return it."
        if would_start_a_number(c, next, next2) {
            consume_a_numeric_token(input, current)
        // "Otherwise, return a <delim-token> with its value set to the current input code
        // point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+002C COMMA (,)
    } else if c == 0x2C {
        (Token::Comma, pos)
    // U+002D HYPHEN-MINUS (-)
    } else if c == 0x2D {
        // "If the input stream starts with a number, reconsume the current input code
        // point, consume a numeric token, and return it."
        if would_start_a_number(c, next, next2) {
            consume_a_numeric_token(input, current)
        // "Otherwise, if the next 2 input code points are U+002D HYPHEN-MINUS U+003E
        // GREATER-THAN SIGN (->), consume them and return a <CDC-token>."
        } else if next == 0x2D && next2 == 0x3E {
            (Token::Cdc, pos + 2)
        // "Otherwise, if the input stream starts with an ident sequence, reconsume the
        // current input code point, consume an ident-like token, and return it."
        } else if would_start_an_ident_sequence(c, next, next2) {
            consume_an_ident_like_token(input, current)
        // "Otherwise, return a <delim-token> with its value set to the current input code
        // point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+002E FULL STOP (.)
    } else if c == 0x2E {
        // "If the input stream starts with a number, reconsume the current input code
        // point, consume a numeric token, and return it."
        if would_start_a_number(c, next, next2) {
            consume_a_numeric_token(input, current)
        // "Otherwise, return a <delim-token> with its value set to the current input code
        // point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+003A COLON (:)
    } else if c == 0x3A {
        (Token::Colon, pos)
    // U+003B SEMICOLON (;)
    } else if c == 0x3B {
        (Token::Semicolon, pos)
    // U+003C LESS-THAN SIGN (<)
    } else if c == 0x3C {
        // "If the next 3 input code points are U+0021 EXCLAMATION MARK U+002D HYPHEN-MINUS
        // U+002D HYPHEN-MINUS (!--), consume them and return a <CDO-token>."
        if next == 0x21 && next2 == 0x2D && at(input, pos + 2) == 0x2D {
            (Token::Cdo, pos + 3)
        // "Otherwise, return a <delim-token> with its value set to the current input code
        // point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+0040 COMMERCIAL AT (@)
    } else if c == 0x40 {
        // "If the next 3 input code points would start an ident sequence, consume an ident
        // sequence, create an <at-keyword-token> with its value set to the returned value,
        // and return it."
        if would_start_an_ident_sequence(next, next2, at(input, pos + 2)) {
            let (value, end) = consume_ident_sequence(input, pos);
            (Token::AtKeyword { value }, end)
        // "Otherwise, return a <delim-token> with its value set to the current input code
        // point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+005B LEFT SQUARE BRACKET ([)
    } else if c == 0x5B {
        (Token::OpenSquare, pos)
    // U+005C REVERSE SOLIDUS (\)
    } else if c == 0x5C {
        // "If the input stream starts with a valid escape, reconsume the current input code
        // point, consume an ident-like token, and return it."
        if are_a_valid_escape(c, next) {
            consume_an_ident_like_token(input, current)
        // "Otherwise, this is a parse error. Return a <delim-token> with its value set to
        // the current input code point."
        } else {
            (Token::Delim { value: c }, pos)
        }
    // U+005D RIGHT SQUARE BRACKET (])
    } else if c == 0x5D {
        (Token::CloseSquare, pos)
    // U+007B LEFT CURLY BRACKET ({)
    } else if c == 0x7B {
        (Token::OpenCurly, pos)
    // U+007D RIGHT CURLY BRACKET (})
    } else if c == 0x7D {
        (Token::CloseCurly, pos)
    // digit: "Reconsume the current input code point, consume a numeric token, and return
    // it."
    } else if is_digit(c) {
        consume_a_numeric_token(input, current)
    // U+0055 LATIN CAPITAL LETTER U (U), U+0075 LATIN LOWERCASE LETTER U (u)
    } else if c == 0x55 || c == 0x75 {
        // "If unicode ranges allowed is true and the input stream would start a
        // unicode-range, reconsume the current input code point, consume a unicode-range
        // token, and return it."
        if unicode_ranges_allowed && would_start_a_unicode_range(c, next, next2) {
            consume_a_unicode_range_token(input, current)
        // "Otherwise, reconsume the current input code point, consume an ident-like token,
        // and return it."
        } else {
            consume_an_ident_like_token(input, current)
        }
    // ident-start code point: "Reconsume the current input code point, consume an
    // ident-like token, and return it."
    } else if is_ident_start_code_point(c) {
        consume_an_ident_like_token(input, current)
    // EOF: "Return an <EOF-token>."
    } else if c == EOF {
        (Token::Eof, current)
    // anything else: "Return a <delim-token> with its value set to the current input code
    // point."
    } else {
        (Token::Delim { value: c }, pos)
    }
}

// ------------------------------------------------------------------------------------
// §4 Tokenization
// ------------------------------------------------------------------------------------

/// "repeatedly consume a token from input until an <EOF-token> is reached, pushing each
/// of the returned tokens into a stream."
pub open spec fn tokenize_loop(input: Seq<u32>, pos: int, tokens: Seq<Token>) -> Seq<Token>
    decreases remaining(input, pos) via tokenize_decreases
{
    let (token, next) = consume_a_token(input, pos, false);
    if token is Eof {
        tokens.push(token)
    } else {
        tokenize_loop(input, next, tokens.push(token))
    }
}

/// §4 <https://drafts.csswg.org/css-syntax-3/#css-tokenize>.
pub open spec fn tokenize(input: Seq<u32>) -> Seq<Token> {
    tokenize_loop(input, 0, Seq::empty())
}

/// Termination of [`consume_comments`].
#[via_fn]
pub proof fn consume_comments_decreases(input: Seq<u32>, pos: int) {
    super::termination::lemma_end_of_comment_advances(input, pos + 2);
}

/// Termination of [`consume_ident_sequence_loop`].
#[via_fn]
pub proof fn consume_ident_sequence_decreases(input: Seq<u32>, pos: int, result: Seq<u32>) {
    super::termination::lemma_escape_advances(input, pos + 1);
}

/// Termination of [`consume_string_loop`].
#[via_fn]
pub proof fn consume_string_decreases(input: Seq<u32>, pos: int, ending: u32, value: Seq<u32>) {
    super::termination::lemma_escape_advances(input, pos + 1);
}

/// Termination of [`consume_remnants_of_a_bad_url`].
#[via_fn]
pub proof fn consume_remnants_decreases(input: Seq<u32>, pos: int) {
    super::termination::lemma_escape_advances(input, pos + 1);
}

/// Termination of [`consume_url_loop`].
#[via_fn]
pub proof fn consume_url_decreases(input: Seq<u32>, pos: int, value: Seq<u32>) {
    super::termination::lemma_escape_advances(input, pos + 1);
}

/// Termination of [`tokenize_loop`].
#[via_fn]
pub proof fn tokenize_decreases(input: Seq<u32>, pos: int, tokens: Seq<Token>) {
    super::termination::lemma_token_advances(input, pos, false);
}

} // verus!
