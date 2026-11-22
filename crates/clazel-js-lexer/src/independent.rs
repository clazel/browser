//! An independent transcription of part of ECMAScript's lexical grammar,
//! written before this agent re-read [`super::spec`] for this task and
//! without consulting it (docs/VERIFICATION.md, "Trust without reviewers",
//! item 2). The same model family wrote both files, so the two are
//! independent in source document, in form and in order of writing only.
//!
//! # Sources
//!
//! - **Unicode Standard Annex #31**, "Unicode Identifiers and Syntax",
//!   §2 "Default Identifier Syntax" (`<Identifier> := <Start> <Continue>*`),
//!   with §2.3's ECMAScript profile of `Start` and `Continue`; the Unicode
//!   Standard §6.2 "General Punctuation" (the Zs space separators, U+2028
//!   and U+2029) for white space and line separators.
//! - **ECMA-262 Annex A "Grammar Summary"**, A.1 "Lexical Grammar", in the
//!   2026 edition, for the productions and their alternatives, and Annex
//!   B.1.1 for the legacy numeric forms. (Annex A restates §12's grammar,
//!   so for those productions the source document is the same standard;
//!   what differs is the *form*, below.)
//!
//! # Form
//!
//! [`super::spec`] writes every production as a recursive relation on a
//! range, one clause per grammar alternative. This file writes each
//! production as a **closed-form characterisation of the strings it
//! derives**, with no recursion where a regular language allows none:
//!
//! - a run of digits with `_` separators is "first and last code points
//!   are digits, every code point is a digit or `_`, and no two `_` are
//!   adjacent" ([`ind_sep_digits`]), not `Digits Digit | Digits _ Digit`;
//! - a single-line comment is "`//` then no line terminator"; a
//!   multi-line comment is "`/*`, `*/` at the end, and no earlier `*/`";
//! - a legacy octal literal is "`0` then one or more octal digits"; a
//!   NonOctalDecimalIntegerLiteral is "`0`, decimal digits, at least one
//!   of them 8 or 9";
//! - an identifier name is read left to right as a sequence of *units*
//!   ([`ind_unit_len`]: one code point, or one `\u` escape), each of which
//!   has one length, instead of `IdentifierName IdentifierPart`.
//!
//! The equivalence proofs (`equivalence.rs`) show that each closed form is
//! the same relation as the spec's production, at every range of every
//! source text. A misreading in either file shows up there at the exact
//! production.
//!
//! # What is covered, and what is not
//!
//! Covered: `WhiteSpace`, `LineTerminator`, the line terminator sequence,
//! `SingleLineComment`, `MultiLineComment`, `HashbangComment`, the digit
//! classes and `DecimalDigits`, `HexDigits`, `OctalDigits` and
//! `BinaryDigits` with separators, `NumericLiteral` in all its forms
//! (including BigInt and the Annex B legacy forms), `UnicodeEscapeSequence`
//! (as a range), the `IdentifierName` and `PrivateIdentifier` ranges,
//! `ReservedWord` and `Punctuator`.
//!
//! Not covered (no independent transcription exists yet, so nothing is
//! claimed about them): string literals and their SV, template literals,
//! regular expression literals, the Annex B.1.1 HTML-like comments, the
//! values (identifier code points, TV, TRV), and the longest-match and error
//! rules (§12 intro). Those parts of the spec are checked by the
//! conformance tests (`tests/conformance_test262.rs`) alone.
//!
//! # Shared assumptions
//!
//! - `ID_Start` and `ID_Continue` of code points above U+007F are
//!   [`super::spec::unicode_id_start_non_ascii`] and
//!   [`super::spec::unicode_id_continue_non_ascii`]: uninterpreted in
//!   Verus, with the generated table (`unicode_data.rs`) as their only
//!   connection to Unicode. This file does not try to say more, so the
//!   equivalence says "the same given the same Unicode properties".
//! - Source text is a `Seq<u32>` of code points, and a production is a
//!   predicate on `(s, i, j)` meaning the code points `s[i..j)` are derived,
//!   as in the spec: a different model of source text would change what
//!   the proofs relate.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Code point classes.
// ---------------------------------------------------------------------

/// Unicode General_Category Zs ("Space_Separator"), Unicode Standard
/// Table 6-1 and UnicodeData.txt: U+0020, U+00A0, U+1680, U+2000..U+200A,
/// U+202F, U+205F, U+3000.
pub open spec fn ind_zs(c: u32) -> bool {
    c == 0x20 || c == 0xA0 || c == 0x1680 || (0x2000 <= c && c <= 0x200A) || c == 0x202F
        || c == 0x205F || c == 0x3000
}

/// Annex A: `WhiteSpace :: <TAB> | <VT> | <FF> | <ZWNBSP> | <USP>`, where
/// <USP> is any code point in Zs.
pub open spec fn ind_ws_cp(c: u32) -> bool {
    c == 0x09 || c == 0x0B || c == 0x0C || c == 0xFEFF || ind_zs(c)
}

/// Annex A: `LineTerminator :: <LF> | <CR> | <LS> | <PS>`.
pub open spec fn ind_lt_cp(c: u32) -> bool {
    c == 0x0A || c == 0x0D || c == 0x2028 || c == 0x2029
}

/// `DecimalDigit :: one of 0 1 2 3 4 5 6 7 8 9`.
pub open spec fn ind_dec(c: u32) -> bool {
    0x30 <= c && c <= 0x39
}

/// `OctalDigit :: one of 0 1 2 3 4 5 6 7`.
pub open spec fn ind_oct(c: u32) -> bool {
    0x30 <= c && c <= 0x37
}

/// `BinaryDigit :: one of 0 1`.
pub open spec fn ind_bin(c: u32) -> bool {
    c == 0x30 || c == 0x31
}

/// `HexDigit :: one of 0 1 2 3 4 5 6 7 8 9 a b c d e f A B C D E F`.
pub open spec fn ind_hex(c: u32) -> bool {
    ind_dec(c) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
}

/// The digit class of a radix 2, 8, 10 or 16.
pub open spec fn ind_radix_digit(radix: int, c: u32) -> bool {
    if radix == 2 {
        ind_bin(c)
    } else if radix == 8 {
        ind_oct(c)
    } else if radix == 10 {
        ind_dec(c)
    } else {
        ind_hex(c)
    }
}

/// The mathematical value of a hex digit.
pub open spec fn ind_hex_val(c: u32) -> int {
    if ind_dec(c) {
        c - 0x30
    } else if 0x41 <= c && c <= 0x46 {
        c - 0x41 + 10
    } else {
        c - 0x61 + 10
    }
}

/// UAX #31 §2.3, the ECMAScript profile: `Start := ID_Start + $ + _`.
pub open spec fn ind_id_start(c: u32) -> bool {
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) || c == 0x24 || c == 0x5F || (c > 0x7F
        && unicode_id_start_non_ascii(c))
}

/// UAX #31 §2.3, the ECMAScript profile: `Continue := ID_Continue + $`.
/// (Since Unicode 15.1 ZWNJ and ZWJ are in `ID_Continue` themselves, so the
/// profile no longer adds them; the code points above U+007F are the shared
/// table's.) For ASCII, `ID_Continue` is the letters, the digits and `_`.
/// `ID_Continue` contains `ID_Start` (UAX #31 §1.1), which is a fact about
/// the Unicode data, so for code points above U+007F this file does not
/// derive it: it uses `ID_Continue`'s own (shared, uninterpreted) predicate.
pub open spec fn ind_id_continue(c: u32) -> bool {
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) || c == 0x24 || c == 0x5F || ind_dec(c)
        || (c > 0x7F && unicode_id_continue_non_ascii(c))
}

/// `SourceCharacter :: any Unicode code point` (ECMA-262 §11.1): U+0000 to
/// U+10FFFF.
pub open spec fn ind_src_cp(c: u32) -> bool {
    c <= 0x10FFFF
}

// ---------------------------------------------------------------------
// Whole-range predicates.
// ---------------------------------------------------------------------

/// Every code point of `s[i..j)` is a `SourceCharacter` that is not a
/// `LineTerminator`: `SingleLineCommentChar :: SourceCharacter but not
/// LineTerminator`.
pub open spec fn ind_no_line_terminator(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && j <= s.len() && forall|k: int|
        i <= k < j ==> (ind_src_cp(#[trigger] s[k]) && !ind_lt_cp(s[k]))
}

/// `s[k]` exists and is the code point `c`.
pub open spec fn ind_is(s: Seq<u32>, k: int, c: u32) -> bool {
    0 <= k < s.len() && s[k] == c
}

/// `WhiteSpace`: one code point.
pub open spec fn ind_white_space(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && j == i + 1 && j <= s.len() && ind_ws_cp(s[i])
}

/// `LineTerminator`: one code point.
pub open spec fn ind_line_terminator(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && j == i + 1 && j <= s.len() && ind_lt_cp(s[i])
}

/// `LineTerminatorSequence :: <LF> | <CR> [lookahead != <LF>] | <LS> | <PS>
/// | <CR> <LF>`: written as the two shapes it has. A `<CR>` alone is a
/// sequence only when no `<LF>` follows.
pub open spec fn ind_line_terminator_sequence(s: Seq<u32>, i: int, j: int) -> bool {
    (0 <= i && j == i + 1 && j <= s.len() && (s[i] == 0x0A || s[i] == 0x2028 || s[i] == 0x2029
        || (s[i] == 0x0D && !ind_is(s, j, 0x0A)))) || (0 <= i && j == i + 2 && j <= s.len()
        && s[i] == 0x0D && s[i + 1] == 0x0A)
}

/// `SingleLineComment :: // SingleLineCommentChars?`: `//` and then no line
/// terminator up to `j`.
pub open spec fn ind_single_line_comment(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i + 2 <= j && j <= s.len() && s[i] == 0x2F && s[i + 1] == 0x2F && ind_no_line_terminator(
        s,
        i + 2,
        j,
    )
}

/// `MultiLineComment :: /* MultiLineCommentChars? */`: `/*` and `*/` do not
/// share their `*`, and the first `*/` after the opening is the closing one.
pub open spec fn ind_multi_line_comment(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i + 4 <= j && j <= s.len() && s[i] == 0x2F && s[i + 1] == 0x2A && s[j - 2] == 0x2A
        && s[j - 1] == 0x2F && (forall|k: int|
        i + 2 <= k < j - 2 ==> !(#[trigger] s[k] == 0x2A && s[k + 1] == 0x2F)) && (forall|k: int|
        i + 2 <= k < j - 2 ==> ind_src_cp(#[trigger] s[k]))
}

/// `HashbangComment :: #! SingleLineCommentChars?`.
pub open spec fn ind_hashbang_comment(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i + 2 <= j && j <= s.len() && s[i] == 0x23 && s[i + 1] == 0x21 && ind_no_line_terminator(
        s,
        i + 2,
        j,
    )
}

// ---------------------------------------------------------------------
// Digit runs with numeric separators.
// ---------------------------------------------------------------------

/// `XDigits[+Sep] :: XDigit | XDigits[+Sep] XDigit | XDigits[+Sep]
/// NumericLiteralSeparator XDigit`, as its closed form: it starts and ends
/// with a digit, holds only digits and `_`, and no `_` follows a `_`.
pub open spec fn ind_sep_digits(radix: int, s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i < j && j <= s.len() && ind_radix_digit(radix, s[i]) && ind_radix_digit(
        radix,
        s[j - 1],
    ) && (forall|k: int|
        i <= k < j ==> (ind_radix_digit(radix, #[trigger] s[k]) || s[k] == 0x5F)) && (forall|k: int|
        i <= k < j - 1 ==> !(#[trigger] s[k] == 0x5F && s[k + 1] == 0x5F))
}

/// `XDigits[~Sep] :: XDigit | XDigits[~Sep] XDigit`: one or more digits.
pub open spec fn ind_plain_digits(radix: int, s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i < j && j <= s.len() && forall|k: int|
        i <= k < j ==> ind_radix_digit(radix, #[trigger] s[k])
}

// ---------------------------------------------------------------------
// Numeric literals (Annex A.1, Annex B.1.1).
// ---------------------------------------------------------------------

/// `LegacyOctalIntegerLiteral :: 0 OctalDigit | LegacyOctalIntegerLiteral
/// OctalDigit`: `0` then one or more octal digits.
pub open spec fn ind_legacy_octal(s: Seq<u32>, i: int, j: int) -> bool {
    ind_is(s, i, 0x30) && ind_plain_digits(8, s, i + 1, j)
}

/// `NonOctalDecimalIntegerLiteral :: 0 NonOctalDigit |
/// LegacyOctalLikeDecimalIntegerLiteral NonOctalDigit |
/// NonOctalDecimalIntegerLiteral DecimalDigit`: `0`, then decimal digits of
/// which at least one is 8 or 9.
pub open spec fn ind_non_octal_decimal_integer(s: Seq<u32>, i: int, j: int) -> bool {
    ind_is(s, i, 0x30) && ind_plain_digits(10, s, i + 1, j) && exists|k: int|
        i < k < j && (#[trigger] s[k] == 0x38 || s[k] == 0x39)
}

/// `DecimalIntegerLiteral :: 0 | NonZeroDigit | NonZeroDigit
/// NumericLiteralSeparator? DecimalDigits[+Sep] | NonOctalDecimalIntegerLiteral`:
/// the single `0`; a separated digit run that does not begin with `0`; or
/// the non-octal form.
pub open spec fn ind_decimal_integer(s: Seq<u32>, i: int, j: int) -> bool {
    (ind_is(s, i, 0x30) && j == i + 1) || (ind_sep_digits(10, s, i, j) && s[i] != 0x30)
        || ind_non_octal_decimal_integer(s, i, j)
}

/// `ExponentPart :: ExponentIndicator SignedInteger`, with `SignedInteger ::
/// DecimalDigits[+Sep] | + DecimalDigits[+Sep] | - DecimalDigits[+Sep]`.
pub open spec fn ind_exponent(s: Seq<u32>, i: int, j: int) -> bool {
    (ind_is(s, i, 0x65) || ind_is(s, i, 0x45)) && (ind_sep_digits(10, s, i + 1, j) || ((ind_is(
        s,
        i + 1,
        0x2B,
    ) || ind_is(s, i + 1, 0x2D)) && ind_sep_digits(10, s, i + 2, j)))
}

/// First shape of a `DecimalLiteral`: the integer on `[i, a)`, `.` at `a`,
/// optional digits on `[a + 1, b)`, optional exponent on `[b, j)`.
pub open spec fn ind_dl_alt1(s: Seq<u32>, i: int, j: int, a: int, b: int) -> bool {
    i < a < b <= j && ind_decimal_integer(s, i, a) && ind_is(s, a, 0x2E) && (b == a + 1
        || ind_sep_digits(10, s, a + 1, b)) && (b == j || ind_exponent(s, b, j))
}

/// Second shape: `.` at `i`, digits on `[i + 1, b)`, optional exponent.
pub open spec fn ind_dl_alt2(s: Seq<u32>, i: int, j: int, b: int) -> bool {
    i + 1 < b <= j && ind_is(s, i, 0x2E) && ind_sep_digits(10, s, i + 1, b) && (b == j
        || ind_exponent(s, b, j))
}

/// Third shape: the integer on `[i, a)` and an optional exponent.
pub open spec fn ind_dl_alt3(s: Seq<u32>, i: int, j: int, a: int) -> bool {
    i < a <= j && ind_decimal_integer(s, i, a) && (a == j || ind_exponent(s, a, j))
}

/// `DecimalLiteral :: DecimalIntegerLiteral . DecimalDigits[+Sep]?
/// ExponentPart[+Sep]? | . DecimalDigits[+Sep] ExponentPart[+Sep]? |
/// DecimalIntegerLiteral ExponentPart[+Sep]?`.
pub open spec fn ind_decimal_literal(s: Seq<u32>, i: int, j: int) -> bool {
    (exists|a: int, b: int| #[trigger] ind_dl_alt1(s, i, j, a, b)) || (exists|b: int|
        #[trigger] ind_dl_alt2(s, i, j, b)) || (exists|a: int| #[trigger] ind_dl_alt3(s, i, j, a))
}

/// `BigIntLiteralSuffix :: n`.
pub open spec fn ind_bigint_suffix(s: Seq<u32>, k: int) -> bool {
    ind_is(s, k, 0x6E)
}

/// `DecimalBigIntegerLiteral :: 0 BigIntLiteralSuffix | NonZeroDigit
/// DecimalDigits[+Sep]? BigIntLiteralSuffix | NonZeroDigit
/// NumericLiteralSeparator DecimalDigits[+Sep] BigIntLiteralSuffix`: the
/// `0`, or a separated digit run that does not begin with `0`, then `n`.
pub open spec fn ind_decimal_bigint(s: Seq<u32>, i: int, j: int) -> bool {
    i < j && ind_bigint_suffix(s, j - 1) && ((ind_is(s, i, 0x30) && j == i + 2) || (
    ind_sep_digits(10, s, i, j - 1) && s[i] != 0x30))
}

/// `NonDecimalIntegerLiteral[+Sep] :: 0b BinaryDigits | 0B ... | 0o
/// OctalDigits | 0O ... | 0x HexDigits | 0X ...`.
pub open spec fn ind_non_decimal_integer(s: Seq<u32>, i: int, j: int) -> bool {
    ind_is(s, i, 0x30) && ((((ind_is(s, i + 1, 0x62) || ind_is(s, i + 1, 0x42))
        && ind_sep_digits(2, s, i + 2, j)) || ((ind_is(s, i + 1, 0x6F) || ind_is(s, i + 1, 0x4F))
        && ind_sep_digits(8, s, i + 2, j))) || ((ind_is(s, i + 1, 0x78) || ind_is(s, i + 1, 0x58))
        && ind_sep_digits(16, s, i + 2, j)))
}

/// `NumericLiteral :: DecimalBigIntegerLiteral | NonDecimalIntegerLiteral
/// [+Sep] | NonDecimalIntegerLiteral[+Sep] BigIntLiteralSuffix |
/// LegacyOctalIntegerLiteral | DecimalLiteral`.
pub open spec fn ind_numeric_literal(s: Seq<u32>, i: int, j: int) -> bool {
    ind_decimal_bigint(s, i, j) || ind_non_decimal_integer(s, i, j) || (i < j
        && ind_bigint_suffix(s, j - 1) && ind_non_decimal_integer(s, i, j - 1))
        || ind_legacy_octal(s, i, j) || ind_decimal_literal(s, i, j)
}

// ---------------------------------------------------------------------
// Identifiers: UAX #31 `<Identifier> := <Start> <Continue>*`, where the
// ECMAScript profile lets a `\u` escape stand for a code point.
// ---------------------------------------------------------------------

/// The code points of a hex digit run `s[a..b)` as an integer, most
/// significant digit first.
pub open spec fn ind_hex_run_value(s: Seq<u32>, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a {
        0
    } else {
        16 * ind_hex_run_value(s, a, b - 1) + ind_hex_val(s[b - 1])
    }
}

/// The index of the first code point at or after `k` that is not a hex
/// digit (`s.len()` if there is none).
pub open spec fn ind_hex_run_end(s: Seq<u32>, k: int) -> int
    decreases s.len() - k,
{
    if 0 <= k < s.len() && ind_hex(s[k]) {
        ind_hex_run_end(s, k + 1)
    } else {
        k
    }
}

/// Where the `UnicodeEscapeSequence` that starts at `k` (the code point
/// after the backslash) ends, or -1 when none starts there. It is read
/// deterministically: `u{` opens a braced `CodePoint`, which runs to the
/// end of its hex digits and must then be closed by `}` with a value of at
/// most 0x10FFFF; any other `u` must be followed by four hex digits.
pub open spec fn ind_escape_end(s: Seq<u32>, k: int) -> int {
    if !ind_is(s, k, 0x75) {
        -1
    } else if ind_is(s, k + 1, 0x7B) {
        let m = ind_hex_run_end(s, k + 2);
        if m > k + 2 && ind_is(s, m, 0x7D) && ind_hex_run_value(s, k + 2, m) <= 0x10FFFF {
            m + 1
        } else {
            -1
        }
    } else if ind_hex_run_end(s, k + 1) >= k + 5 {
        k + 5
    } else {
        -1
    }
}

/// Where the identifier unit at `k` ends, or -1 when none starts there. A
/// unit is one code point of the class `start` selects (`Start` when true,
/// `Continue` when false) or `\` and a `UnicodeEscapeSequence`.
pub open spec fn ind_unit_end(s: Seq<u32>, k: int, start: bool) -> int {
    if 0 <= k < s.len() && s[k] == 0x5C {
        ind_escape_end(s, k + 1)
    } else if 0 <= k < s.len() && (if start {
        ind_id_start(s[k])
    } else {
        ind_id_continue(s[k])
    }) {
        k + 1
    } else {
        -1
    }
}

/// UAX #31 `<Identifier> := <Start> <Continue>*`, read left to right as
/// units: `s[i..j)` is derived when its first unit is a `Start` unit
/// (`first`), every later one a `Continue` unit, and the units end exactly
/// at `j`.
pub open spec fn ind_name_from(s: Seq<u32>, i: int, j: int, first: bool) -> bool
    decreases j - i,
{
    if i >= j {
        i == j && !first
    } else {
        let e = ind_unit_end(s, i, first);
        i < e && e <= j && ind_name_from(s, e, j, false)
    }
}

/// `IdentifierName` over `s[i..j)`.
pub open spec fn ind_identifier_name(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && ind_name_from(s, i, j, true)
}

/// `UnicodeEscapeSequence` over `s[i..j)` (the code points after the
/// backslash): the deterministic reading of [`ind_escape_end`] ends at `j`.
pub open spec fn ind_unicode_escape(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i < j && j <= s.len() && ind_escape_end(s, i) == j
}

/// `PrivateIdentifier :: # IdentifierName`.
pub open spec fn ind_private_identifier(s: Seq<u32>, i: int, j: int) -> bool {
    ind_is(s, i, 0x23) && ind_identifier_name(s, i + 1, j)
}

// ---------------------------------------------------------------------
// Punctuators and reserved words.
// ---------------------------------------------------------------------

/// The one-code-point `OtherPunctuator`s: `{ ( ) [ ] . ; , < > + - * % & |
/// ^ ! ~ ? : =`.
pub open spec fn ind_punct1(a: u32) -> bool {
    a == 0x7B || a == 0x28 || a == 0x29 || a == 0x5B || a == 0x5D || a == 0x2E || a == 0x3B
        || a == 0x2C || a == 0x3C || a == 0x3E || a == 0x2B || a == 0x2D || a == 0x2A
        || a == 0x25 || a == 0x26 || a == 0x7C || a == 0x5E || a == 0x21 || a == 0x7E
        || a == 0x3F || a == 0x3A || a == 0x3D
}

/// The two-code-point ones: `<= >= == != ++ -- << >> && || ?? => += -= *=
/// %= &= |= ^= **`.
pub open spec fn ind_punct2(a: u32, b: u32) -> bool {
    (b == 0x3D && (a == 0x3C || a == 0x3E || a == 0x3D || a == 0x21 || a == 0x2B || a == 0x2D
        || a == 0x2A || a == 0x25 || a == 0x26 || a == 0x7C || a == 0x5E)) || (a == 0x2B && b
        == 0x2B) || (a == 0x2D && b == 0x2D) || (a == 0x3C && b == 0x3C) || (a == 0x3E && b
        == 0x3E) || (a == 0x26 && b == 0x26) || (a == 0x7C && b == 0x7C) || (a == 0x3F && b
        == 0x3F) || (a == 0x3D && b == 0x3E) || (a == 0x2A && b == 0x2A)
}

/// The three-code-point ones: `... === !== >>> **= <<= >>= &&= ||= ??=`.
pub open spec fn ind_punct3(a: u32, b: u32, c: u32) -> bool {
    (a == 0x2E && b == 0x2E && c == 0x2E) || (b == 0x3D && c == 0x3D && (a == 0x3D || a == 0x21))
        || (a == 0x3E && b == 0x3E && c == 0x3E) || (c == 0x3D && ((a == 0x2A && b == 0x2A) || (
    a == 0x3C && b == 0x3C) || (a == 0x3E && b == 0x3E) || (a == 0x26 && b == 0x26) || (a
        == 0x7C && b == 0x7C) || (a == 0x3F && b == 0x3F)))
}

/// The four-code-point one: `>>>=`.
pub open spec fn ind_punct4(a: u32, b: u32, c: u32, d: u32) -> bool {
    a == 0x3E && b == 0x3E && c == 0x3E && d == 0x3D
}

/// `OtherPunctuator` over `s[i..j)`: one of the one- to four-code-point
/// punctuators above.
pub open spec fn ind_other_punctuator(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && i < j && j <= s.len() && ((j == i + 1 && ind_punct1(s[i])) || (j == i + 2
        && ind_punct2(s[i], s[i + 1])) || (j == i + 3 && ind_punct3(s[i], s[i + 1], s[i + 2]))
        || (j == i + 4 && ind_punct4(s[i], s[i + 1], s[i + 2], s[i + 3])))
}

/// `OptionalChainingPunctuator :: ?. [lookahead ∉ DecimalDigit]`.
pub open spec fn ind_optional_chaining(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && j == i + 2 && j <= s.len() && s[i] == 0x3F && s[i + 1] == 0x2E && !(j < s.len()
        && ind_dec(s[j]))
}

/// `DivPunctuator :: / | /=`.
pub open spec fn ind_div_punctuator(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && j <= s.len() && s[i] == 0x2F && (j == i + 1 || (j == i + 2 && s[i + 1] == 0x3D))
}

/// `RightBracePunctuator :: }`.
pub open spec fn ind_right_brace(s: Seq<u32>, i: int, j: int) -> bool {
    0 <= i && j == i + 1 && j <= s.len() && s[i] == 0x7D
}

/// The code points of an ASCII word.
pub open spec fn ind_word(w: Seq<char>) -> Seq<u32> {
    w.map_values(|c: char| c as u32)
}

/// `ReservedWord :: one of await break case catch class const continue
/// debugger default delete do else enum export extends false finally for
/// function if import in instanceof new null return super switch this
/// throw true try typeof var void while with yield`.
pub open spec fn ind_reserved_words() -> Seq<Seq<char>> {
    seq![
        seq!['a', 'w', 'a', 'i', 't'],
        seq!['b', 'r', 'e', 'a', 'k'],
        seq!['c', 'a', 's', 'e'],
        seq!['c', 'a', 't', 'c', 'h'],
        seq!['c', 'l', 'a', 's', 's'],
        seq!['c', 'o', 'n', 's', 't'],
        seq!['c', 'o', 'n', 't', 'i', 'n', 'u', 'e'],
        seq!['d', 'e', 'b', 'u', 'g', 'g', 'e', 'r'],
        seq!['d', 'e', 'f', 'a', 'u', 'l', 't'],
        seq!['d', 'e', 'l', 'e', 't', 'e'],
        seq!['d', 'o'],
        seq!['e', 'l', 's', 'e'],
        seq!['e', 'n', 'u', 'm'],
        seq!['e', 'x', 'p', 'o', 'r', 't'],
        seq!['e', 'x', 't', 'e', 'n', 'd', 's'],
        seq!['f', 'a', 'l', 's', 'e'],
        seq!['f', 'i', 'n', 'a', 'l', 'l', 'y'],
        seq!['f', 'o', 'r'],
        seq!['f', 'u', 'n', 'c', 't', 'i', 'o', 'n'],
        seq!['i', 'f'],
        seq!['i', 'm', 'p', 'o', 'r', 't'],
        seq!['i', 'n'],
        seq!['i', 'n', 's', 't', 'a', 'n', 'c', 'e', 'o', 'f'],
        seq!['n', 'e', 'w'],
        seq!['n', 'u', 'l', 'l'],
        seq!['r', 'e', 't', 'u', 'r', 'n'],
        seq!['s', 'u', 'p', 'e', 'r'],
        seq!['s', 'w', 'i', 't', 'c', 'h'],
        seq!['t', 'h', 'i', 's'],
        seq!['t', 'h', 'r', 'o', 'w'],
        seq!['t', 'r', 'u', 'e'],
        seq!['t', 'r', 'y'],
        seq!['t', 'y', 'p', 'e', 'o', 'f'],
        seq!['v', 'a', 'r'],
        seq!['v', 'o', 'i', 'd'],
        seq!['w', 'h', 'i', 'l', 'e'],
        seq!['w', 'i', 't', 'h'],
        seq!['y', 'i', 'e', 'l', 'd'],
    ]
}

/// Whether `cps` spells a reserved word.
pub open spec fn ind_is_reserved(cps: Seq<u32>) -> bool {
    exists|w: int| 0 <= w < ind_reserved_words().len() && cps == ind_word(
        #[trigger] ind_reserved_words()[w],
    )
}

} // verus!
