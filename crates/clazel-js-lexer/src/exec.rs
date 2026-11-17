//! The executable lexer (phase-7.md item 7.2, second half).
//!
//! Each `scan_` function reads one production of [`super::spec`] at a
//! position, as a loop with no recursion (a script is what a page chose;
//! Verus proves no panic, not no stack overflow), and returns where it
//! ends. [`next_input_element`] dispatches on the first code point, takes
//! the longest of the alternatives that can start there (§12), and then
//! applies the two checks the spec makes after the longest element is
//! chosen ([`lex_error`]); [`next_token`] repeats it over trivia.
//!
//! # What is proven, and what is not
//!
//! Verus proves, for every input, with no escape hatch:
//!
//! - **Totality:** every function terminates (each loop has a `decreases`)
//!   and never panics: no index out of range, no overflow.
//! - **Span coverage:** [`next_input_element_proven`]: the end of the
//!   source text gives `Eof`, and nothing else does; an element starts at
//!   `pos`, ends after it and inside the source text; so elements from
//!   repeated calls tile the source text. [`next_token_proven`]: the token
//!   starts at or after `pos`, is not trivia, and its `newline_before` is
//!   [`contains_line_terminator`] of some trivia element between them.
//! - **The value's shape:** [`value_shape_agrees`]: an element has the
//!   kind of `Value` its kind has (a `StringLiteral` a `Value::String`, and
//!   so on), and a regular expression's `body_end` is inside it.
//! - **The derivation of the simple kinds:** [`kind_agrees_proven`]: a
//!   `WhiteSpace`, `LineTerminator`, `HashbangComment`, `DivPunctuator` or
//!   `RightBracePunctuator` element is derived by its kind in the goal
//!   ([`element_matches`]).
//! - **Single code points:** the classifiers (`is_ws`, `is_lt`, the digit
//!   classes, `hex_val`) equal the spec's, and `push_utf16` is
//!   UTF16EncodeCodePoint (§11.1.1).
//!
//! It is **not** proven that the results agree with [`super::spec`]
//! otherwise: that the kind derives the range for the other kinds
//! (comments, names, punctuators, literals, templates, regular
//! expressions), that no longer element exists ([`longest_len`]), that the
//! errors are [`lex_error`]'s, that `newline_before` is [`skip_trivia`]'s,
//! and that the values are the spec's relations. These are the rest of
//! [`super::contract`], which the functions here do not claim, so they do
//! not implement [`super::api::JsLexer`]. Their agreement with the spec is
//! tested (`tests/`), not proven. [`lemma_contract_implies_proven`] shows
//! that what is proven is implied by the full contract.
//!
//! Non-ASCII `ID_Start` and `ID_Continue` come from [`super::unicode`],
//! which the spec leaves uninterpreted: nothing is claimed about them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::api::{Element, Next, Step, Token, Value};

verus! {

// ---------------------------------------------------------------------
// What the executable lexer is proven to satisfy.
// ---------------------------------------------------------------------

/// The kind of [`Value`] an element has is the one its kind has (the shape
/// of [`super::contract::element_value_agrees`], not the values), and a
/// regular expression's closing `/` is inside it, after a non-empty body.
pub open spec fn value_shape_agrees(el: Element) -> bool {
    match el.value {
        Value::None => !(el.kind == ElementKind::IdentifierName
            || el.kind == ElementKind::PrivateIdentifier || el.kind == ElementKind::StringLiteral
            || el.kind == ElementKind::NumericLiteral
            || el.kind == ElementKind::RegularExpressionLiteral
            || el.kind == ElementKind::Template(TemplateKind::NoSubstitution)
            || el.kind == ElementKind::Template(TemplateKind::Head)
            || el.kind == ElementKind::Template(TemplateKind::Middle)
            || el.kind == ElementKind::Template(TemplateKind::Tail)),
        Value::Name { .. } => el.kind == ElementKind::IdentifierName || el.kind
            == ElementKind::PrivateIdentifier,
        Value::String { .. } => el.kind == ElementKind::StringLiteral,
        Value::Template { .. } => el.kind == ElementKind::Template(TemplateKind::NoSubstitution)
            || el.kind == ElementKind::Template(TemplateKind::Head) || el.kind
            == ElementKind::Template(TemplateKind::Middle) || el.kind == ElementKind::Template(
            TemplateKind::Tail,
        ),
        Value::Numeric { .. } => el.kind == ElementKind::NumericLiteral,
        Value::RegExp { body_end } => el.kind == ElementKind::RegularExpressionLiteral
            && el.start + 1 < body_end < el.end,
    }
}

/// For the kinds whose derivation is proven, the kind derives the
/// element's range in the goal ([`element_matches`], one conjunct of
/// [`super::contract::next_input_element_ensures`]): `WhiteSpace`,
/// `LineTerminator`, `HashbangComment`, `DivPunctuator` and
/// `RightBracePunctuator`. For the other kinds nothing is claimed here.
pub open spec fn kind_agrees_proven(goal: Goal, html: bool, src: Seq<u32>, el: Element) -> bool {
    (el.kind == ElementKind::WhiteSpace || el.kind == ElementKind::LineTerminator || el.kind
        == ElementKind::HashbangComment || el.kind == ElementKind::DivPunctuator || el.kind
        == ElementKind::RightBracePunctuator) ==> element_matches(
        goal,
        html,
        el.kind,
        src,
        el.start as int,
        el.end as int,
    )
}

/// What [`next_input_element`] is proven to return: totality, span
/// coverage, the value's shape, and the derivation of the simple kinds. A
/// weakening of [`super::contract::next_input_element_ensures`]
/// ([`lemma_contract_implies_proven`]).
pub open spec fn next_input_element_proven(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<Step, LexError>,
) -> bool {
    match r {
        Err(_) => pos < src.len(),
        Ok(Step::Eof) => pos == src.len(),
        Ok(Step::Element(el)) => pos < src.len() && el.start == pos && pos < el.end && el.end
            <= src.len() && value_shape_agrees(el) && kind_agrees_proven(goal, html, src, el),
    }
}

/// What [`next_token`] is proven to return: the token is after `pos`,
/// inside the source text and not trivia, and the flag is set only by a
/// line terminator code point between `pos` and the token.
pub open spec fn next_token_proven(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<Next, LexError>,
) -> bool {
    match r {
        Err(_) => pos < src.len(),
        Ok(Next::Eof { newline_before }) => newline_before ==> contains_line_terminator(
            src,
            pos as int,
            src.len() as int,
        ),
        Ok(Next::Token(tok)) => pos <= tok.element.start < tok.element.end <= src.len()
            && !is_trivia(tok.element.kind) && value_shape_agrees(tok.element)
            && kind_agrees_proven(goal, html, src, tok.element) && (tok.newline_before
            ==> contains_line_terminator(src, pos as int, tok.element.start as int)),
    }
}

/// The full contract implies what is proven of [`next_input_element`]
/// (except the value's shape, which the full contract states value by
/// value): the proven part is a weakening, not a different claim.
/// ([`kind_agrees_proven`] is the contract's `element_matches` conjunct
/// itself, restricted to some kinds.)
pub proof fn lemma_contract_implies_proven(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<Step, LexError>,
)
    requires
        pos <= src.len(),
        super::contract::next_input_element_ensures(src, pos, goal, html, r),
    ensures
        match r {
            Err(_) => pos < src.len(),
            Ok(Step::Eof) => pos == src.len(),
            Ok(Step::Element(el)) => pos < src.len() && el.start == pos && pos < el.end && el.end
                <= src.len() && kind_agrees_proven(goal, html, src, el),
        },
{
}

// ---------------------------------------------------------------------
// Reading code points.
// ---------------------------------------------------------------------

/// What [`peek`] returns past the end of the source text. It is above
/// U+10FFFF, so it is no `SourceCharacter` and matches no class below,
/// just as a lookahead fails at the end (§11.1, `at` in the spec).
pub const EOF: u32 = 0xFFFF_FFFF;

/// The code point at `k`, or [`EOF`].
pub fn peek(src: &[u32], k: usize) -> (c: u32)
    ensures
        k < src.len() ==> c == src@[k as int],
        k >= src.len() ==> c == EOF,
{
    match src.get(k) {
        Some(c) => *c,
        None => EOF,
    }
}

/// §11.1 `SourceCharacter`.
fn is_src(c: u32) -> (r: bool)
    ensures
        r == is_source_character(c),
{
    c <= 0x10FFFF
}

/// `low <= c <= high`.
fn between(c: u32, low: u32, high: u32) -> (r: bool)
    ensures
        r == (low <= c <= high),
{
    low <= c && c <= high
}

/// §12.3 `LineTerminator`: <LF>, <CR>, <LS>, <PS>.
fn is_lt(c: u32) -> (r: bool)
    ensures
        r == is_line_terminator(c),
{
    c == 0x0A || c == 0x0D || c == 0x2028 || c == 0x2029
}

/// `SourceCharacter but not LineTerminator` (§12.4 `SingleLineCommentChar`,
/// §12.9.5 `RegularExpressionNonTerminator`).
fn is_line_char(c: u32) -> (r: bool)
    ensures
        r == is_not_line_terminator(c),
{
    is_src(c) && !is_lt(c)
}

/// §12.2 `WhiteSpace`: <TAB>, <VT>, <FF>, <ZWNBSP>, <USP>.
fn is_ws(c: u32) -> (r: bool)
    ensures
        r == (c == 0x0009 || c == 0x000B || c == 0x000C || c == 0xFEFF
            || unicode_space_separator(c)),
{
    c == 0x0009 || c == 0x000B || c == 0x000C || c == 0xFEFF || c == 0x0020 || c == 0x00A0 || c
        == 0x1680 || between(c, 0x2000, 0x200A) || c == 0x202F || c == 0x205F || c == 0x3000
}

/// §12.9.3 `DecimalDigit`.
fn is_dec(c: u32) -> (r: bool)
    ensures
        r == is_decimal_digit(c),
{
    between(c, 0x30, 0x39)
}

/// §12.9.3 `OctalDigit`.
fn is_oct(c: u32) -> (r: bool)
    ensures
        r == is_octal_digit(c),
{
    between(c, 0x30, 0x37)
}

/// §12.9.3 `HexDigit`.
fn is_hex(c: u32) -> (r: bool)
    ensures
        r == is_hex_digit(c),
{
    between(c, 0x30, 0x39) || between(c, 0x61, 0x66) || between(c, 0x41, 0x46)
}

/// `BinaryDigit`, `OctalDigit`, `DecimalDigit` or `HexDigit` by radix.
fn is_radix(radix: u32, c: u32) -> (r: bool)
    requires
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        r == is_radix_digit(radix as int, c),
{
    if radix == 2 {
        c == 0x30 || c == 0x31
    } else if radix == 8 {
        is_oct(c)
    } else if radix == 10 {
        is_dec(c)
    } else {
        is_hex(c)
    }
}

/// The MV of a `HexDigit` (§12.9.3.2).
fn hex_val(c: u32) -> (r: u32)
    requires
        is_hex_digit(c),
    ensures
        r as int == hex_digit_value(c),
        r < 16,
{
    if between(c, 0x30, 0x39) {
        c.saturating_sub(0x30)
    } else if between(c, 0x61, 0x66) {
        c.saturating_sub(0x61).saturating_add(10)
    } else {
        c.saturating_sub(0x41).saturating_add(10)
    }
}

/// §12.7 `IdentifierStartChar :: UnicodeIDStart | $ | _`. Above U+007F,
/// [`super::unicode`]'s table, about which nothing is claimed.
fn id_start_char(c: u32) -> (r: bool)
    ensures
        c < 0x80 ==> r == is_identifier_start_char(c),
        r ==> c <= 0x10FFFF,
        r ==> c != 0x5C,
{
    if c < 0x80 {
        between(c, 0x61, 0x7A) || between(c, 0x41, 0x5A) || c == 0x24 || c == 0x5F
    } else {
        super::unicode::id_start_non_ascii(c)
    }
}

/// §12.7 `IdentifierPartChar :: UnicodeIDContinue | $`.
fn id_part_char(c: u32) -> (r: bool)
    ensures
        c < 0x80 ==> r == is_identifier_part_char(c),
        r ==> c <= 0x10FFFF,
        r ==> c != 0x5C,
{
    if c < 0x80 {
        between(c, 0x61, 0x7A) || between(c, 0x41, 0x5A) || between(c, 0x30, 0x39) || c
            == 0x24 || c == 0x5F
    } else {
        super::unicode::id_continue_non_ascii(c)
    }
}

/// Appends UTF16EncodeCodePoint(`cp`) (§11.1.1).
fn push_utf16(out: &mut Vec<u16>, cp: u32)
    requires
        cp <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + utf16_encode_code_point(cp as int),
{
    if cp <= 0xFFFF {
        // 2. "If cp ≤ 0xFFFF, return the String value consisting of the
        //    code unit whose numeric value is cp."
        out.push(cp as u16);
        assert(final(out)@ =~= old(out)@ + utf16_encode_code_point(cp as int));
    } else {
        let v = cp.saturating_sub(0x10000);
        // 3. cu1 is floor((cp - 0x10000) / 0x400) + 0xD800.
        let cu1 = (v / 0x400).saturating_add(0xD800) as u16;
        // 4. cu2 is ((cp - 0x10000) modulo 0x400) + 0xDC00.
        let cu2 = (v % 0x400).saturating_add(0xDC00) as u16;
        // 5. The string-concatenation of cu1 and cu2.
        out.push(cu1);
        out.push(cu2);
        assert(final(out)@ =~= old(out)@ + utf16_encode_code_point(cp as int));
    }
}

/// Appends the UTF-16 of `src[i..j)`, each code point a `SourceCharacter`.
fn push_range_utf16(out: &mut Vec<u16>, src: &[u32], i: usize, j: usize)
    requires
        i <= j <= src.len(),
{
    let mut k = i;
    while k < j
        invariant
            i <= k <= j <= src.len(),
        decreases j - k,
    {
        let c = peek(src, k);
        if c <= 0x10FFFF {
            push_utf16(out, c);
        }
        k = k.saturating_add(1);
    }
}

// ---------------------------------------------------------------------
// §12.4 Comments, §12.5 Hashbang Comments, Annex B.1.1
// ---------------------------------------------------------------------

/// §12.4 `SingleLineCommentChars?` from `k`: the first index at or after
/// `k` that is not a `SourceCharacter` other than a `LineTerminator`.
fn scan_line_chars(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
        all_of(src@, k as int, r as int, |c: u32| is_not_line_terminator(c)),
        r < src.len() ==> !is_not_line_terminator(src@[r as int]),
{
    let mut j = k;
    loop
        invariant
            k <= j <= src.len(),
            all_of(src@, k as int, j as int, |c: u32| is_not_line_terminator(c)),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if is_line_char(c) {
            j = j.saturating_add(1);
        } else {
            return j;
        }
    }
}

/// §12.4 `MultiLineComment` (or, with `!multi_line`, Annex B's
/// `SingleLineDelimitedComment`) after its `/*` at `k`: the end of the
/// first `*/` and whether a `LineTerminator` came before it. `None` if the
/// source text ends, or a code point that is not a `SourceCharacter` (or,
/// with `!multi_line`, a `LineTerminator`) comes, first.
fn scan_block_comment(src: &[u32], k: usize, multi_line: bool) -> (r: Option<(usize, bool)>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some((e, _)) => k + 2 <= e <= src.len(),
            None => true,
        },
{
    let mut j = k;
    let mut lt = false;
    loop
        invariant
            k <= j <= src.len(),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x2A && peek(src, j.saturating_add(1)) == 0x2F {
            return Some((j.saturating_add(2), lt));
        }
        if !is_src(c) || (!multi_line && is_lt(c)) {
            return None;
        }
        if is_lt(c) {
            lt = true;
        }
        j = j.saturating_add(1);
    }
}

/// Annex B.1.1 `WhiteSpaceSequence?` from `k`.
fn scan_ws(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
{
    let mut j = k;
    loop
        invariant
            k <= j <= src.len(),
        decreases src.len() - j,
    {
        if is_ws(peek(src, j)) {
            j = j.saturating_add(1);
        } else {
            return j;
        }
    }
}

/// Annex B.1.1 the end of `-->` SingleLineCommentChars? at `k`.
fn scan_html_arrow(src: &[u32], k: usize) -> (r: Option<usize>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some(e) => k + 3 <= e <= src.len(),
            None => true,
        },
{
    if peek(src, k) == 0x2D && peek(src, k.saturating_add(1)) == 0x2D && peek(
        src,
        k.saturating_add(2),
    ) == 0x3E {
        Some(scan_line_chars(src, k.saturating_add(3)))
    } else {
        None
    }
}

/// Annex B.1.1 `HTMLCloseComment :: WhiteSpaceSequence?
/// SingleLineDelimitedCommentSequence? --> SingleLineCommentChars?` at `k`.
/// Each part is determined by the code point that starts it (white space,
/// `/*` or `-->`), so the parse is the only one, and it ends where the
/// line does.
fn scan_html_close(src: &[u32], k: usize) -> (r: Option<usize>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some(e) => k + 3 <= e <= src.len(),
            None => true,
        },
{
    let mut j = scan_ws(src, k);
    loop
        invariant
            k <= j <= src.len(),
        decreases src.len() - j,
    {
        if peek(src, j) == 0x2F && peek(src, j.saturating_add(1)) == 0x2A {
            // SingleLineDelimitedComment WhiteSpaceSequence?
            match scan_block_comment(src, j.saturating_add(2), false) {
                Some((e, _)) => {
                    j = scan_ws(src, e);
                },
                None => {
                    return None;
                },
            }
        } else {
            return scan_html_arrow(src, j);
        }
    }
}

/// The `LineTerminatorSequence` at `k` (§12.3): <CR><LF> is one.
fn line_terminator_sequence_end(src: &[u32], k: usize) -> (r: usize)
    requires
        k < src.len(),
        is_line_terminator(src@[k as int]),
    ensures
        k < r <= src.len(),
{
    if peek(src, k) == 0x0D && peek(src, k.saturating_add(1)) == 0x0A {
        k.saturating_add(2)
    } else {
        k.saturating_add(1)
    }
}

// ---------------------------------------------------------------------
// §12.7 Names
// ---------------------------------------------------------------------

/// The MV of the `HexDigits[~Sep]` that start at `k` (all of them), capped
/// at 0x110000 (any value above U+10FFFF is `NotCodePoint`), and the end.
fn scan_hex_digits(src: &[u32], k: usize) -> (r: (u32, usize))
    requires
        k <= src.len(),
    ensures
        r.0 <= 0x110000,
        k <= r.1 <= src.len(),
{
    let mut j = k;
    let mut v: u32 = 0;
    loop
        invariant
            k <= j <= src.len(),
            v <= 0x110000,
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if is_hex(c) {
            let d = hex_val(c);
            if v <= 0x10FFFF {
                let w = v.saturating_mul(16).saturating_add(d);
                v = if w > 0x10FFFF {
                    0x110000
                } else {
                    w
                };
            }
            j = j.saturating_add(1);
        } else {
            return (v, j);
        }
    }
}

/// §12.9.4 `Hex4Digits` at `k`: its MV.
fn scan_hex4(src: &[u32], k: usize) -> (r: Option<u32>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some(v) => k + 4 <= src.len() && v <= 0xFFFF,
            None => true,
        },
{
    let a = peek(src, k);
    let b = peek(src, k.saturating_add(1));
    let c = peek(src, k.saturating_add(2));
    let d = peek(src, k.saturating_add(3));
    if is_hex(a) && is_hex(b) && is_hex(c) && is_hex(d) {
        let v = hex_val(a).saturating_mul(0x1000).saturating_add(
            hex_val(b).saturating_mul(0x100),
        ).saturating_add(hex_val(c).saturating_mul(0x10)).saturating_add(hex_val(d));
        Some(v)
    } else {
        None
    }
}

/// §12.9.4 `UnicodeEscapeSequence :: u Hex4Digits | u{ CodePoint }` at `k`
/// (after the backslash): its code point (§12.7.1.3 IdentifierCodePoint)
/// and its end.
fn scan_unicode_escape(src: &[u32], k: usize) -> (r: Option<(u32, usize)>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some((cp, e)) => k < e <= src.len() && cp <= 0x10FFFF,
            None => true,
        },
{
    if peek(src, k) != 0x75 {
        return None;
    }
    if peek(src, k.saturating_add(1)) == 0x7B {
        // 2. `u{` CodePoint `}`, with CodePoint's MV at most 0x10FFFF.
        let (v, e) = scan_hex_digits(src, k.saturating_add(2));
        if e > k.saturating_add(2) && v <= 0x10FFFF && peek(src, e) == 0x7D {
            Some((v, e.saturating_add(1)))
        } else {
            None
        }
    } else {
        // 1. `u` Hex4Digits
        let v = scan_hex4(src, k.saturating_add(1))?;
        Some((v, k.saturating_add(5)))
    }
}

/// §12.7 `IdentifierName` at `k`, greedily (each `IdentifierPart` is
/// determined by its first code point, so the longest derivation is the
/// greedy one): IdentifierCodePoints (§12.7.1.2), whether an escape was
/// used, whether the §12.7.1.1 early errors pass, and the end.
fn scan_identifier(src: &[u32], k: usize) -> (r: Option<(Vec<u32>, bool, bool, usize)>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some((_, _, _, e)) => k < e <= src.len(),
            None => true,
        },
{
    let mut cps: Vec<u32> = Vec::new();
    let mut escaped = false;
    let mut valid = true;
    let c = peek(src, k);
    let mut j: usize;
    if c == 0x5C {
        // IdentifierStart :: \ UnicodeEscapeSequence; §12.7.1.1: "It is a
        // Syntax Error if the IdentifierCodePoint of UnicodeEscapeSequence
        // is not some Unicode code point matched by the IdentifierStartChar
        // lexical grammar production."
        match scan_unicode_escape(src, k.saturating_add(1)) {
            Some((cp, e)) => {
                cps.push(cp);
                escaped = true;
                valid = id_start_char(cp);
                j = e;
            },
            None => {
                return None;
            },
        }
    } else if id_start_char(c) {
        // IdentifierStart :: IdentifierStartChar
        cps.push(c);
        j = k.saturating_add(1);
    } else {
        return None;
    }
    loop
        invariant
            k < j <= src.len(),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x5C {
            // IdentifierPart :: \ UnicodeEscapeSequence, with §12.7.1.1's
            // rule for IdentifierPartChar.
            match scan_unicode_escape(src, j.saturating_add(1)) {
                Some((cp, e)) => {
                    cps.push(cp);
                    escaped = true;
                    if !id_part_char(cp) {
                        valid = false;
                    }
                    j = e;
                },
                None => {
                    return Some((cps, escaped, valid, j));
                },
            }
        } else if id_part_char(c) {
            // IdentifierPart :: IdentifierPartChar
            cps.push(c);
            j = j.saturating_add(1);
        } else {
            return Some((cps, escaped, valid, j));
        }
    }
}

// ---------------------------------------------------------------------
// §12.8 Punctuators
// ---------------------------------------------------------------------

/// §12.8 `Punctuator` (`OptionalChainingPunctuator` and `OtherPunctuator`)
/// at `k`: the end of the longest one, or `k` if none starts there.
fn scan_punctuator(src: &[u32], k: usize) -> (r: usize)
    requires
        k < src.len(),
    ensures
        k <= r <= src.len(),
{
    let c0 = peek(src, k);
    let c1 = peek(src, k.saturating_add(1));
    let c2 = peek(src, k.saturating_add(2));
    let c3 = peek(src, k.saturating_add(3));
    let n: usize = if c0 == 0x7B || c0 == 0x28 || c0 == 0x29 || c0 == 0x5B || c0 == 0x5D || c0
        == 0x3B || c0 == 0x2C || c0 == 0x7E || c0 == 0x3A {
        // { ( ) [ ] ; , ~ :
        1
    } else if c0 == 0x2E {
        // ... .
        if c1 == 0x2E && c2 == 0x2E {
            3
        } else {
            1
        }
    } else if c0 == 0x3C {
        // <<= << <= <
        if c1 == 0x3C && c2 == 0x3D {
            3
        } else if c1 == 0x3C || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x3E {
        // >>>= >>> >>= >> >= >
        if c1 == 0x3E && c2 == 0x3E && c3 == 0x3D {
            4
        } else if c1 == 0x3E && (c2 == 0x3E || c2 == 0x3D) {
            3
        } else if c1 == 0x3E || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x3D {
        // === == => =
        if c1 == 0x3D && c2 == 0x3D {
            3
        } else if c1 == 0x3D || c1 == 0x3E {
            2
        } else {
            1
        }
    } else if c0 == 0x21 {
        // !== != !
        if c1 == 0x3D && c2 == 0x3D {
            3
        } else if c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x2B || c0 == 0x2D {
        // ++ += +, -- -= -
        if c1 == c0 || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x2A {
        // **= ** *= *
        if c1 == 0x2A && c2 == 0x3D {
            3
        } else if c1 == 0x2A || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x25 || c0 == 0x5E {
        // %= %, ^= ^
        if c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x26 || c0 == 0x7C {
        // &&= && &= &, ||= || |= |
        if c1 == c0 && c2 == 0x3D {
            3
        } else if c1 == c0 || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x3F {
        // ??= ?? ?. ?, with OptionalChainingPunctuator :: ?.
        // [lookahead ∉ DecimalDigit]
        if c1 == 0x3F && c2 == 0x3D {
            3
        } else if c1 == 0x3F || (c1 == 0x2E && !is_dec(c2)) {
            2
        } else {
            1
        }
    } else {
        0
    };
    k.saturating_add(n)
}

// ---------------------------------------------------------------------
// §12.9.3 Numeric Literals
// ---------------------------------------------------------------------

/// §12.9.3 `Digits[+Sep]` of a radix, from a digit at `k`: digits, each
/// pair of them possibly separated by one `_`. Greedy, since a `_` is
/// taken only when a digit follows it.
fn scan_digits_sep(src: &[u32], k: usize, radix: u32) -> (r: usize)
    requires
        k < src.len(),
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        k < r <= src.len(),
{
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
            radix == 2 || radix == 8 || radix == 10 || radix == 16,
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if is_radix(radix, c) {
            j = j.saturating_add(1);
        } else if c == 0x5F && is_radix(radix, peek(src, j.saturating_add(1))) {
            j = j.saturating_add(2);
        } else {
            return j;
        }
    }
}

/// §12.9.3 `ExponentPart[+Sep]?` at `k`: its end, or `k`.
fn scan_exponent(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
{
    let c = peek(src, k);
    if c == 0x65 || c == 0x45 {
        let s = peek(src, k.saturating_add(1));
        let m = if s == 0x2B || s == 0x2D {
            k.saturating_add(2)
        } else {
            k.saturating_add(1)
        };
        if is_dec(peek(src, m)) {
            scan_digits_sep(src, m, 10)
        } else {
            k
        }
    } else {
        k
    }
}

/// The rest of a §12.9.3 `DecimalLiteral` after its `DecimalIntegerLiteral`
/// ends at `k`: `. DecimalDigits[+Sep]? ExponentPart[+Sep]?` or
/// `ExponentPart[+Sep]?`.
fn scan_decimal_tail(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
{
    if peek(src, k) == 0x2E {
        let m = k.saturating_add(1);
        let n = if is_dec(peek(src, m)) {
            scan_digits_sep(src, m, 10)
        } else {
            m
        };
        scan_exponent(src, n)
    } else {
        scan_exponent(src, k)
    }
}

/// §12.9.3 `NumericLiteral` at `k`, the longest: its end, whether it is a
/// BigInt literal, and whether it is legacy (§12.9.3.1).
fn scan_numeric(src: &[u32], k: usize) -> (r: Option<(usize, bool, bool)>)
    requires
        k < src.len(),
    ensures
        match r {
            Some((e, _, _)) => k < e <= src.len(),
            None => true,
        },
{
    let c0 = peek(src, k);
    let c1 = peek(src, k.saturating_add(1));
    if c0 == 0x2E {
        // DecimalLiteral :: . DecimalDigits[+Sep] ExponentPart[+Sep]?
        if is_dec(c1) {
            let e = scan_digits_sep(src, k.saturating_add(1), 10);
            Some((scan_exponent(src, e), false, false))
        } else {
            None
        }
    } else if c0 == 0x30 {
        let c2 = peek(src, k.saturating_add(2));
        let radix: u32 = if c1 == 0x62 || c1 == 0x42 {
            2
        } else if c1 == 0x6F || c1 == 0x4F {
            8
        } else if c1 == 0x78 || c1 == 0x58 {
            16
        } else {
            0
        };
        if radix != 0 && is_radix(radix, c2) {
            // NonDecimalIntegerLiteral[+Sep] BigIntLiteralSuffix?
            let e = scan_digits_sep(src, k.saturating_add(2), radix);
            if peek(src, e) == 0x6E {
                Some((e.saturating_add(1), true, false))
            } else {
                Some((e, false, false))
            }
        } else if c1 == 0x6E {
            // DecimalBigIntegerLiteral :: 0 BigIntLiteralSuffix
            Some((k.saturating_add(2), true, false))
        } else if is_dec(c1) {
            // `0` and decimal digits, with no separator: a
            // LegacyOctalIntegerLiteral if they are all octal, else a
            // NonOctalDecimalIntegerLiteral, which a DecimalLiteral may
            // continue.
            let mut j = k.saturating_add(1);
            let mut octal = true;
            loop
                invariant
                    k < j <= src.len(),
                decreases src.len() - j,
            {
                let c = peek(src, j);
                if is_dec(c) {
                    if !is_oct(c) {
                        octal = false;
                    }
                    j = j.saturating_add(1);
                } else {
                    break;
                }
            }
            if octal {
                Some((j, false, true))
            } else {
                Some((scan_decimal_tail(src, j), false, true))
            }
        } else {
            // DecimalIntegerLiteral :: 0
            Some((scan_decimal_tail(src, k.saturating_add(1)), false, false))
        }
    } else if is_dec(c0) {
        // DecimalIntegerLiteral :: NonZeroDigit NumericLiteralSeparator?
        // DecimalDigits[+Sep], or a DecimalBigIntegerLiteral.
        let e = scan_digits_sep(src, k, 10);
        if peek(src, e) == 0x6E {
            Some((e.saturating_add(1), true, false))
        } else {
            Some((scan_decimal_tail(src, e), false, false))
        }
    } else {
        None
    }
}

/// §12.9.3: "The SourceCharacter immediately following a NumericLiteral
/// must not be an IdentifierStart or DecimalDigit."
fn numeric_follow_error(src: &[u32], j: usize) -> (r: bool)
    requires
        j <= src.len(),
{
    let c = peek(src, j);
    if is_dec(c) || id_start_char(c) {
        true
    } else if c == 0x5C {
        scan_unicode_escape(src, j.saturating_add(1)).is_some()
    } else {
        false
    }
}

// ---------------------------------------------------------------------
// §12.9.4 String Literals
// ---------------------------------------------------------------------

/// §12.9.4 `LegacyOctalEscapeSequence` at `k`, whose first digit `d` is an
/// octal digit: its MV, pushed as one code unit, and its end. The
/// lookaheads make it the longest run its first digit allows: three digits
/// after `0` to `3`, two after `4` to `7`.
fn scan_legacy_octal_escape(src: &[u32], k: usize, units: &mut Vec<u16>) -> (r: usize)
    requires
        k < src.len(),
        is_octal_digit(src@[k as int]),
    ensures
        k < r <= src.len(),
{
    let d = peek(src, k);
    let mut v: u32 = d.saturating_sub(0x30);
    let mut e = k.saturating_add(1);
    let c1 = peek(src, e);
    if is_oct(c1) {
        v = v.saturating_mul(8).saturating_add(c1.saturating_sub(0x30));
        e = e.saturating_add(1);
        let c2 = peek(src, e);
        if d <= 0x33 && is_oct(c2) {
            v = v.saturating_mul(8).saturating_add(c2.saturating_sub(0x30));
            e = e.saturating_add(1);
        }
    }
    units.push(v as u16);
    e
}

/// §12.9.4 `\ EscapeSequence` or `LineContinuation`, the backslash at
/// `k`: appends the SV (§12.9.4.2) and returns the end.
fn scan_string_escape(src: &[u32], k: usize, units: &mut Vec<u16>) -> (r: Option<usize>)
    requires
        k < src.len(),
    ensures
        match r {
            Some(e) => k + 1 < e <= src.len(),
            None => true,
        },
{
    let m = k.saturating_add(1);
    let d = peek(src, m);
    if is_lt(d) {
        // LineContinuation: the empty String.
        Some(line_terminator_sequence_end(src, m))
    } else if d == 0x27 || d == 0x22 || d == 0x5C {
        // SingleEscapeCharacter ' " \: the character itself.
        units.push(d as u16);
        Some(m.saturating_add(1))
    } else if d == 0x62 || d == 0x66 || d == 0x6E || d == 0x72 || d == 0x74 || d == 0x76 {
        // SingleEscapeCharacter b f n r t v (Table "String Single Character
        // Escape Sequences").
        let u: u16 = if d == 0x62 {
            0x08
        } else if d == 0x74 {
            0x09
        } else if d == 0x6E {
            0x0A
        } else if d == 0x76 {
            0x0B
        } else if d == 0x66 {
            0x0C
        } else {
            0x0D
        };
        units.push(u);
        Some(m.saturating_add(1))
    } else if d == 0x30 && !is_dec(peek(src, m.saturating_add(1))) {
        // `0` [lookahead ∉ DecimalDigit]: 0x0000.
        units.push(0);
        Some(m.saturating_add(1))
    } else if d == 0x30 && !is_oct(peek(src, m.saturating_add(1))) {
        // LegacyOctalEscapeSequence :: `0` [lookahead ∈ { 8, 9 }]: 0.
        units.push(0);
        Some(m.saturating_add(1))
    } else if is_oct(d) {
        // LegacyOctalEscapeSequence, the other alternatives.
        Some(scan_legacy_octal_escape(src, m, units))
    } else if d == 0x38 || d == 0x39 {
        // NonOctalDecimalEscapeSequence: 0x0038 or 0x0039.
        units.push(d as u16);
        Some(m.saturating_add(1))
    } else if d == 0x78 {
        // HexEscapeSequence :: x HexDigit HexDigit
        let a = peek(src, m.saturating_add(1));
        let b = peek(src, m.saturating_add(2));
        if is_hex(a) && is_hex(b) {
            units.push(hex_val(a).saturating_mul(16).saturating_add(hex_val(b)) as u16);
            Some(m.saturating_add(3))
        } else {
            None
        }
    } else if d == 0x75 {
        // UnicodeEscapeSequence: UTF16EncodeCodePoint of its MV.
        match scan_unicode_escape(src, m) {
            Some((cp, e)) => {
                push_utf16(units, cp);
                Some(e)
            },
            None => None,
        }
    } else if is_src(d) {
        // NonEscapeCharacter: the code point.
        push_utf16(units, d);
        Some(m.saturating_add(1))
    } else {
        None
    }
}

/// §12.9.4 `StringLiteral` at `k` (a quote): its SV and its end.
fn scan_string(src: &[u32], k: usize) -> (r: Option<(Vec<u16>, usize)>)
    requires
        k < src.len(),
        src@[k as int] == 0x22 || src@[k as int] == 0x27,
    ensures
        match r {
            Some((_, e)) => k + 2 <= e <= src.len(),
            None => true,
        },
{
    let quote = peek(src, k);
    let mut units: Vec<u16> = Vec::new();
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
            quote == 0x22 || quote == 0x27,
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == quote {
            return Some((units, j.saturating_add(1)));
        } else if c == 0x5C {
            match scan_string_escape(src, j, &mut units) {
                Some(e) => {
                    j = e;
                },
                None => {
                    return None;
                },
            }
        } else if c == 0x2028 || c == 0x2029 {
            // <LS>, <PS>: the code unit.
            units.push(c as u16);
            j = j.saturating_add(1);
        } else if is_line_char(c) {
            // SourceCharacter but not one of the quote or \ or
            // LineTerminator.
            push_utf16(&mut units, c);
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

// ---------------------------------------------------------------------
// §12.9.5 Regular Expression Literals
// ---------------------------------------------------------------------

/// §12.9.5 `RegularExpressionClass` at `k` (a `[`): its end.
fn scan_regexp_class(src: &[u32], k: usize) -> (r: Option<usize>)
    requires
        k < src.len(),
    ensures
        match r {
            Some(e) => k < e <= src.len(),
            None => true,
        },
{
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x5D {
            return Some(j.saturating_add(1));
        } else if c == 0x5C {
            // RegularExpressionBackslashSequence
            if is_line_char(peek(src, j.saturating_add(1))) {
                j = j.saturating_add(2);
            } else {
                return None;
            }
        } else if is_line_char(c) {
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

/// §12.9.5 `RegularExpressionLiteral` at `k` (a `/`): the index of the
/// closing `/` and the end of the flags.
fn scan_regexp(src: &[u32], k: usize) -> (r: Option<(usize, usize)>)
    requires
        k < src.len(),
    ensures
        match r {
            Some((b, e)) => k + 1 < b < e <= src.len(),
            None => true,
        },
{
    let first = peek(src, k.saturating_add(1));
    // RegularExpressionFirstChar is not `*` or `/`.
    if first == 0x2A || first == 0x2F {
        return None;
    }
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
            j == k + 1 ==> (k + 1 >= src.len() || src@[(k + 1) as int] != 0x2F),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x2F {
            // The closing `/`, then RegularExpressionFlags.
            let mut f = j.saturating_add(1);
            loop
                invariant
                    k + 1 < j < f <= src.len(),
                decreases src.len() - f,
            {
                if id_part_char(peek(src, f)) {
                    f = f.saturating_add(1);
                } else {
                    return Some((j, f));
                }
            }
        } else if c == 0x5C {
            if is_line_char(peek(src, j.saturating_add(1))) {
                j = j.saturating_add(2);
            } else {
                return None;
            }
        } else if c == 0x5B {
            match scan_regexp_class(src, j) {
                Some(e) => {
                    j = e;
                },
                None => {
                    return None;
                },
            }
        } else if is_line_char(c) {
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

// ---------------------------------------------------------------------
// §12.9.6 Template Literal Lexical Components
// ---------------------------------------------------------------------

/// A template component's TV (`None` once a `NotEscapeSequence` makes it
/// *undefined*) and TRV, as they are built.
struct TemplateValues {
    cooked: Vec<u16>,
    defined: bool,
    raw: Vec<u16>,
}

/// §12.9.6 `\ TemplateEscapeSequence`, `\ NotEscapeSequence` or
/// `LineContinuation`, the backslash at `k`: appends the TV and TRV
/// (§12.9.6.1, §12.9.6.2) and returns the end.
fn scan_template_escape(src: &[u32], k: usize, values: &mut TemplateValues) -> (r: Option<usize>)
    requires
        k < src.len(),
    ensures
        match r {
            Some(e) => k + 1 < e <= src.len(),
            None => true,
        },
{
    let m = k.saturating_add(1);
    let d = peek(src, m);
    if is_lt(d) {
        // LineContinuation: TV is empty; TRV is \ and the TRV of the
        // LineTerminatorSequence (<CR><LF> and <CR> are <LF>).
        let e = line_terminator_sequence_end(src, m);
        values.raw.push(0x5C);
        if d == 0x2028 || d == 0x2029 {
            values.raw.push(d as u16);
        } else {
            values.raw.push(0x0A);
        }
        return Some(e);
    }
    // In every other case the TRV is the UTF-16 of the matched code points.
    let e: usize;
    if d == 0x27 || d == 0x22 || d == 0x5C {
        values.cooked.push(d as u16);
        e = m.saturating_add(1);
    } else if d == 0x62 || d == 0x66 || d == 0x6E || d == 0x72 || d == 0x74 || d == 0x76 {
        let u: u16 = if d == 0x62 {
            0x08
        } else if d == 0x74 {
            0x09
        } else if d == 0x6E {
            0x0A
        } else if d == 0x76 {
            0x0B
        } else if d == 0x66 {
            0x0C
        } else {
            0x0D
        };
        values.cooked.push(u);
        e = m.saturating_add(1);
    } else if d == 0x30 {
        if is_dec(peek(src, m.saturating_add(1))) {
            // NotEscapeSequence :: 0 DecimalDigit
            values.defined = false;
            e = m.saturating_add(2);
        } else {
            // TemplateEscapeSequence :: 0 [lookahead ∉ DecimalDigit]
            values.cooked.push(0);
            e = m.saturating_add(1);
        }
    } else if is_dec(d) {
        // NotEscapeSequence :: DecimalDigit but not 0
        values.defined = false;
        e = m.saturating_add(1);
    } else if d == 0x78 {
        let a = peek(src, m.saturating_add(1));
        let b = peek(src, m.saturating_add(2));
        if is_hex(a) && is_hex(b) {
            // HexEscapeSequence
            values.cooked.push(hex_val(a).saturating_mul(16).saturating_add(hex_val(b)) as u16);
            e = m.saturating_add(3);
        } else if is_hex(a) {
            // NotEscapeSequence :: x HexDigit [lookahead ∉ HexDigit]
            values.defined = false;
            e = m.saturating_add(2);
        } else {
            // NotEscapeSequence :: x [lookahead ∉ HexDigit]
            values.defined = false;
            e = m.saturating_add(1);
        }
    } else if d == 0x75 {
        match scan_unicode_escape(src, m) {
            Some((cp, end)) => {
                // UnicodeEscapeSequence
                push_utf16(&mut values.cooked, cp);
                e = end;
            },
            None => {
                // NotEscapeSequence, alternatives 5 to 11: `u` and the hex
                // digits that follow (up to three), or `u{` and all of
                // them; each ends where no further hex digit follows.
                values.defined = false;
                if peek(src, m.saturating_add(1)) == 0x7B {
                    let (_, h) = scan_hex_digits(src, m.saturating_add(2));
                    e = h;
                } else {
                    let mut h = m.saturating_add(1);
                    while is_hex(peek(src, h)) && h < m.saturating_add(4)
                        invariant
                            m < h <= src.len(),
                        decreases src.len() - h,
                    {
                        h = h.saturating_add(1);
                    }
                    e = h;
                }
            },
        }
    } else if is_src(d) {
        // CharacterEscapeSequence :: NonEscapeCharacter
        push_utf16(&mut values.cooked, d);
        e = m.saturating_add(1);
    } else {
        return None;
    }
    push_range_utf16(&mut values.raw, src, k, e);
    Some(e)
}

/// What [`scan_template`] finds: whether the component closes with `` ` ``,
/// its TV (`None` for *undefined*), its TRV, and its end.
type TemplateScan = (bool, Option<Vec<u16>>, Vec<u16>, usize);

/// §12.9.6 a template component at `k` (`` ` `` for `NoSubstitutionTemplate`
/// and `TemplateHead`, `}` for `TemplateMiddle` and `TemplateTail`): whether
/// it closes with `` ` `` (rather than `${`), its TV and TRV, and its end.
fn scan_template(src: &[u32], k: usize) -> (r: Option<TemplateScan>)
    requires
        k < src.len(),
    ensures
        match r {
            Some((_, _, _, e)) => k + 2 <= e <= src.len(),
            None => true,
        },
{
    let mut values = TemplateValues { cooked: Vec::new(), defined: true, raw: Vec::new() };
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x60 || (c == 0x24 && peek(src, j.saturating_add(1)) == 0x7B) {
            let closes = c == 0x60;
            let end = if closes {
                j.saturating_add(1)
            } else {
                j.saturating_add(2)
            };
            let cooked = if values.defined {
                Some(values.cooked)
            } else {
                None
            };
            return Some((closes, cooked, values.raw, end));
        } else if c == 0x5C {
            match scan_template_escape(src, j, &mut values) {
                Some(e) => {
                    j = e;
                },
                None => {
                    return None;
                },
            }
        } else if is_lt(c) {
            // LineTerminatorSequence: TV and TRV are its TRV.
            let e = line_terminator_sequence_end(src, j);
            let u: u16 = if c == 0x2028 || c == 0x2029 {
                c as u16
            } else {
                0x0A
            };
            values.cooked.push(u);
            values.raw.push(u);
            j = e;
        } else if is_src(c) {
            // `$` [lookahead ≠ {], or SourceCharacter but not one of ` \ $
            // LineTerminator: UTF16EncodeCodePoint of it.
            push_utf16(&mut values.cooked, c);
            push_utf16(&mut values.raw, c);
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

// ---------------------------------------------------------------------
// §12 The goal symbols and the longest input element.
// ---------------------------------------------------------------------

/// The goal has `RegularExpressionLiteral`.
fn goal_regexp(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementRegExp || goal == Goal::InputElementRegExpOrTemplateTail
            || goal == Goal::InputElementHashbangOrRegExp),
{
    matches!(
        goal,
        Goal::InputElementRegExp | Goal::InputElementRegExpOrTemplateTail
            | Goal::InputElementHashbangOrRegExp
    )
}

/// The goal has `DivPunctuator`.
fn goal_div(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementDiv || goal == Goal::InputElementTemplateTail),
{
    matches!(goal, Goal::InputElementDiv | Goal::InputElementTemplateTail)
}

/// The goal has `RightBracePunctuator`.
fn goal_right_brace(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementDiv || goal == Goal::InputElementRegExp),
{
    matches!(goal, Goal::InputElementDiv | Goal::InputElementRegExp)
}

/// The goal has `TemplateSubstitutionTail`.
fn goal_template_tail(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementRegExpOrTemplateTail || goal
            == Goal::InputElementTemplateTail),
{
    matches!(goal, Goal::InputElementRegExpOrTemplateTail | Goal::InputElementTemplateTail)
}

/// An element with no value.
fn plain(kind: ElementKind, start: usize, end: usize) -> (r: Element)
    requires
        !(kind == ElementKind::IdentifierName || kind == ElementKind::PrivateIdentifier || kind
            == ElementKind::StringLiteral || kind == ElementKind::NumericLiteral || kind
            == ElementKind::RegularExpressionLiteral || kind == ElementKind::Template(
            TemplateKind::NoSubstitution,
        ) || kind == ElementKind::Template(TemplateKind::Head) || kind == ElementKind::Template(
            TemplateKind::Middle,
        ) || kind == ElementKind::Template(TemplateKind::Tail)),
    ensures
        r.kind == kind,
        r.start == start,
        r.end == end,
        value_shape_agrees(r),
{
    Element { kind, start, end, value: Value::None }
}

/// An element and the error that the checks after the longest element is
/// chosen raise for it, if any (§12.9.3, §12.7.1.1; [`lex_error`]).
type Candidate = (Element, Option<LexError>);

/// The candidate's element is a non-empty range at `pos`.
pub open spec fn candidate_ok(src: Seq<u32>, pos: usize, c: (Element, Option<LexError>)) -> bool {
    c.0.start == pos && pos < c.0.end <= src.len() && value_shape_agrees(c.0)
}

/// [`candidate_ok`], and [`kind_agrees_proven`] in the goal.
pub open spec fn candidate_agrees(
    goal: Goal,
    html: bool,
    src: Seq<u32>,
    pos: usize,
    c: (Element, Option<LexError>),
) -> bool {
    candidate_ok(src, pos, c) && kind_agrees_proven(goal, html, src, c.0)
}

/// The longer of two candidates (the first on a tie).
fn longer(a: Option<Candidate>, b: Option<Candidate>) -> (r: Option<Candidate>)
    ensures
        match a {
            Some(x) => match b {
                Some(y) => r == Some(x) || r == Some(y),
                None => r == Some(x),
            },
            None => r == b,
        },
{
    match (a, b) {
        (Some(x), Some(y)) => {
            if y.0.end > x.0.end {
                Some(y)
            } else {
                Some(x)
            }
        },
        (Some(x), None) => Some(x),
        (None, y) => y,
    }
}

/// A comment that starts with `/` at `pos`: `//` (§12.4
/// `SingleLineComment`) or `/*` (§12.4 `MultiLineComment`; with `html`,
/// Annex B.1.1's `SingleLineDelimitedComment`, or its `MultiLineComment`
/// with an optional `HTMLCloseComment` after the `*/` when the comment
/// holds a `LineTerminator`).
fn lex_slash_comment(src: &[u32], pos: usize, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind == ElementKind::Comment,
            None => true,
        },
{
    let c1 = peek(src, pos.saturating_add(1));
    if c1 == 0x2F {
        let e = scan_line_chars(src, pos.saturating_add(2));
        Some((plain(ElementKind::Comment, pos, e), None))
    } else if c1 == 0x2A {
        match scan_block_comment(src, pos.saturating_add(2), true) {
            Some((e, lt)) => {
                let end = if html && lt {
                    match scan_html_close(src, e) {
                        Some(f) => f,
                        None => e,
                    }
                } else {
                    e
                };
                Some((plain(ElementKind::Comment, pos, end), None))
            },
            None => None,
        }
    } else {
        None
    }
}

/// Every alternative of `goal` that can start with the code point at
/// `pos`, the longest of them.
fn lex_common(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        match r {
            Some(c) => candidate_agrees(goal, html, src@, pos, c),
            None => true,
        },
{
    let c = peek(src, pos);
    let c1 = peek(src, pos.saturating_add(1));
    if is_ws(c) {
        // WhiteSpace
        assert(white_space(src@, pos as int, pos + 1));
        Some((plain(ElementKind::WhiteSpace, pos, pos.saturating_add(1)), None))
    } else if is_lt(c) {
        // LineTerminator; with `html`, Annex B.1.1's
        // SingleLineHTMLCloseComment :: LineTerminatorSequence
        // HTMLCloseComment, which is longer when it matches.
        let lt = Some((plain(ElementKind::LineTerminator, pos, pos.saturating_add(1)), None));
        if html {
            let s = line_terminator_sequence_end(src, pos);
            longer(lt, html_close_candidate(src, pos, s))
        } else {
            lt
        }
    } else if c == 0x2F {
        // Comment, RegularExpressionLiteral or DivPunctuator.
        let comment = lex_slash_comment(src, pos, html);
        let regexp = if goal_regexp(goal) {
            regexp_candidate(src, pos)
        } else {
            None
        };
        let div = if goal_div(goal) {
            let e = if c1 == 0x3D {
                // DivPunctuator :: `/=`
                assert(src@.subrange(pos as int, pos + 2) =~= seq!['/', '='].map_values(
                    |c: char| c as u32,
                ));
                pos.saturating_add(2)
            } else {
                // DivPunctuator :: `/`
                assert(src@.subrange(pos as int, pos + 1) =~= seq!['/'].map_values(
                    |c: char| c as u32,
                ));
                pos.saturating_add(1)
            };
            assert(div_punctuator(src@, pos as int, e as int));
            Some((plain(ElementKind::DivPunctuator, pos, e), None))
        } else {
            None
        };
        longer(longer(comment, regexp), div)
    } else if c == 0x7D {
        // TemplateMiddle / TemplateTail or RightBracePunctuator.
        if goal_template_tail(goal) {
            lex_template(src, pos, true)
        } else if goal_right_brace(goal) {
            // RightBracePunctuator :: `}`
            assert(src@.subrange(pos as int, pos + 1) =~= seq!['}'].map_values(
                |c: char| c as u32,
            ));
            assert(right_brace_punctuator(src@, pos as int, pos + 1));
            Some((plain(ElementKind::RightBracePunctuator, pos, pos.saturating_add(1)), None))
        } else {
            None
        }
    } else if c == 0x60 {
        // NoSubstitutionTemplate / TemplateHead
        lex_template(src, pos, false)
    } else if c == 0x22 || c == 0x27 {
        // StringLiteral
        let (units, e) = scan_string(src, pos)?;
        Some(
            (
                Element {
                    kind: ElementKind::StringLiteral,
                    start: pos,
                    end: e,
                    value: Value::String { units },
                },
                None,
            ),
        )
    } else if c == 0x23 {
        // PrivateIdentifier :: # IdentifierName
        match scan_identifier(src, pos.saturating_add(1)) {
            Some((cps, escaped, valid, e)) => {
                let err = if valid {
                    None
                } else {
                    Some(LexError::InvalidIdentifierEscape)
                };
                Some(
                    (
                        Element {
                            kind: ElementKind::PrivateIdentifier,
                            start: pos,
                            end: e,
                            value: Value::Name { code_points: cps, escaped },
                        },
                        err,
                    ),
                )
            },
            None => None,
        }
    } else if is_dec(c) || (c == 0x2E && is_dec(c1)) {
        // NumericLiteral
        match scan_numeric(src, pos) {
            Some((e, bigint, legacy)) => {
                let err = if numeric_follow_error(src, e) {
                    Some(LexError::IdentifierAfterNumericLiteral)
                } else {
                    None
                };
                Some(
                    (
                        Element {
                            kind: ElementKind::NumericLiteral,
                            start: pos,
                            end: e,
                            value: Value::Numeric { bigint, legacy },
                        },
                        err,
                    ),
                )
            },
            None => None,
        }
    } else if c == 0x5C || id_start_char(c) {
        // IdentifierName
        match scan_identifier(src, pos) {
            Some((cps, escaped, valid, e)) => {
                let err = if valid {
                    None
                } else {
                    Some(LexError::InvalidIdentifierEscape)
                };
                Some(
                    (
                        Element {
                            kind: ElementKind::IdentifierName,
                            start: pos,
                            end: e,
                            value: Value::Name { code_points: cps, escaped },
                        },
                        err,
                    ),
                )
            },
            None => None,
        }
    } else if html && c == 0x3C && c1 == 0x21 && peek(src, pos.saturating_add(2)) == 0x2D && peek(
        src,
        pos.saturating_add(3),
    ) == 0x2D {
        // Annex B.1.1 SingleLineHTMLOpenComment :: <!-- SingleLineCommentChars?
        let e = scan_line_chars(src, pos.saturating_add(4));
        Some((plain(ElementKind::Comment, pos, e), None))
    } else {
        // Punctuator
        let e = scan_punctuator(src, pos);
        if e > pos {
            Some((plain(ElementKind::Punctuator, pos, e), None))
        } else {
            None
        }
    }
}

/// A template component at `pos`: `NoSubstitutionTemplate` or
/// `TemplateHead` after `` ` ``, `TemplateTail` or `TemplateMiddle` after
/// `}` (`substitution_tail`).
fn lex_template(src: &[u32], pos: usize, substitution_tail: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind is Template,
            None => true,
        },
{
    match scan_template(src, pos) {
        Some((closes, cooked, raw, e)) => {
            let kind = if substitution_tail {
                if closes {
                    TemplateKind::Tail
                } else {
                    TemplateKind::Middle
                }
            } else {
                if closes {
                    TemplateKind::NoSubstitution
                } else {
                    TemplateKind::Head
                }
            };
            Some(
                (
                    Element {
                        kind: ElementKind::Template(kind),
                        start: pos,
                        end: e,
                        value: Value::Template { cooked, raw },
                    },
                    None,
                ),
            )
        },
        None => None,
    }
}

/// The alternatives of `InputElementHashbangOrRegExp` that match only at
/// the start of the source text: `HashbangComment` (§12.5) and, with
/// `html`, Annex B.1.1's `HTMLCloseComment`.
fn lex_start(src: &[u32], html: bool) -> (r: Option<Candidate>)
    requires
        0 < src.len(),
    ensures
        match r {
            Some(c) => candidate_agrees(Goal::InputElementHashbangOrRegExp, html, src@, 0, c),
            None => true,
        },
{
    let hashbang = if peek(src, 0) == 0x23 && peek(src, 1) == 0x21 {
        // §12.5 HashbangComment :: `#!` SingleLineCommentChars?
        let e = scan_line_chars(src, 2);
        assert(src@.subrange(0, 2) =~= seq!['#', '!'].map_values(|c: char| c as u32));
        assert(hashbang_comment(src@, 0, e as int));
        Some((plain(ElementKind::HashbangComment, 0, e), None))
    } else {
        None
    };
    let close = if html {
        html_close_candidate(src, 0, 0)
    } else {
        None
    };
    longer(hashbang, close)
}

/// A `Comment` from `pos` to the end of the Annex B.1.1 `HTMLCloseComment`
/// at `k`, if one is there.
fn html_close_candidate(src: &[u32], pos: usize, k: usize) -> (r: Option<Candidate>)
    requires
        pos <= k <= src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind == ElementKind::Comment,
            None => true,
        },
{
    let e = scan_html_close(src, k)?;
    Some((plain(ElementKind::Comment, pos, e), None))
}

/// A `RegularExpressionLiteral` at `pos`, if one is there.
fn regexp_candidate(src: &[u32], pos: usize) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind
                == ElementKind::RegularExpressionLiteral,
            None => true,
        },
{
    let (b, e) = scan_regexp(src, pos)?;
    Some(
        (
            Element {
                kind: ElementKind::RegularExpressionLiteral,
                start: pos,
                end: e,
                value: Value::RegExp { body_end: b },
            },
            None,
        ),
    )
}

/// The next input element of `goal` at `pos`, trivia included (§12): the
/// longest alternative, then the checks [`lex_error`] makes of it.
///
/// Proven: [`next_input_element_proven`] (totality and span coverage).
/// Not proven: the rest of [`super::contract::next_input_element_ensures`];
/// see the module header.
pub fn next_input_element(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Result<
    Step,
    LexError,
>)
    requires
        pos <= src.len(),
    ensures
        next_input_element_proven(src@, pos, goal, html, r),
{
    if pos >= src.len() {
        return Ok(Step::Eof);
    }
    let common = lex_common(src, pos, goal, html);
    let best = if pos == 0 && matches!(goal, Goal::InputElementHashbangOrRegExp) {
        longer(common, lex_start(src, html))
    } else {
        common
    };
    match best {
        None => Err(LexError::NoInputElement),
        Some((el, None)) => Ok(Step::Element(el)),
        Some((_, Some(e))) => Err(e),
    }
}

/// Whether a code point of `src[i..j)` is a `LineTerminator`: whether the
/// trivia element on that range "is a LineTerminator" for the syntactic
/// grammar (§12.3, §12.4, Annex B.1.1).
fn range_has_lt(src: &[u32], i: usize, j: usize) -> (r: bool)
    requires
        i <= j <= src.len(),
    ensures
        r == contains_line_terminator(src@, i as int, j as int),
{
    let mut k = i;
    while k < j
        invariant
            i <= k <= j <= src.len(),
            forall|m: int| i <= m < k ==> !is_line_terminator(#[trigger] src@[m]),
        decreases j - k,
    {
        if is_lt(peek(src, k)) {
            return true;
        }
        k = k.saturating_add(1);
    }
    false
}

/// Whether an element kind is trivia ([`is_trivia`]).
fn trivia(kind: ElementKind) -> (r: bool)
    ensures
        r == is_trivia(kind),
{
    matches!(
        kind,
        ElementKind::WhiteSpace | ElementKind::LineTerminator | ElementKind::Comment
            | ElementKind::HashbangComment
    )
}

/// The next token of `goal` at `pos`: [`next_input_element`] repeated over
/// trivia, with the line-terminator flag ASI needs (§12.10).
///
/// Proven: [`next_token_proven`]. Not proven: the rest of
/// [`super::contract::next_token_ensures`]; see the module header.
pub fn next_token(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Result<Next, LexError>)
    requires
        pos <= src.len(),
    ensures
        next_token_proven(src@, pos, goal, html, r),
{
    let mut p = pos;
    let mut newline = false;
    loop
        invariant
            pos <= p <= src.len(),
            newline ==> contains_line_terminator(src@, pos as int, p as int),
        decreases src.len() - p,
    {
        match next_input_element(src, p, goal, html) {
            Err(e) => {
                return Err(e);
            },
            Ok(Step::Eof) => {
                return Ok(Next::Eof { newline_before: newline });
            },
            Ok(Step::Element(el)) => {
                if trivia(el.kind) {
                    if range_has_lt(src, el.start, el.end) {
                        newline = true;
                    }
                    p = el.end;
                } else {
                    return Ok(Next::Token(Token { element: el, newline_before: newline }));
                }
            },
        }
    }
}

} // verus!
