//! A second transcription of CSS Syntax Level 3, written from the standard
//! alone: CSS Syntax Module Level 3, Editor's Draft, `css-syntax-3/Overview.bs`
//! of `w3c/csswg-drafts` at commit `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`
//! (2026-10-20), the commit the crate's `spec.rs` files cite. The text was read
//! from that commit's raw file, not from this crate. It is the same text the spec
//! transcribes, not a different one (phase-5.md item 5.4 proposed CSS 2.1 §4.1.1,
//! §4.2 and Appendix G as the second text, "proven equal where the two texts decide
//! the same"; the brief for this file asked for the pinned standard itself, and this
//! file does that). So a misreading of the standard that both transcriptions share
//! is not found by this file; what it finds is a misreading by one of them.
//!
//! This file holds the tokenizer (§4, and §3.3 "filter code points"); the parser
//! (§5) is in [`parse`]. The equivalence with the spec is in the `equiv_*` modules,
//! which were written after the definitions had been committed (`aa0567aa`).
//!
//! ## How the definitions were written
//!
//! The definitions (this file and [`parse`], from the top to their end) were written
//! from the standard's text alone, in a session that had not read `spec.rs` (of
//! `input`, `tokenizer` or `parser`), `contract.rs`, `lemmas.rs`, `termination.rs`,
//! `exec*.rs`, `examples.rs`, `rows.rs`, `mutations.json`, this crate's `README.md`
//! or its `tests/`. That session read this crate's `Cargo.toml`, `lib.rs` and the
//! one-paragraph headers of its `mod.rs` files; the headers of
//! `clazel-displaylist`'s, `clazel-der`'s and `clazel-treebuilder`'s `independent.rs`
//! for their shape; `docs/SPEC-STYLE.md`, `docs/VERIFICATION.md`, the paragraph of
//! `docs/phases/phase-5.md` that plans this file (item 5.4) with the status row
//! beside it, `docs/STATUS.md`'s row for this crate, and the headings of
//! `docs/ERRATA.md` (the entry "CSS Syntax §5.5.5" was found by them: it says the
//! standard's "consume a block's contents" never appends its last declarations; the
//! definitions here specify the evident intent too, see [`parse`]). It saw three
//! leaks of the spec, none of them an algorithm: a `grep` for the commit pin printed
//! the pin and the section anchors from the doc comments of the `spec.rs` files;
//! Verus's warnings from a build printed, as part of a lint about enum fields, the
//! declarations (doc comments kept, variant bodies elided) of the spec's `Rule` and
//! `Token` enums; and a tail of that output showed a fragment of a warning. That
//! showed that the spec's `Rule` has a `child_rules` field that is `None` for a
//! statement at-rule and that its `Token` has a variant `Eof`; nothing in the
//! definitions depends on either. From then on Verus's output was filtered so that
//! only errors that point into `independent*` files printed. One attempt to print a
//! file of the forbidden list (`input/lemmas.rs`) was refused by the tool's
//! permission layer and returned nothing.
//!
//! Those definitions were committed on their own (`aa0567aa`). Since that commit they
//! have changed in no definition: apart from this header and the list of `mod` lines
//! below, [`parse`] and this file are as committed. Only then were
//! `tokenizer/spec.rs`, `parser/spec.rs` (to the An+B part), `tokenizer/termination.rs`
//! and `parser/termination.rs` read, to write the `equiv_*` modules, which necessarily
//! name the spec's items. The equivalence proofs found no place where the two
//! transcriptions disagree: no definition on either side had to change.
//!
//! ## What the equivalence says
//!
//! For every stream of code points `s` with no value above U+10FFFF (the
//! precondition the spec itself states), after mapping the spec's results by
//! [`equiv_base::ints`], [`equiv_tokenizer::tok_of`], [`equiv_map`] and
//! [`equiv_tokenizer::inum_of`]:
//!
//! - [`equiv_tokenizer::theorem_filter_equals`]: "filter code points" agrees, for
//!   any string of code points, and [`equiv_tokenizer::lemma_filter_valid`] shows its
//!   output is a stream of code points;
//! - [`equiv_tokenizer::theorem_tokenize_equals`]: "tokenize" agrees, token by token,
//!   with the spec's final `<EOF-token>` removed, with and without |unicode ranges
//!   allowed|; each algorithm of §4.3 in between has its own theorem
//!   ([`equiv_tokenizer::theorem_token_equal`], `theorem_number_equal`,
//!   `theorem_escaped_equal`, `theorem_name_equal`, `theorem_string_equal`,
//!   `theorem_url_equal`, `theorem_ident_like_equal`, `theorem_unicode_range_equal`,
//!   `theorem_comments_equal`, ...), and [`equiv_tokenizer::lemma_spans_loop_equal`]
//!   says the positions the spec gives each token are the ones [`Lex`] has;
//! - [`equiv_parser::lemma_component_value_equal`], `lemma_simple_block_loop_equal`,
//!   `lemma_function_loop_equal`, `lemma_list_loop_equal`, `lemma_remnants_equal`,
//!   `lemma_declaration_equal`, `lemma_at_rule_loop_equal`,
//!   `lemma_qualified_rule_loop_equal`, `lemma_block_equal`,
//!   `lemma_contents_loop_equal`, `lemma_stylesheet_loop_equal`,
//!   `lemma_declarations_loop_equal` and `lemma_comma_loop_equal`: each algorithm of
//!   §5.4, at every position of a stream the tokenizer made, returns the mapped result
//!   at the same index;
//! - the entry points, on a string, in [`equiv_parser`]:
//!   `theorem_parse_stylesheet_contents_equals`, `theorem_parse_stylesheet_equals`,
//!   `theorem_parse_list_of_declarations_equals`, `theorem_parse_rule_equals`,
//!   `theorem_parse_declaration_equals`, `theorem_parse_component_value_equals`,
//!   `theorem_parse_list_of_component_values_equals` and
//!   `theorem_parse_comma_separated_list_equals`.
//!
//! What it does not say:
//!
//! - It compares the independent transcription's numbers with the spec's through
//!   [`equiv_tokenizer::inum_of`], which reads a sign, a mantissa, a fraction length
//!   and an exponent off the spec's strings (its own `unsigned`, `point_of` and
//!   `digits_value`), not through the spec's `number_value`. So a number is equal
//!   when those four agree (they determine the value); leading zeros and the
//!   percentage's type flag, which the spec keeps and the standard drops, are not
//!   compared.
//! - The input byte stream (§3.2), the An+B microsyntax (§6), serialization (§9), the
//!   grammar hooks of §5.3.1 and entry points on token or component-value lists are
//!   not transcribed here, so nothing is proven about them by this file.
//! - "Valid in the current context" is true on both sides (a modelling choice both
//!   transcriptions make), and "original source text" is the filtered string on both.
//! - The theorems hold for streams with the shape [`equiv_stream::shaped`] gives,
//!   which [`equiv_parser::lemma_token_stream_shaped`] proves of every stream the
//!   tokenizer makes (including the inner one of a unicode-range value).
//! - Two transcriptions of one text by two sessions of one model can share a
//!   misreading; this shows only that they say the same.
//!
//! ## Modelling choices
//!
//! - Code points are `int`. The end of the stream (the standard's EOF code
//!   point) is the value [`EOF`], which is no code point; position `p` of a
//!   stream is "the next input code point is `s[p]`", and any position at or
//!   past the end reads EOF. "Reconsume" is not advancing; consuming EOF does
//!   not advance either.
//! - The stream is a `Seq<int>` and a position, never a consumed prefix. Each
//!   "consume ..." algorithm is a function of the stream and the position at
//!   which it starts, and returns what it returns together with the position
//!   after what it consumed. "Repeatedly consume ..." loops are recursions.
//! - A loop step that must consume something is written through [`fwd`], so
//!   that a recursion visibly goes forward: `fwd(p, e)` is `e` when `e > p`,
//!   which every use has (the equivalence proofs rely on that), and `p + 1`
//!   otherwise.
//! - Parse errors are not recorded, as the standard attaches no behaviour to
//!   them besides "return" or "continue", which are written as such.
//! - A numeric value is exact, and kept as the digits the standard
//!   interprets: [`INum`] is a sign character, a mantissa (the digits of the
//!   number part, without the point, as an integer), the number of digits
//!   after the point and an exponent; the value is
//!   `sign * mantissa * 10^(exponent - fraction digits)`.
//! - Tokens carry the positions they were consumed from ([`Lex`]), because the
//!   parser needs "the segment of the original source text string
//!   corresponding to the tokens" of a declaration's value (§5.4.7). The
//!   start is after the comments that precede a token, the end is after it.
//! - The standard's `<EOF-token>` is a token ([`ITok::Eof`]) that
//!   [`i_consume_token`] returns at the end and [`i_tokenize`] does not
//!   push.

#[allow(unused_imports)]
use vstd::prelude::*;

pub mod equiv_base;
pub mod equiv_bounds;
pub mod equiv_map;
pub mod equiv_parser;
pub mod equiv_stream;
pub mod equiv_tokenizer;
pub mod parse;

verus! {

/// The standard's EOF code point: the value of the next input code point when
/// the stream is empty. It is below every code point.
pub open spec fn EOF() -> int { -1 }

/// A position of a stream `s`: the code point at `p`, EOF at and past the end.
pub open spec fn i_at(s: Seq<int>, p: nat) -> int {
    if p < s.len() { s[p as int] } else { EOF() }
}

/// "A loop step that must consume something": `e`, or `p + 1` when `e` is not
/// past `p` (it always is).
pub open spec fn fwd(p: nat, e: nat) -> nat {
    if e > p { e } else { (p + 1) as nat }
}

// ---------------------------------------------------------------------
// §4.2 Definitions

/// "digit": U+0030 to U+0039 inclusive.
pub open spec fn i_digit(c: int) -> bool { 0x30 <= c && c <= 0x39 }

/// "hex digit": a digit, U+0041 to U+0046, or U+0061 to U+0066 inclusive.
pub open spec fn i_hex_digit(c: int) -> bool {
    i_digit(c) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
}

/// "uppercase letter".
pub open spec fn i_uppercase(c: int) -> bool { 0x41 <= c && c <= 0x5A }

/// "lowercase letter".
pub open spec fn i_lowercase(c: int) -> bool { 0x61 <= c && c <= 0x7A }

/// "letter".
pub open spec fn i_letter(c: int) -> bool { i_uppercase(c) || i_lowercase(c) }

/// "non-ASCII ident code point", the list of the standard, all ranges inclusive.
pub open spec fn i_non_ascii_ident(c: int) -> bool {
    c == 0xB7
        || (0xC0 <= c && c <= 0xD6)
        || (0xD8 <= c && c <= 0xF6)
        || (0xF8 <= c && c <= 0x37D)
        || (0x37F <= c && c <= 0x1FFF)
        || c == 0x200C
        || c == 0x200D
        || c == 0x203F
        || c == 0x2040
        || (0x2070 <= c && c <= 0x218F)
        || (0x2C00 <= c && c <= 0x2FEF)
        || (0x3001 <= c && c <= 0xD7FF)
        || (0xF900 <= c && c <= 0xFDCF)
        || (0xFDF0 <= c && c <= 0xFFFD)
        || c >= 0x10000
}

/// "ident-start code point": a letter, a non-ASCII ident code point, or U+005F.
pub open spec fn i_ident_start(c: int) -> bool {
    i_letter(c) || i_non_ascii_ident(c) || c == 0x5F
}

/// "ident code point": an ident-start code point, a digit, or U+002D.
pub open spec fn i_ident(c: int) -> bool {
    i_ident_start(c) || i_digit(c) || c == 0x2D
}

/// "non-printable code point": U+0000 to U+0008, U+000B, U+000E to U+001F,
/// or U+007F.
pub open spec fn i_non_printable(c: int) -> bool {
    (0x0 <= c && c <= 0x8) || c == 0xB || (0xE <= c && c <= 0x1F) || c == 0x7F
}

/// "newline": U+000A.
pub open spec fn i_newline(c: int) -> bool { c == 0xA }

/// "whitespace": a newline, U+0009 or U+0020.
pub open spec fn i_whitespace(c: int) -> bool { i_newline(c) || c == 0x9 || c == 0x20 }

/// "surrogate": U+D800 to U+DFFF.
pub open spec fn i_surrogate(c: int) -> bool { 0xD800 <= c && c <= 0xDFFF }

/// "maximum allowed code point": U+10FFFF.
pub open spec fn i_max_code_point() -> int { 0x10FFFF }

/// The value of a digit or hex digit code point.
pub open spec fn i_digit_value(c: int) -> nat {
    if i_digit(c) { (c - 0x30) as nat }
    else if 0x41 <= c && c <= 0x46 { (c - 0x41 + 10) as nat }
    else if 0x61 <= c && c <= 0x66 { (c - 0x61 + 10) as nat }
    else { 0 }
}

/// "base^e".
pub open spec fn i_pow(base: nat, e: nat) -> nat
    decreases e,
{
    if e == 0 { 1 } else { base * i_pow(base, (e - 1) as nat) }
}

/// The number the code points `s[a..b)` spell as digits of the given base
/// (most significant first); 0 for no code points.
pub open spec fn i_value(s: Seq<int>, a: nat, b: nat, base: nat) -> nat
    decreases b,
{
    if b <= a { 0 } else { i_value(s, a, (b - 1) as nat, base) * base + i_digit_value(i_at(s, (b - 1) as nat)) }
}

/// "ASCII lowercase" of a code point.
pub open spec fn i_ascii_lower(c: int) -> int {
    if i_uppercase(c) { c + 0x20 } else { c }
}

/// "ASCII case-insensitive match" of `a` for the lowercase string `lower`.
pub open spec fn i_ci_match(a: Seq<int>, lower: Seq<int>) -> bool {
    a.len() == lower.len() && forall|k: int| 0 <= k < a.len() ==> i_ascii_lower(a[k]) == lower[k]
}

// ---------------------------------------------------------------------
// §3.3 Preprocessing the input stream

/// "filter code points", from position `p` of `input`: "Replace any U+000D
/// CARRIAGE RETURN (CR) code points, U+000C FORM FEED (FF) code points, or
/// pairs of U+000D followed by U+000A in input by a single U+000A", and "any
/// U+0000 NULL or surrogate code points in input with U+FFFD".
pub open spec fn i_filter_from(input: Seq<int>, p: nat) -> Seq<int>
    decreases (if input.len() > p { input.len() - p } else { 0 }),
{
    if p >= input.len() {
        seq![]
    } else {
        let c = input[p as int];
        if c == 0xD && i_at(input, p + 1) == 0xA {
            seq![0xA as int] + i_filter_from(input, p + 2)
        } else if c == 0xD || c == 0xC {
            seq![0xA as int] + i_filter_from(input, p + 1)
        } else if c == 0 || i_surrogate(c) {
            seq![0xFFFD as int] + i_filter_from(input, p + 1)
        } else {
            seq![c] + i_filter_from(input, p + 1)
        }
    }
}

/// "filter code points" from a stream of (unfiltered) code points.
pub open spec fn i_filter(input: Seq<int>) -> Seq<int> { i_filter_from(input, 0) }

// ---------------------------------------------------------------------
// §4.1 Tokens

/// A sign character of a numeric token: "'+', '-', or missing".
pub ghost enum ISign {
    /// Missing.
    NoSign,
    /// "+".
    Plus,
    /// "-".
    Minus,
}

/// What "consume a number" returns apart from the type flag: the sign
/// character and the value as `sign * mantissa * 10^(exponent - frac_len)`
/// (see the header).
pub ghost struct INum {
    /// The sign character.
    pub sign: ISign,
    /// The digits of the number part, as an integer.
    pub mantissa: nat,
    /// How many of them are after the full stop.
    pub frac_len: nat,
    /// The exponent part as an integer (0 when there is none).
    pub exponent: int,
}

/// The tokens of §4.1.
pub ghost enum ITok {
    /// `<ident-token>`.
    Ident(Seq<int>),
    /// `<function-token>`.
    Function(Seq<int>),
    /// `<at-keyword-token>`.
    AtKeyword(Seq<int>),
    /// `<hash-token>` with its value and whether its type flag is "id".
    Hash(Seq<int>, bool),
    /// `<string-token>`.
    Str(Seq<int>),
    /// `<bad-string-token>`.
    BadStr,
    /// `<url-token>`.
    Url(Seq<int>),
    /// `<bad-url-token>`.
    BadUrl,
    /// `<delim-token>`.
    Delim(int),
    /// `<number-token>`, with its type flag: true for "integer".
    Number(INum, bool),
    /// `<percentage-token>`.
    Percentage(INum),
    /// `<dimension-token>`: value, type flag (true for "integer") and unit.
    Dimension(INum, bool, Seq<int>),
    /// `<unicode-range-token>`: starting and ending code point.
    UnicodeRange(int, int),
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
    /// `<EOF-token>`, the conceptual one.
    Eof,
}

/// A token and where the tokenizer consumed it from: `start..end` of the
/// stream, after the comments that preceded it.
pub ghost struct Lex {
    /// The token.
    pub tok: ITok,
    /// The position of its first code point.
    pub start: nat,
    /// The position after its last.
    pub end: nat,
}

// ---------------------------------------------------------------------
// §4.3 Tokenizer algorithms

/// §4.3.14 "check if two code points are a valid escape": "If the first code
/// point is not U+005C REVERSE SOLIDUS (\), return false. Otherwise, if the
/// second code point is a newline, return false. Otherwise, return true."
pub open spec fn i_valid_escape(a: int, b: int) -> bool {
    if a != 0x5C { false } else if i_newline(b) { false } else { true }
}

/// §4.3.10 "check if three code points would start an ident sequence".
pub open spec fn i_starts_ident(a: int, b: int, c: int) -> bool {
    if a == 0x2D {
        i_ident_start(b) || b == 0x2D || i_valid_escape(b, c)
    } else if i_ident_start(a) {
        true
    } else if a == 0x5C {
        i_valid_escape(a, b)
    } else {
        false
    }
}

/// §4.3.11 "check if three code points would start a number".
pub open spec fn i_starts_number(a: int, b: int, c: int) -> bool {
    if a == 0x2B || a == 0x2D {
        if i_digit(b) { true } else if b == 0x2E && i_digit(c) { true } else { false }
    } else if a == 0x2E {
        i_digit(b)
    } else if i_digit(a) {
        true
    } else {
        false
    }
}

/// §4.3.12 "check if three code points would start a unicode-range".
pub open spec fn i_starts_unicode_range(a: int, b: int, c: int) -> bool {
    (a == 0x55 || a == 0x75) && b == 0x2B && (c == 0x3F || i_hex_digit(c))
}

/// §4.3.2 "consume comments": at `p`, "If the next two input code point are
/// U+002F SOLIDUS (/) followed by a U+002A ASTERISK (*), consume them and all
/// following code points up to and including the first U+002A followed by a
/// U+002F, or up to an EOF code point. Return to the start of this step."
/// Returns the position after them.
pub open spec fn i_consume_comments(s: Seq<int>, p: nat) -> nat {
    p + i_comments_len(s, p)
}

/// How many code points the comments at `p` take, one comment after the other
/// ("Return to the start of this step").
pub open spec fn i_comments_len(s: Seq<int>, p: nat) -> nat
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    if i_at(s, p) == 0x2F && i_at(s, p + 1) == 0x2A {
        let n = 2 + i_comment_body_len(s, p + 2);
        n + i_comments_len(s, p + n)
    } else {
        0
    }
}

/// How many code points a comment takes from `q`, after its "/" "*": up to and
/// including the first "*" "/", or up to the end of the stream.
pub open spec fn i_comment_body_len(s: Seq<int>, q: nat) -> nat
    decreases (if s.len() > q { s.len() - q } else { 0 }),
{
    if q >= s.len() {
        0
    } else if s[q as int] == 0x2A && i_at(s, q + 1) == 0x2F {
        2
    } else {
        1 + i_comment_body_len(s, q + 1)
    }
}

/// "Consume as much whitespace as possible" from `p`: the position after it.
pub open spec fn i_whitespace_end(s: Seq<int>, p: nat) -> nat
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    if i_whitespace(i_at(s, p)) { i_whitespace_end(s, p + 1) } else { p }
}

/// "Consume as many digits as possible" from `p`: the position after them.
pub open spec fn i_digits_end(s: Seq<int>, p: nat) -> nat
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    if i_digit(i_at(s, p)) { i_digits_end(s, p + 1) } else { p }
}

/// "Consume as many hex digits as possible, but no more than `max`" from `p`:
/// how many were consumed.
pub open spec fn i_hex_run(s: Seq<int>, p: nat, max: nat) -> nat
    decreases max,
{
    if max > 0 && i_hex_digit(i_at(s, p)) { 1 + i_hex_run(s, p + 1, (max - 1) as nat) } else { 0 }
}

/// "Consume as many U+003F QUESTION MARK (?) code points as possible, but no
/// more than `max`" from `p`: how many were consumed.
pub open spec fn i_question_run(s: Seq<int>, p: nat, max: nat) -> nat
    decreases max,
{
    if max > 0 && i_at(s, p) == 0x3F { 1 + i_question_run(s, p + 1, (max - 1) as nat) } else { 0 }
}

/// §4.3.7 "consume an escaped code point", with the U+005C already consumed,
/// so `p` is the position of the next input code point. Returns the code point
/// and the position after what it consumed.
pub open spec fn i_consume_escaped(s: Seq<int>, p: nat) -> (int, nat) {
    let c = i_at(s, p);
    if i_hex_digit(c) {
        // "Consume as many hex digits as possible, but no more than 5."
        let more = i_hex_run(s, p + 1, 5);
        let after_digits = p + 1 + more;
        // "If the next input code point is whitespace, consume it as well."
        let after = if i_whitespace(i_at(s, after_digits)) { after_digits + 1 } else { after_digits };
        let n = i_value(s, p, after_digits, 16) as int;
        if n == 0 || i_surrogate(n) || n > i_max_code_point() { (0xFFFD, after) } else { (n, after) }
    } else if c == EOF() {
        (0xFFFD, p)
    } else {
        (c, p + 1)
    }
}

/// §4.3.9 "consume an ident sequence" from `p`: the string and the position
/// after it.
pub open spec fn i_consume_name(s: Seq<int>, p: nat) -> (Seq<int>, nat)
    decreases (if s.len() > p { s.len() - p } else { 0 }), 0nat,
{
    let c = i_at(s, p);
    if i_ident(c) {
        let rest = i_consume_name(s, p + 1);
        (seq![c] + rest.0, rest.1)
    } else if i_valid_escape(c, i_at(s, p + 1)) {
        let esc = i_consume_escaped(s, p + 1);
        let rest = i_consume_name(s, fwd(p, esc.1));
        (seq![esc.0] + rest.0, rest.1)
    } else {
        (seq![], p)
    }
}

/// §4.3.12 "consume a number" from `p`: the sign character and value, whether
/// the type is "integer", and the position after it.
pub open spec fn i_consume_number(s: Seq<int>, p: nat) -> (INum, bool, nat) {
    let ch = i_at(s, p);
    // 2. "If the next input code point is U+002B or U+002D, consume it."
    let has_sign = ch == 0x2B || ch == 0x2D;
    let sign = if ch == 0x2B { ISign::Plus } else if ch == 0x2D { ISign::Minus } else { ISign::NoSign };
    let a = if has_sign { p + 1 } else { p };
    // 3. "While the next input code point is a digit, consume it."
    let b = i_digits_end(s, a);
    // 4. "If the next 2 input code points are U+002E followed by a digit":
    let has_frac = i_at(s, b) == 0x2E && i_digit(i_at(s, b + 1));
    let c = if has_frac { i_digits_end(s, b + 1) } else { b };
    let frac_len = if has_frac { (c - b - 1) as nat } else { 0 };
    let mantissa = if has_frac {
        i_value(s, a, b, 10) * i_pow(10, frac_len) + i_value(s, b + 1, c, 10)
    } else {
        i_value(s, a, b, 10)
    };
    // 5. "If the next 2 or 3 input code points are U+0045 or U+0065, optionally
    // followed by U+002D or U+002B, followed by a digit":
    let e0 = i_at(s, c);
    let e1 = i_at(s, c + 1);
    let exp_signed = (e1 == 0x2B || e1 == 0x2D) && i_digit(i_at(s, c + 2));
    let has_exp = (e0 == 0x45 || e0 == 0x65) && (i_digit(e1) || exp_signed);
    let ds = if exp_signed { c + 2 } else { c + 1 };
    let de = i_digits_end(s, ds);
    let exp_mag = i_value(s, ds, de, 10) as int;
    let exponent = if !has_exp { 0 } else if e1 == 0x2D { -exp_mag } else { exp_mag };
    let end = if has_exp { de } else { c };
    (INum { sign, mantissa, frac_len, exponent }, !has_frac && !has_exp, end)
}

/// §4.3.3 "consume a numeric token" from `p`.
pub open spec fn i_consume_numeric(s: Seq<int>, p: nat) -> (ITok, nat) {
    let (num, integer, e) = i_consume_number(s, p);
    if i_starts_ident(i_at(s, e), i_at(s, e + 1), i_at(s, e + 2)) {
        let (unit, e2) = i_consume_name(s, e);
        (ITok::Dimension(num, integer, unit), e2)
    } else if i_at(s, e) == 0x25 {
        (ITok::Percentage(num), e + 1)
    } else {
        (ITok::Number(num, integer), e)
    }
}

/// §4.3.5 "consume a string token", with the opening quote consumed, so `p`
/// is the next input code point and `ending` the ending code point. Returns
/// the value, whether the token is a `<bad-string-token>` (then the value is
/// not used) and the position after what it consumed.
pub open spec fn i_consume_string(s: Seq<int>, p: nat, ending: int) -> (Seq<int>, bool, nat)
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    let c = i_at(s, p);
    if c == ending {
        (seq![], false, p + 1)
    } else if c == EOF() {
        (seq![], false, p)
    } else if i_newline(c) {
        // "Reconsume the current input code point, create a <bad-string-token>".
        (seq![], true, p)
    } else if c == 0x5C {
        let n = i_at(s, p + 1);
        if n == EOF() {
            // "do nothing"
            i_consume_string(s, p + 1, ending)
        } else if i_newline(n) {
            i_consume_string(s, p + 2, ending)
        } else {
            let esc = i_consume_escaped(s, p + 1);
            let rest = i_consume_string(s, fwd(p, esc.1), ending);
            (seq![esc.0] + rest.0, rest.1, rest.2)
        }
    } else {
        let rest = i_consume_string(s, p + 1, ending);
        (seq![c] + rest.0, rest.1, rest.2)
    }
}

/// §4.3.15 "consume the remnants of a bad url" from `p`: the position after
/// what it consumed.
pub open spec fn i_consume_bad_url_remnants(s: Seq<int>, p: nat) -> nat
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    let c = i_at(s, p);
    if c == 0x29 {
        p + 1
    } else if c == EOF() {
        p
    } else if i_valid_escape(c, i_at(s, p + 1)) {
        i_consume_bad_url_remnants(s, fwd(p, i_consume_escaped(s, p + 1).1))
    } else {
        i_consume_bad_url_remnants(s, p + 1)
    }
}

/// §4.3.6 "consume a url token", after the "url(" and the whitespace that
/// the step 2 consumes, with the value so far; `p` is the next input code
/// point of step 3's loop. Returns the token and the position after it.
pub open spec fn i_consume_url_rest(s: Seq<int>, p: nat, value: Seq<int>) -> (ITok, nat)
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    let c = i_at(s, p);
    if c == 0x29 {
        (ITok::Url(value), p + 1)
    } else if c == EOF() {
        (ITok::Url(value), p)
    } else if i_whitespace(c) {
        let q = i_whitespace_end(s, p);
        if i_at(s, q) == 0x29 {
            (ITok::Url(value), q + 1)
        } else if i_at(s, q) == EOF() {
            (ITok::Url(value), q)
        } else {
            (ITok::BadUrl, i_consume_bad_url_remnants(s, q))
        }
    } else if c == 0x22 || c == 0x27 || c == 0x28 || i_non_printable(c) {
        (ITok::BadUrl, i_consume_bad_url_remnants(s, p + 1))
    } else if c == 0x5C {
        if i_valid_escape(c, i_at(s, p + 1)) {
            let esc = i_consume_escaped(s, p + 1);
            i_consume_url_rest(s, fwd(p, esc.1), value + seq![esc.0])
        } else {
            (ITok::BadUrl, i_consume_bad_url_remnants(s, p + 1))
        }
    } else {
        i_consume_url_rest(s, p + 1, value + seq![c])
    }
}

/// §4.3.6 "consume a url token", with the "url(" consumed: `p` is the next
/// input code point.
pub open spec fn i_consume_url(s: Seq<int>, p: nat) -> (ITok, nat) {
    // 2. "Consume as much whitespace as possible."
    i_consume_url_rest(s, i_whitespace_end(s, p), seq![])
}

/// §4.3.4 "consume an ident-like token" from `p`.
pub open spec fn i_consume_ident_like(s: Seq<int>, p: nat) -> (ITok, nat) {
    let (name, e) = i_consume_name(s, p);
    if i_ci_match(name, seq![0x75 as int, 0x72, 0x6C]) && i_at(s, e) == 0x28 {
        // "consume it. While the next two input code points are whitespace,
        // consume the next input code point."
        let e1 = i_skip_double_whitespace(s, e + 1);
        let q = i_at(s, e1);
        let q2 = i_at(s, e1 + 1);
        if q == 0x22 || q == 0x27 || (i_whitespace(q) && (q2 == 0x22 || q2 == 0x27)) {
            (ITok::Function(name), e1)
        } else {
            i_consume_url(s, e1)
        }
    } else if i_at(s, e) == 0x28 {
        (ITok::Function(name), e + 1)
    } else {
        (ITok::Ident(name), e)
    }
}

/// "While the next two input code points are whitespace, consume the next input
/// code point", from `p`.
pub open spec fn i_skip_double_whitespace(s: Seq<int>, p: nat) -> nat
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    if i_whitespace(i_at(s, p)) && i_whitespace(i_at(s, p + 1)) {
        i_skip_double_whitespace(s, p + 1)
    } else {
        p
    }
}

/// §4.3.13 "consume a unicode-range token", from `p` where the stream
/// "would start a unicode-range".
pub open spec fn i_consume_unicode_range(s: Seq<int>, p: nat) -> (ITok, nat) {
    // 1. "Consume the next two input code points and discard them."
    let a = p + 2;
    // 2. hex digits, then question marks, to 6 in all.
    let digits = i_hex_run(s, a, 6);
    let questions = if digits < 6 { i_question_run(s, a + digits, (6 - digits) as nat) } else { 0 };
    let first_end = a + digits + questions;
    let first = i_value(s, a, a + digits, 16);
    if questions > 0 {
        // 3. "Replace the question marks with 0 ... with F".
        let lo = first * i_pow(16, questions);
        let hi = lo + i_pow(16, questions) - 1;
        (ITok::UnicodeRange(lo as int, hi as int), first_end)
    } else if i_at(s, first_end) == 0x2D && i_hex_digit(i_at(s, first_end + 1)) {
        // 5. "If the next 2 input code points are U+002D followed by a hex digit".
        let more = i_hex_run(s, first_end + 1, 6);
        (ITok::UnicodeRange(first as int, i_value(s, first_end + 1, first_end + 1 + more, 16) as int), first_end + 1 + more)
    } else {
        // 6.
        (ITok::UnicodeRange(first as int, first as int), first_end)
    }
}

/// §4.3.1 "consume a token" from `p`, after the comments (the first step is
/// [`i_consume_comments`]), given |unicode ranges allowed|. Returns the token
/// and the position after it.
pub open spec fn i_consume_token(s: Seq<int>, p: nat, unicode_ranges: bool) -> (ITok, nat) {
    let c = i_at(s, p);
    let n1 = i_at(s, p + 1);
    let n2 = i_at(s, p + 2);
    let n3 = i_at(s, p + 3);
    if i_whitespace(c) {
        (ITok::Whitespace, i_whitespace_end(s, p))
    } else if c == 0x22 {
        let (v, bad, e) = i_consume_string(s, p + 1, c);
        (if bad { ITok::BadStr } else { ITok::Str(v) }, e)
    } else if c == 0x23 {
        if i_ident(n1) || i_valid_escape(n1, n2) {
            let (name, e) = i_consume_name(s, p + 1);
            (ITok::Hash(name, i_starts_ident(n1, n2, n3)), e)
        } else {
            (ITok::Delim(c), p + 1)
        }
    } else if c == 0x27 {
        let (v, bad, e) = i_consume_string(s, p + 1, c);
        (if bad { ITok::BadStr } else { ITok::Str(v) }, e)
    } else if c == 0x28 {
        (ITok::OpenParen, p + 1)
    } else if c == 0x29 {
        (ITok::CloseParen, p + 1)
    } else if c == 0x2B {
        if i_starts_number(c, n1, n2) { i_consume_numeric(s, p) } else { (ITok::Delim(c), p + 1) }
    } else if c == 0x2C {
        (ITok::Comma, p + 1)
    } else if c == 0x2D {
        if i_starts_number(c, n1, n2) {
            i_consume_numeric(s, p)
        } else if n1 == 0x2D && n2 == 0x3E {
            (ITok::Cdc, p + 3)
        } else if i_starts_ident(c, n1, n2) {
            i_consume_ident_like(s, p)
        } else {
            (ITok::Delim(c), p + 1)
        }
    } else if c == 0x2E {
        if i_starts_number(c, n1, n2) { i_consume_numeric(s, p) } else { (ITok::Delim(c), p + 1) }
    } else if c == 0x3A {
        (ITok::Colon, p + 1)
    } else if c == 0x3B {
        (ITok::Semicolon, p + 1)
    } else if c == 0x3C {
        if n1 == 0x21 && n2 == 0x2D && n3 == 0x2D { (ITok::Cdo, p + 4) } else { (ITok::Delim(c), p + 1) }
    } else if c == 0x40 {
        if i_starts_ident(n1, n2, n3) {
            let (name, e) = i_consume_name(s, p + 1);
            (ITok::AtKeyword(name), e)
        } else {
            (ITok::Delim(c), p + 1)
        }
    } else if c == 0x5B {
        (ITok::OpenSquare, p + 1)
    } else if c == 0x5C {
        if i_valid_escape(c, n1) { i_consume_ident_like(s, p) } else { (ITok::Delim(c), p + 1) }
    } else if c == 0x5D {
        (ITok::CloseSquare, p + 1)
    } else if c == 0x7B {
        (ITok::OpenCurly, p + 1)
    } else if c == 0x7D {
        (ITok::CloseCurly, p + 1)
    } else if i_digit(c) {
        i_consume_numeric(s, p)
    } else if c == 0x55 || c == 0x75 {
        if unicode_ranges && i_starts_unicode_range(c, n1, n2) {
            i_consume_unicode_range(s, p)
        } else {
            i_consume_ident_like(s, p)
        }
    } else if i_ident_start(c) {
        i_consume_ident_like(s, p)
    } else if c == EOF() {
        (ITok::Eof, p)
    } else {
        (ITok::Delim(c), p + 1)
    }
}

/// §4 "tokenize" from `p`: "repeatedly consume a token from input until an
/// <EOF-token> is reached, pushing each of the returned tokens into a stream".
pub open spec fn i_tokenize_from(s: Seq<int>, p: nat, unicode_ranges: bool) -> Seq<Lex>
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    // §4.3.1 step 1: "Consume comments."
    let q = i_consume_comments(s, p);
    let (tok, e) = i_consume_token(s, q, unicode_ranges);
    if q >= s.len() || tok == ITok::Eof {
        seq![]
    } else {
        seq![Lex { tok, start: q, end: e }] + i_tokenize_from(s, fwd(q, e), unicode_ranges)
    }
}

/// §4 "tokenize" a stream of (filtered) code points, given |unicode ranges
/// allowed|.
pub open spec fn i_tokenize(s: Seq<int>, unicode_ranges: bool) -> Seq<Lex> {
    i_tokenize_from(s, 0, unicode_ranges)
}

} // verus!
