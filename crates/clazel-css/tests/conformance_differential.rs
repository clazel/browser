//! The tokenizer against Servo's `cssparser` (phase-5.md item 5.4), on random and mutated
//! sheets and every `css-parsing-tests` input. Tokens are compared here; rule structure is
//! not compared yet.
//!
//! `cssparser` hands out blocks and functions nested, so our tokens are nested the same
//! way first, as `tests/conformance_tokens.rs` does. Both engines read the same text,
//! after our "filter code points", so a difference is in tokenizing and not in
//! preprocessing.
//!
//! Known differences, each decided by the pinned text and each excused only where it
//! happens:
//! - `cssparser` has match tokens such as `~=`, from an older draft. They are read here
//!   as their two delim tokens, which is what the pinned text gives.
//! - It takes every non-ASCII code point into an ident, also from an older draft, where
//!   the pinned text lists ranges. Those outside the ranges of [`NON_ASCII_IDENT`], a
//!   table written in this file from the pinned text, become U+0001 for both engines, so
//!   the rest of such a sheet is still compared. That our tokenizer takes exactly those
//!   ranges into idents is tested on both sides of every boundary in
//!   `tests/ident_code_points.rs`.
//! - It takes `-` before a backslash and a newline as starting an ident, in
//!   `is_ident_start`: it looks for the newline at offset 1, which is the backslash, and
//!   not at offset 2. §4.3.9 needs "the second and third code points" to be a valid
//!   escape, and §4.3.8 says these are not. It shows in `cssparser`'s tokens only as a
//!   token that starts with that `-`: an ident `-`, an at-keyword `-`, an id hash `-`, or
//!   a unit `-`. [`undo_dash_before_escaped_newline`] rewrites exactly those, where a
//!   backslash delim and whitespace follow, into what the pinned text gives, and
//!   the sheet then has to agree everywhere else.
//! - It gives NaN for zero with a huge exponent, such as `0e99999999999999999999`: it
//!   works out 0 times infinity in floats. §4.3.12 step 6 multiplies by 10 to the power,
//!   which is exactly 0. A NaN is accepted only where our value is 0 and the text has an
//!   exponent.
//! - After whitespace in an unquoted url, its `consume_url_end` consumes the next byte
//!   before it looks for the remnants, so a backslash there is lost and `url(a \)b)` ends
//!   at the first `)`. §4.3.6 consumes the remnants from that code point, where `\)` is a
//!   valid escape. The random sheets never reach this (it is not excused, so one that did
//!   would fail); `known_difference_url_whitespace_backslash` pins both engines' tokens
//!   for the inputs that do.
//!
//! Numbers are compared as tightly as the two engines allow. `cssparser` adds up digits
//! in `f64` (`value * 10 + digit`, a fraction as `digit * 0.1^n`) and casts to `f32`;
//! we parse the exact text into `f64` and cast. The two `f32` have to be equal to the bit
//! (so the sign of zero and infinity are compared too), a percentage as the `f32` of
//! its value over 100 (`cssparser`'s `unit_value`), and the integer value of an
//! "integer" token exactly, saturated to `i32` as `cssparser` does. What remains
//! loose, and why: nothing in the corpus, but their `f64` sums are not exact for long
//! fractions, so a corpus with more of those may show a one-bit difference in `f32`.
//! If one does, it must be named here, with the bound, and not be allowed by default;
//! the `max_ulps` pin shows the largest difference seen (0 today).
//!
//! The corpus is fixed (a fixed seed and fixed lists), so the outcome is pinned: the
//! counts at the end of [`differential_tokens`] are asserted exactly. A change to the
//! generator, to a fragment or to either engine moves them; to update, run
//! `cargo test -p clazel-css --test conformance_differential -- --nocapture`, read the
//! `clazel-conformance:` line and the `pinned` line it prints, check that every new
//! difference is one of the classes above, and change the constants.
//!
//! Skipped under Miri (`#[cfg_attr(miri, ignore)]`, as `clazel-cookie`'s differential
//! is): `cssparser` has `unsafe` of its own, and our tokenizer has none and runs there
//! in `tests/conformance_tokens.rs`.

use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, filter, tokenize_all};
use cssparser::{ParseError, Parser, Token};
use std::iter::Peekable;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::vec::IntoIter;

/// The `css-parsing-tests` table.
mod syntax {
    use Json::{Bool, List, Null, Num, Obj, Str};

    /// A value of the suite's JSON, as the converter wrote it.
    #[derive(Debug, PartialEq)]
    pub enum Json {
        Null,
        Bool(bool),
        Num(&'static str),
        Str(&'static str),
        List(&'static [Json]),
        Obj(&'static [(&'static str, Json)]),
    }

    /// One case.
    pub struct Case {
        pub file: &'static str,
        pub index: usize,
        pub input: Json,
        pub expected: Json,
    }

    include!("generated/css_parsing_tests.rs");

    /// The table.
    pub fn cases() -> &'static [Case] {
        CASES
    }
}

/// A number's value and flags, as both engines can give them.
#[derive(Debug, Clone)]
struct Numeric {
    value: f32,
    /// The value of an "integer" token, saturated to `i32` (as `cssparser` does); `None`
    /// for a "number" token.
    int_value: Option<i32>,
    has_sign: bool,
    /// Whether the text had an exponent part. Ours only.
    has_exponent: bool,
}

/// How far apart two `f32` of one sign are, in units in the last place; `None` if
/// either is NaN, they differ in sign (zero included), or only one is infinite.
fn ulps(a: f32, b: f32) -> Option<u32> {
    if a.is_nan()
        || b.is_nan()
        || a.is_sign_negative() != b.is_sign_negative()
        || a.is_infinite() != b.is_infinite()
    {
        return None;
    }
    Some(a.abs().to_bits().abs_diff(b.abs().to_bits()))
}

/// Largest distance seen between two numbers that were accepted (always 0 now; kept so
/// that a number the tolerance would have hidden is not hidden by being forgotten).
static MAX_SEEN_ULPS: AtomicU32 = AtomicU32::new(0);
/// How many numbers `cssparser` gave as NaN where we give 0.
static NAN_FOR_ZERO: AtomicUsize = AtomicUsize::new(0);

/// `a` is ours and `b` is theirs.
fn same_number(a: &Numeric, b: &Numeric) -> bool {
    if a.has_sign != b.has_sign || a.int_value != b.int_value {
        return false;
    }
    if b.value.is_nan() {
        // Their 0 * infinity; see the module comment.
        let ok = a.value.abs().to_bits() == 0 && a.has_exponent;
        if ok {
            NAN_FOR_ZERO.fetch_add(1, Ordering::Relaxed);
        }
        return ok;
    }
    let Some(distance) = ulps(a.value, b.value) else {
        return false;
    };
    MAX_SEEN_ULPS.fetch_max(distance, Ordering::Relaxed);
    distance == 0
}

/// A token or block, in terms both engines share.
#[derive(Debug, Clone)]
enum Tree {
    Ident(String),
    AtKeyword(String),
    Hash(String, bool),
    QuotedString(String),
    Url(String),
    Delim(char),
    Number(Numeric),
    Percentage(Numeric),
    Dimension(Numeric, String),
    Function(String, Vec<Tree>),
    Block(char, Vec<Tree>),
    Close(char),
    Whitespace,
    Cdo,
    Cdc,
    Colon,
    Semicolon,
    Comma,
    BadString,
    BadUrl,
}

fn same_list(a: &[Tree], b: &[Tree]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same(a, b))
}

fn same(a: &Tree, b: &Tree) -> bool {
    use Tree::*;
    match (a, b) {
        (Ident(a), Ident(b))
        | (AtKeyword(a), AtKeyword(b))
        | (QuotedString(a), QuotedString(b))
        | (Url(a), Url(b)) => a == b,
        (Hash(a, x), Hash(b, y)) => a == b && x == y,
        (Delim(a), Delim(b)) | (Close(a), Close(b)) => a == b,
        (Number(a), Number(b)) | (Percentage(a), Percentage(b)) => same_number(a, b),
        (Dimension(a, x), Dimension(b, y)) => same_number(a, b) && x == y,
        (Function(a, x), Function(b, y)) => a == b && same_list(x, y),
        (Block(a, x), Block(b, y)) => a == b && same_list(x, y),
        (Whitespace, Whitespace)
        | (Cdo, Cdo)
        | (Cdc, Cdc)
        | (Colon, Colon)
        | (Semicolon, Semicolon)
        | (Comma, Comma)
        | (BadString, BadString)
        | (BadUrl, BadUrl) => true,
        _ => false,
    }
}

fn text(v: &[u32]) -> String {
    v.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// The integer `digits` (a sign and digits) denote, saturated to `i32`.
fn saturated(digits: &[u32]) -> i32 {
    let negative = digits.first() == Some(&0x2D);
    let magnitude = digits
        .iter()
        .filter_map(|c| c.checked_sub(0x30).filter(|d| *d < 10))
        .fold(0i64, |value, digit| {
            value
                .saturating_mul(10)
                .saturating_add(i64::from(digit))
                .min(1 << 33)
        });
    let signed = if negative {
        magnitude.saturating_neg()
    } else {
        magnitude
    };
    i32::try_from(signed.clamp(i64::from(i32::MIN), i64::from(i32::MAX))).unwrap_or(0)
}

/// §4.3.12 "interpreting … as a base-10 number", as `f32`. A percentage gives its value
/// divided by 100, which is what `cssparser` calls `unit_value`.
fn ours_number(number: &ExecNumber, percentage: bool) -> Numeric {
    let mut source = text(&number.number_part);
    if !number.exponent_part.is_empty() {
        source.push('e');
        source.push_str(&text(&number.exponent_part));
    }
    let exact_value = source.parse::<f64>().unwrap_or(f64::NAN);
    let value = if percentage {
        exact_value / 100.0
    } else {
        exact_value
    } as f32;
    Numeric {
        value,
        int_value: number.is_integer.then(|| saturated(&number.number_part)),
        has_sign: number.sign_character.is_some(),
        has_exponent: !number.exponent_part.is_empty(),
    }
}

/// Our tokens up to `closer` or the end, nested.
fn ours_list(tokens: &mut Peekable<IntoIter<ExecToken>>, closer: Option<&ExecToken>) -> Vec<Tree> {
    let mut out = Vec::new();
    while let Some(token) = tokens.next() {
        if closer == Some(&token) {
            return out;
        }
        out.extend(ours_tree(token, tokens));
    }
    out
}

fn ours_tree(token: ExecToken, tokens: &mut Peekable<IntoIter<ExecToken>>) -> Option<Tree> {
    Some(match token {
        ExecToken::Ident { value } => Tree::Ident(text(&value)),
        ExecToken::AtKeyword { value } => Tree::AtKeyword(text(&value)),
        ExecToken::Hash { value, is_id } => Tree::Hash(text(&value), is_id),
        ExecToken::String { value } => Tree::QuotedString(text(&value)),
        ExecToken::Url { value } => Tree::Url(text(&value)),
        ExecToken::Delim { value } => {
            Tree::Delim(char::from_u32(value).unwrap_or(char::REPLACEMENT_CHARACTER))
        }
        ExecToken::Number { number } => Tree::Number(ours_number(&number, false)),
        ExecToken::Percentage { number } => Tree::Percentage(ours_number(&number, true)),
        ExecToken::Dimension { number, unit } => {
            Tree::Dimension(ours_number(&number, false), text(&unit))
        }
        ExecToken::Function { value } => Tree::Function(
            text(&value),
            ours_list(tokens, Some(&ExecToken::CloseParen)),
        ),
        ExecToken::OpenParen => Tree::Block('(', ours_list(tokens, Some(&ExecToken::CloseParen))),
        ExecToken::OpenSquare => Tree::Block('[', ours_list(tokens, Some(&ExecToken::CloseSquare))),
        ExecToken::OpenCurly => Tree::Block('{', ours_list(tokens, Some(&ExecToken::CloseCurly))),
        ExecToken::CloseParen => Tree::Close(')'),
        ExecToken::CloseSquare => Tree::Close(']'),
        ExecToken::CloseCurly => Tree::Close('}'),
        ExecToken::Whitespace => Tree::Whitespace,
        ExecToken::Cdo => Tree::Cdo,
        ExecToken::Cdc => Tree::Cdc,
        ExecToken::Colon => Tree::Colon,
        ExecToken::Semicolon => Tree::Semicolon,
        ExecToken::Comma => Tree::Comma,
        ExecToken::BadString => Tree::BadString,
        ExecToken::BadUrl => Tree::BadUrl,
        ExecToken::UnicodeRange { .. } | ExecToken::Eof => return None,
    })
}

/// The contents of the block `cssparser` just gave.
fn theirs_nested(parser: &mut Parser<'_>) -> Vec<Tree> {
    let result: Result<Vec<Tree>, ParseError<()>> =
        parser.parse_nested_block(|parser| Ok(theirs_list(parser)));
    result.unwrap_or_default()
}

fn theirs_number(value: f32, int_value: Option<i32>, has_sign: bool) -> Numeric {
    Numeric {
        value,
        int_value,
        has_sign,
        has_exponent: false,
    }
}

fn theirs_list(parser: &mut Parser<'_>) -> Vec<Tree> {
    let mut out = Vec::new();
    while let Ok(token) = parser.next_including_whitespace_and_comments() {
        let match_token = |out: &mut Vec<Tree>, first: char| {
            out.push(Tree::Delim(first));
            out.push(Tree::Delim('='));
        };
        match token.clone() {
            Token::Comment(_) => {}
            Token::Ident(v) => out.push(Tree::Ident(v.to_string())),
            Token::AtKeyword(v) => out.push(Tree::AtKeyword(v.to_string())),
            Token::Hash(v) => out.push(Tree::Hash(v.to_string(), false)),
            Token::IDHash(v) => out.push(Tree::Hash(v.to_string(), true)),
            Token::QuotedString(v) => out.push(Tree::QuotedString(v.to_string())),
            Token::UnquotedUrl(v) => out.push(Tree::Url(v.to_string())),
            Token::Delim(c) => out.push(Tree::Delim(c)),
            Token::Number {
                has_sign,
                value,
                int_value,
            } => out.push(Tree::Number(theirs_number(value, int_value, has_sign))),
            Token::Percentage {
                has_sign,
                unit_value,
                int_value,
            } => out.push(Tree::Percentage(theirs_number(
                unit_value, int_value, has_sign,
            ))),
            Token::Dimension {
                has_sign,
                value,
                int_value,
                unit,
            } => out.push(Tree::Dimension(
                theirs_number(value, int_value, has_sign),
                unit.to_string(),
            )),
            Token::WhiteSpace(_) => out.push(Tree::Whitespace),
            Token::Colon => out.push(Tree::Colon),
            Token::Semicolon => out.push(Tree::Semicolon),
            Token::Comma => out.push(Tree::Comma),
            Token::IncludeMatch => match_token(&mut out, '~'),
            Token::DashMatch => match_token(&mut out, '|'),
            Token::PrefixMatch => match_token(&mut out, '^'),
            Token::SuffixMatch => match_token(&mut out, '$'),
            Token::SubstringMatch => match_token(&mut out, '*'),
            Token::CDO => out.push(Tree::Cdo),
            Token::CDC => out.push(Tree::Cdc),
            Token::Function(name) => {
                let inner = theirs_nested(parser);
                out.push(Tree::Function(name.to_string(), inner));
            }
            Token::ParenthesisBlock => {
                let inner = theirs_nested(parser);
                out.push(Tree::Block('(', inner));
            }
            Token::SquareBracketBlock => {
                let inner = theirs_nested(parser);
                out.push(Tree::Block('[', inner));
            }
            Token::CurlyBracketBlock => {
                let inner = theirs_nested(parser);
                out.push(Tree::Block('{', inner));
            }
            Token::BadUrl(_) => out.push(Tree::BadUrl),
            Token::BadString(_) => out.push(Tree::BadString),
            Token::CloseParenthesis => out.push(Tree::Close(')')),
            Token::CloseSquareBracket => out.push(Tree::Close(']')),
            Token::CloseCurlyBracket => out.push(Tree::Close('}')),
        }
    }
    out
}

/// "non-ASCII ident code point", CSS Syntax §4.2 at the commit the specs here are pinned
/// to (`w3c/csswg-drafts` `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`, `css-syntax-3/
/// Overview.bs`): "A code point whose value is any of: U+00B7; between U+00C0 and U+00D6;
/// between U+00D8 and U+00F6; between U+00F8 and U+037D; between U+037F and U+1FFF;
/// U+200C; U+200D; U+203F; U+2040; between U+2070 and U+218F; between U+2C00 and U+2FEF;
/// between U+3001 and U+D7FF; between U+F900 and U+FDCF; between U+FDF0 and U+FFFD;
/// greater than or equal to U+10000. All of these ranges are inclusive." Inclusive
/// `(first, last)` pairs; the last is the largest code point, U+10FFFF.
const NON_ASCII_IDENT: &[(u32, u32)] = &[
    (0xB7, 0xB7),
    (0xC0, 0xD6),
    (0xD8, 0xF6),
    (0xF8, 0x37D),
    (0x37F, 0x1FFF),
    (0x200C, 0x200C),
    (0x200D, 0x200D),
    (0x203F, 0x203F),
    (0x2040, 0x2040),
    (0x2070, 0x218F),
    (0x2C00, 0x2FEF),
    (0x3001, 0xD7FF),
    (0xF900, 0xFDCF),
    (0xFDF0, 0xFFFD),
    (0x1_0000, 0x10_FFFF),
];

/// True if `c` is non-ASCII and the pinned text keeps it out of idents, so that
/// `cssparser` and our tokenizer are known to differ on it.
fn outside_idents(c: u32) -> bool {
    c >= 0x80
        && !NON_ASCII_IDENT
            .iter()
            .any(|(first, last)| (*first..=*last).contains(&c))
}

/// How many tokens [`undo_dash_before_escaped_newline`] rewrote, over the whole corpus.
static DASH_REWRITES: AtomicUsize = AtomicUsize::new(0);

/// `cssparser`'s tokens with its one known difference undone, where, and only where, it
/// shows: a token that starts with a `-` that §4.3.9 does not make start an ident
/// sequence, because the `-` is followed by a backslash and a newline (the module
/// comment has the reason). The backslash is then a delim token and the newline starts a
/// whitespace token, and the token that starts with the `-` is, in `cssparser`'s tokens:
/// - ident `-`, where we have the delim `-`;
/// - at-keyword `-`, where we have the delims `@` and `-`;
/// - id hash `-`, where we have an unrestricted one (§4.3.9 decides the type flag);
/// - dimension with unit `-`, where we have the number and the delim `-`.
fn undo_dash_before_escaped_newline(list: &[Tree]) -> Vec<Tree> {
    let mut out = Vec::new();
    for (at, tree) in list.iter().enumerate() {
        let before_escaped_newline =
            matches!(list.get(at.saturating_add(1)), Some(Tree::Delim('\\')))
                && matches!(list.get(at.saturating_add(2)), Some(Tree::Whitespace));
        let rewritten = |trees: Vec<Tree>, out: &mut Vec<Tree>| {
            DASH_REWRITES.fetch_add(1, Ordering::Relaxed);
            out.extend(trees);
        };
        match tree {
            Tree::Ident(v) if before_escaped_newline && v == "-" => {
                rewritten(vec![Tree::Delim('-')], &mut out);
            }
            Tree::AtKeyword(v) if before_escaped_newline && v == "-" => {
                rewritten(vec![Tree::Delim('@'), Tree::Delim('-')], &mut out);
            }
            Tree::Hash(v, true) if before_escaped_newline && v == "-" => {
                rewritten(vec![Tree::Hash(v.clone(), false)], &mut out);
            }
            Tree::Dimension(n, unit) if before_escaped_newline && unit == "-" => {
                rewritten(vec![Tree::Number(n.clone()), Tree::Delim('-')], &mut out);
            }
            Tree::Function(name, inner) => out.push(Tree::Function(
                name.clone(),
                undo_dash_before_escaped_newline(inner),
            )),
            Tree::Block(kind, inner) => {
                out.push(Tree::Block(*kind, undo_dash_before_escaped_newline(inner)))
            }
            other => out.push(other.clone()),
        }
    }
    out
}

enum Outcome {
    Same,
    /// Differs, and agrees once the one known difference is undone in `cssparser`'s tokens.
    Expected,
    Different(Vec<Tree>, Vec<Tree>),
}

fn compare(sheet: &str) -> Outcome {
    let code_points: Vec<u32> = sheet.chars().map(u32::from).collect();
    let filtered: Vec<u32> = filter(&code_points)
        .into_iter()
        .map(|c| if outside_idents(c) { 1 } else { c })
        .collect();
    let tokens = tokenize_all(&filtered);
    let ours = ours_list(&mut tokens.into_iter().peekable(), None);
    let source = text(&filtered);
    let theirs = theirs_list(&mut Parser::new(&source));
    if same_list(&ours, &theirs) {
        Outcome::Same
    } else if same_list(&ours, &undo_dash_before_escaped_newline(&theirs)) {
        Outcome::Expected
    } else {
        Outcome::Different(ours, theirs)
    }
}

/// What sheets are made of, weighted to the corners of the tokenizer.
const FRAGMENTS: &[&str] = &[
    "url(",
    "URL(",
    "uRl( ",
    "url(  ",
    "u+",
    "U+1",
    "\\",
    "\\\n",
    "\\41 ",
    "\\0",
    "\\110000",
    "\\d800",
    "\"",
    "'",
    "/*",
    "*/",
    "<!--",
    "-->",
    "<!-",
    "--",
    "-",
    "+",
    ".",
    "1",
    "0",
    "1.5",
    ".5",
    "1.",
    "1e3",
    "1E-2",
    "1e+",
    "1e",
    "+.5",
    "-0",
    "+1",
    "%",
    "px",
    "e",
    "E",
    "#",
    "#a",
    "#1",
    "#-",
    "@",
    "@media",
    "@-",
    "@1",
    "(",
    ")",
    "[",
    "]",
    "{",
    "}",
    ",",
    ":",
    ";",
    " ",
    "  ",
    "\t",
    "\n",
    "a",
    "b",
    "_",
    "é",
    "\u{80}",
    "\u{A0}",
    "\u{2028}",
    "\u{10000}",
    "\u{FFFD}",
    "~=",
    "|=",
    "^=",
    "$=",
    "*=",
    "||",
    "!important",
    "\u{1}",
    "\u{7F}",
    "\0",
    "\r\n",
    "\r",
    "\u{C}",
    "99999999999999999999",
    "1e400",
    "1e-400",
    "2147483648",
    "-2147483649",
];

/// A small generator, so a failure repeats.
struct Random(u64);

impl Random {
    fn next(&mut self, below: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        let limit = u64::try_from(below).unwrap_or(1);
        usize::try_from(self.0.checked_rem(limit).unwrap_or(0)).unwrap_or(0)
    }

    fn fragment(&mut self) -> &'static str {
        FRAGMENTS
            .get(self.next(FRAGMENTS.len()))
            .copied()
            .unwrap_or("")
    }
}

fn random_sheet(random: &mut Random) -> String {
    let length = random.next(24);
    (0..length).map(|_| random.fragment()).collect()
}

/// `sheet` with a few fragments put in and a few characters taken out.
fn mutated(sheet: &str, random: &mut Random) -> String {
    let mut chars: Vec<char> = sheet.chars().collect();
    for _ in 0..=random.next(4) {
        let at = random.next(chars.len().saturating_add(1));
        if random.next(2) == 0 {
            let tail = chars.split_off(at.min(chars.len()));
            chars.extend(random.fragment().chars());
            chars.extend(tail);
        } else if at < chars.len() {
            chars.remove(at);
        }
    }
    chars.into_iter().collect()
}

/// Every string input in the suite's table.
fn vendored() -> Vec<&'static str> {
    syntax::cases()
        .iter()
        .filter_map(|case| match case.input {
            syntax::Json::Str(s) => Some(s),
            _ => None,
        })
        .collect()
}

#[test]
#[cfg_attr(miri, ignore)]
fn differential_tokens() {
    let sheets = vendored();
    let (mut pass, mut xfail, mut fail, mut total) = (0usize, 0usize, 0usize, 0usize);
    let mut random = Random(0x9E37_79B9_7F4A_7C15);
    // Whether the sheet differed in a way nothing explains.
    let mut check = |sheet: &str| {
        total = total.saturating_add(1);
        match compare(sheet) {
            Outcome::Same => pass = pass.saturating_add(1),
            Outcome::Expected => xfail = xfail.saturating_add(1),
            Outcome::Different(ours, theirs) => {
                fail = fail.saturating_add(1);
                if fail <= 12 {
                    println!("DIFFERENT {sheet:?}\n  ours   {ours:?}\n  theirs {theirs:?}");
                }
                return true;
            }
        }
        false
    };
    for case in syntax::cases() {
        if let syntax::Json::Str(sheet) = case.input
            && check(sheet)
        {
            println!(
                "  from {} {}, which expects {:?}",
                case.file, case.index, case.expected
            );
        }
    }
    for _ in 0..20 {
        for sheet in &sheets {
            let changed = mutated(sheet, &mut random);
            check(&changed);
        }
    }
    for _ in 0..200_000 {
        let sheet = random_sheet(&mut random);
        check(&sheet);
    }
    println!(
        "clazel-conformance: suite=\"cssparser token differential\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
    let seen = Pinned {
        pass,
        xfail,
        total,
        dash_rewrites: DASH_REWRITES.load(Ordering::Relaxed),
        nan_for_zero: NAN_FOR_ZERO.load(Ordering::Relaxed),
        max_ulps: MAX_SEEN_ULPS.load(Ordering::Relaxed),
    };
    println!("pinned: {seen:?}");
    assert_eq!(fail, 0);
    assert_eq!(
        seen, PINNED,
        "the corpus outcome moved; see the module comment"
    );
}

/// What the fixed corpus gives. Both engines, the generator and the lists are fixed, so
/// every number is exact: a sheet that starts to differ, one that stops, or a number
/// that starts to differ by more bits all move one of them. To update after a deliberate
/// change, follow the module comment.
#[derive(Debug, PartialEq, Eq)]
struct Pinned {
    /// Sheets on which the engines agree.
    pass: usize,
    /// Sheets that agree once the dash-before-escaped-newline difference is undone.
    xfail: usize,
    /// Sheets in all.
    total: usize,
    /// Tokens rewritten by [`undo_dash_before_escaped_newline`].
    dash_rewrites: usize,
    /// Numbers `cssparser` gave as NaN where we give 0.
    nan_for_zero: usize,
    /// The largest distance, in `f32` units in the last place, between two accepted
    /// numbers. The comparison needs 0, so this stays 0.
    max_ulps: u32,
}

const PINNED: Pinned = Pinned {
    pass: 204_965,
    xfail: 768,
    total: 205_733,
    dash_rewrites: 770,
    nan_for_zero: 10,
    max_ulps: 0,
};

/// §4.3.6 on `url(a \)b)`: after "a" the whitespace is consumed and the next code point,
/// `\`, is not `)` or EOF, so "consume the remnants of a bad url" runs from it, and in the
/// remnants a valid escape (`\)`) is consumed whole. The bad-url token therefore ends at
/// the second `)`, and nothing follows. `cssparser`'s `consume_url_end` has consumed
/// the byte after the whitespace, so it ends the token at the first `)` and goes on
/// from `b`. (Where nothing follows the remnants, or the backslash is first, as in
/// `url( \)b)`, which is a url token with value `)b` in both engines, they agree.)
#[test]
#[cfg_attr(miri, ignore)]
fn known_difference_url_whitespace_backslash() {
    use Tree::{BadUrl, Close, Ident, Url};
    let cases: Vec<(&str, Vec<Tree>, Vec<Tree>)> = vec![
        // ours by §4.3.6; theirs as `cssparser` 0.38.0 gives.
        (
            "url(a \\)b)",
            vec![BadUrl],
            vec![BadUrl, Ident("b".into()), Close(')')],
        ),
        (
            "url(a\t\\)b)x",
            vec![BadUrl, Ident("x".into())],
            vec![BadUrl, Ident("b".into()), Close(')'), Ident("x".into())],
        ),
        // No difference where the remnants end at the first `)` anyway.
        ("url(a \\)", vec![BadUrl], vec![BadUrl]),
        ("url(a \\\n)", vec![BadUrl], vec![BadUrl]),
        // A backslash right after the opening parenthesis and whitespace is an escape.
        ("url( \\)b)", vec![Url(")b".into())], vec![Url(")b".into())]),
    ];
    for (source, want_ours, want_theirs) in cases {
        let code_points: Vec<u32> = source.chars().map(u32::from).collect();
        let ours = ours_list(&mut tokenize_all(&code_points).into_iter().peekable(), None);
        let theirs = theirs_list(&mut Parser::new(source));
        assert!(same_list(&ours, &want_ours), "{source:?}: ours {ours:?}");
        assert!(
            same_list(&theirs, &want_theirs),
            "{source:?}: theirs {theirs:?}"
        );
    }
}
