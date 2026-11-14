//! The tokenizer and the rule structure against Servo's `cssparser` (phase-5.md item
//! 5.4), on random and mutated sheets and every `css-parsing-tests` input. The first test
//! compares tokens; the second compares rules, at-rules and declarations (see "Rule
//! structure" below).
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
//! The rule structure is compared by running `cssparser`'s rule parsers (`StyleSheetParser`
//! and `RuleBodyParser`, which implement §5.5's algorithms for nested blocks) and ours on
//! one sheet and comparing at-rule names, preludes and blocks, qualified rules' preludes and
//! blocks, and declarations' names, values and important flags, all down to the tokens.
//! `cssparser` leaves what a declaration or rule is "valid" for to its user, so `Theirs`
//! below accepts every rule and decides one thing, as §5.5.6 step 8 does for a generic
//! processor: a declaration of a name that is not a custom property name is none if its
//! value has a top-level {}-block and another non-whitespace value (it is then read as a
//! rule). Without that, 1,444 of the 51,638 sheets differ; with it, one class remains:
//! - `cssparser` drops the first rule of a stylesheet if it is an `@charset` at-rule,
//!   from an older draft (the pinned text, with `charset-is-not-a-rule.html`, has it as an
//!   ordinary at-rule). That is excused only where ours has such a rule first and
//!   `cssparser` has exactly the rest, and counted. The random sheets never make one;
//!   `css-parsing-tests` does.
//!
//! Compared the same way as the tokens, with no other difference allowed and the outcome
//! and the coverage of the sheets that agree (rules, nesting, declarations, `!important`,
//! custom properties) pinned.
//!
//! Skipped under Miri (`#[cfg_attr(miri, ignore)]`, as `clazel-cookie`'s differential
//! is): `cssparser` has `unsafe` of its own, and our tokenizer has none and runs there
//! in `tests/conformance_tokens.rs`.

use clazel_css::parser::exec_parse::{ExecParsed, parse_stylesheet_contents};
use clazel_css::parser::rows::{ExecDeclaration, ExecItemKind};
use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, filter, next_token, tokenize_all};
use cssparser::{
    AtRuleParser, CowRcStr, DeclarationParser, ParseError, Parser, ParserState,
    QualifiedRuleParser, RuleBodyItemParser, RuleBodyParser, StyleSheetParser, Token,
    parse_important,
};
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
        let token = token.clone();
        theirs_push(parser, token, &mut out);
    }
    out
}

/// What `token` is in terms both engines share, onto `out`; a block's or function's
/// contents are read from `parser`.
fn theirs_push(parser: &mut Parser<'_>, token: Token<'_>, out: &mut Vec<Tree>) {
    let match_token = |out: &mut Vec<Tree>, first: char| {
        out.push(Tree::Delim(first));
        out.push(Tree::Delim('='));
    };
    match token {
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
        Token::IncludeMatch => match_token(out, '~'),
        Token::DashMatch => match_token(out, '|'),
        Token::PrefixMatch => match_token(out, '^'),
        Token::SuffixMatch => match_token(out, '$'),
        Token::SubstringMatch => match_token(out, '*'),
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

// ------------------------------------------------------------------------------------
// Rule structure
// ------------------------------------------------------------------------------------

/// A rule or declaration in terms both engines share. A block's contents are the items
/// of "consume a block's contents" in order: `cssparser` hands them out one at a time, so
/// our lists of declarations are flattened to match.
#[derive(Debug, Clone)]
enum Node {
    At {
        name: String,
        prelude: Vec<Tree>,
        block: Option<Vec<Node>>,
    },
    Qualified {
        prelude: Vec<Tree>,
        block: Vec<Node>,
    },
    Decl {
        name: String,
        value: Vec<Tree>,
        important: bool,
    },
}

fn same_nodes(a: &[Node], b: &[Node]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| same_node(a, b))
}

fn same_node(a: &Node, b: &Node) -> bool {
    match (a, b) {
        (
            Node::At {
                name: n1,
                prelude: p1,
                block: b1,
            },
            Node::At {
                name: n2,
                prelude: p2,
                block: b2,
            },
        ) => {
            n1 == n2
                && same_list(p1, p2)
                && match (b1, b2) {
                    (Some(b1), Some(b2)) => same_nodes(b1, b2),
                    (None, None) => true,
                    _ => false,
                }
        }
        (
            Node::Qualified {
                prelude: p1,
                block: b1,
            },
            Node::Qualified {
                prelude: p2,
                block: b2,
            },
        ) => same_list(p1, p2) && same_nodes(b1, b2),
        (
            Node::Decl {
                name: n1,
                value: v1,
                important: i1,
            },
            Node::Decl {
                name: n2,
                value: v2,
                important: i2,
            },
        ) => n1 == n2 && same_list(v1, v2) && i1 == i2,
        _ => false,
    }
}

/// Our rows and items as [`Node`]s.
struct OursRules<'a> {
    parsed: &'a ExecParsed,
}

impl OursRules<'_> {
    fn trees(&self, lo: usize, hi: usize) -> Vec<Tree> {
        let rows = &self.parsed.output.rows;
        let mut out = Vec::new();
        let mut k = hi;
        while k > lo {
            let last = k.saturating_sub(1);
            out.push(self.tree(last));
            k = rows
                .get(last)
                .map_or(lo, |row| row.start as usize)
                .min(last);
        }
        out.reverse();
        out
    }

    fn tree(&self, k: usize) -> Tree {
        let Some(row) = self.parsed.output.rows.get(k) else {
            return Tree::BadString;
        };
        let start = row.start as usize;
        let token = next_token(&self.parsed.text, row.pos as usize, false).0;
        match token {
            ExecToken::Function { value } => Tree::Function(text(&value), self.trees(start, k)),
            ExecToken::OpenParen => Tree::Block('(', self.trees(start, k)),
            ExecToken::OpenSquare => Tree::Block('[', self.trees(start, k)),
            ExecToken::OpenCurly => Tree::Block('{', self.trees(start, k)),
            other => {
                ours_tree(other, &mut Vec::new().into_iter().peekable()).unwrap_or(Tree::BadString)
            }
        }
    }

    fn declaration(&self, d: &ExecDeclaration) -> Node {
        let name = match next_token(&self.parsed.text, d.name_pos as usize, false).0 {
            ExecToken::Ident { value } => text(&value),
            _ => String::new(),
        };
        Node::Decl {
            name,
            value: self.trees(d.value_lo as usize, d.value_hi as usize),
            important: d.important,
        }
    }

    /// The items `lo` up to `hi`, flattened.
    fn nodes(&self, lo: usize, hi: usize) -> Vec<Node> {
        let items = &self.parsed.output.items;
        let mut groups: Vec<Vec<Node>> = Vec::new();
        let mut k = hi;
        while k > lo {
            let last = k.saturating_sub(1);
            groups.push(self.item(last));
            k = items
                .get(last)
                .map_or(lo, |item| item.start as usize)
                .min(last);
        }
        groups.into_iter().rev().flatten().collect()
    }

    fn item(&self, k: usize) -> Vec<Node> {
        let Some(item) = self.parsed.output.items.get(k) else {
            return Vec::new();
        };
        let prelude = || self.trees(item.lo as usize, item.hi as usize);
        let name = || match next_token(&self.parsed.text, item.pos as usize, false).0 {
            ExecToken::AtKeyword { value } => text(&value),
            _ => String::new(),
        };
        let block = || self.nodes(item.start as usize, k);
        match item.kind {
            ExecItemKind::StatementAtRule => vec![Node::At {
                name: name(),
                prelude: prelude(),
                block: None,
            }],
            ExecItemKind::BlockAtRule => vec![Node::At {
                name: name(),
                prelude: prelude(),
                block: Some(block()),
            }],
            ExecItemKind::QualifiedRule => vec![Node::Qualified {
                prelude: prelude(),
                block: block(),
            }],
            ExecItemKind::Declarations => (item.lo as usize..item.hi as usize)
                .filter_map(|i| self.parsed.output.declarations.get(i))
                .map(|d| self.declaration(d))
                .collect(),
        }
    }
}

fn ours_rules(sheet: &str) -> Vec<Node> {
    let parsed = parse_stylesheet_contents(&sheet.chars().map(u32::from).collect::<Vec<_>>());
    OursRules { parsed: &parsed }.nodes(0, parsed.output.items.len())
}

/// `cssparser`'s three parser traits, building [`Node`]s. The decisions the crate leaves to
/// its user are made as §5.5.6 step 8 makes them for a generic processor: every rule is
/// accepted, and a declaration of a name that is not a custom property name is not one
/// if its value has a top-level {}-block and anything else but whitespace.
struct Theirs;

impl<'i> DeclarationParser<'i> for Theirs {
    type Declaration = Node;
    type Error = ();

    fn parse_value(
        &mut self,
        name: CowRcStr<'i>,
        input: &mut Parser<'i>,
        _start: &ParserState,
    ) -> Result<Node, ParseError<()>> {
        input.skip_whitespace();
        let mut value = Vec::new();
        let mut important = false;
        loop {
            // `cssparser`'s own `!important`: the last two tokens, whitespace between them
            // allowed (`parse_important` skips it), and nothing after.
            let at_the_end = input.try_parse(|i| {
                parse_important(i)?;
                i.expect_exhausted()
            });
            if at_the_end.is_ok() {
                important = true;
                break;
            }
            let Ok(token) = input.next_including_whitespace_and_comments() else {
                break;
            };
            let token = token.clone();
            theirs_push(input, token, &mut value);
        }
        while matches!(value.last(), Some(Tree::Whitespace)) {
            value.pop();
        }
        let blocks = value
            .iter()
            .filter(|t| matches!(t, Tree::Block('{', _)))
            .count();
        let others = value
            .iter()
            .filter(|t| !matches!(t, Tree::Whitespace | Tree::Block('{', _)))
            .count();
        if !name.starts_with("--") && blocks > 0 && (blocks > 1 || others > 0) {
            return Err(ParseError::custom(()));
        }
        Ok(Node::Decl {
            name: name.to_string(),
            value,
            important,
        })
    }
}

impl<'i> AtRuleParser<'i> for Theirs {
    type Prelude = (String, Vec<Tree>);
    type AtRule = Node;
    type Error = ();

    fn parse_prelude(
        &mut self,
        name: CowRcStr<'i>,
        input: &mut Parser<'i>,
    ) -> Result<Self::Prelude, ParseError<()>> {
        Ok((name.to_string(), theirs_list(input)))
    }

    fn rule_without_block(
        &mut self,
        prelude: Self::Prelude,
        _start: &ParserState,
    ) -> Result<Node, ()> {
        Ok(Node::At {
            name: prelude.0,
            prelude: prelude.1,
            block: None,
        })
    }

    fn parse_block(
        &mut self,
        prelude: Self::Prelude,
        _start: &ParserState,
        input: &mut Parser<'i>,
    ) -> Result<Node, ParseError<()>> {
        Ok(Node::At {
            name: prelude.0,
            prelude: prelude.1,
            block: Some(theirs_block(self, input)),
        })
    }
}

impl<'i> QualifiedRuleParser<'i> for Theirs {
    type Prelude = Vec<Tree>;
    type QualifiedRule = Node;
    type Error = ();

    fn parse_prelude(&mut self, input: &mut Parser<'i>) -> Result<Self::Prelude, ParseError<()>> {
        Ok(theirs_list(input))
    }

    fn parse_block(
        &mut self,
        prelude: Self::Prelude,
        _start: &ParserState,
        input: &mut Parser<'i>,
    ) -> Result<Node, ParseError<()>> {
        Ok(Node::Qualified {
            prelude,
            block: theirs_block(self, input),
        })
    }
}

impl<'i> RuleBodyItemParser<'i, Node, ()> for Theirs {
    fn parse_declarations(&self) -> bool {
        true
    }
    fn parse_qualified(&self) -> bool {
        true
    }
}

/// The items of the block `input` is inside: "consume a block's contents".
fn theirs_block<'i>(parser: &mut Theirs, input: &mut Parser<'i>) -> Vec<Node> {
    RuleBodyParser::new(input, parser)
        .filter_map(Result::ok)
        .collect()
}

fn theirs_rules(source: &str) -> Vec<Node> {
    let mut parser = Parser::new(source);
    let mut builder = Theirs;
    StyleSheetParser::new(&mut parser, &mut builder)
        .filter_map(Result::ok)
        .collect()
}

/// What rule sheets are made of: the pieces of rules, declarations and blocks, with
/// the stray ones a block's error recovery has to deal with.
const RULE_FRAGMENTS: &[&str] = &[
    "a",
    "b",
    "x",
    ".a",
    "#i",
    "&",
    "--c",
    "-x",
    "color",
    "hover",
    "1",
    "1px",
    "\"s\"",
    "url(u)",
    "f(",
    ")",
    "(",
    "[",
    "]",
    "{",
    "}",
    "{}",
    ";",
    ":",
    ",",
    "!",
    "!important",
    "! important",
    "!IMPORTANT",
    "@x",
    "@media",
    "@x y;",
    "@x {}",
    " ",
    " ",
    " ",
    "\n",
    "/* c */",
    "<!--",
    "-->",
    "a:b;",
    "a:b;",
    "a:b",
    "a:b !important;",
    "--c:d !important;",
    "a{b:c;d{e:f}}",
    "@x{a:b;c:d}",
    "--c:d;",
    "--c:{};",
    "a{",
    "a{}",
    "a:b{}",
    "a:{}",
];

fn random_rule_sheet(random: &mut Random) -> String {
    let length = random.next(24);
    (0..length)
        .map(|_| {
            RULE_FRAGMENTS
                .get(random.next(RULE_FRAGMENTS.len()))
                .copied()
                .unwrap_or("")
        })
        .collect()
}

/// What the sheets that agree contain, so that agreeing is not agreeing on nothing.
#[derive(Debug, Default, PartialEq, Eq)]
struct Coverage {
    /// Qualified rules and at-rules, at any depth.
    rules: usize,
    /// Of those, the ones inside a block.
    nested_rules: usize,
    /// Declarations, at any depth.
    declarations: usize,
    /// Declarations with the important flag.
    important: usize,
    /// Declarations of a custom property.
    custom: usize,
    /// Rules whose block holds a rule and a declaration both.
    mixed_blocks: usize,
    /// The deepest nesting of blocks.
    max_depth: usize,
}

fn cover(nodes: &[Node], depth: usize, coverage: &mut Coverage) {
    coverage.max_depth = coverage.max_depth.max(depth);
    let has = |f: fn(&Node) -> bool| nodes.iter().any(f);
    if has(|n| matches!(n, Node::Decl { .. })) && has(|n| !matches!(n, Node::Decl { .. })) {
        coverage.mixed_blocks = coverage.mixed_blocks.saturating_add(1);
    }
    for node in nodes {
        let inside = match node {
            Node::Decl {
                name, important, ..
            } => {
                coverage.declarations = coverage.declarations.saturating_add(1);
                if *important {
                    coverage.important = coverage.important.saturating_add(1);
                }
                if name.starts_with("--") {
                    coverage.custom = coverage.custom.saturating_add(1);
                }
                continue;
            }
            Node::At { block, .. } => block.as_deref().unwrap_or_default(),
            Node::Qualified { block, .. } => block.as_slice(),
        };
        coverage.rules = coverage.rules.saturating_add(1);
        if depth > 0 {
            coverage.nested_rules = coverage.nested_rules.saturating_add(1);
        }
        cover(inside, depth.saturating_add(1), coverage);
    }
}

enum RulesOutcome {
    Same,
    /// Differs only in that `cssparser` leaves out a first `@charset` rule.
    Charset,
    Different(Vec<Node>, Vec<Node>),
}

/// `StyleSheetParser` drops the first rule if it is an at-rule named `charset`
/// (ASCII case-insensitive), whatever it holds, as §8.3 of the older CSS Syntax has it for
/// the byte stream; the pinned text has no such step (`charset-is-not-a-rule.html`: it is
/// an ordinary at-rule), and `tests/conformance_syntax.rs` drops it from our rules in the
/// same way for the suite's expectations. Excused only where ours has such a rule first and
/// `cssparser` has exactly the rest.
fn compare_rules(sheet: &str, coverage: &mut Coverage) -> RulesOutcome {
    let code_points: Vec<u32> = sheet.chars().map(u32::from).collect();
    let filtered: Vec<u32> = filter(&code_points)
        .into_iter()
        .map(|c| if outside_idents(c) { 1 } else { c })
        .collect();
    let source = text(&filtered);
    let ours = ours_rules(&source);
    let theirs = theirs_rules(&source);
    if same_nodes(&ours, &theirs) {
        cover(&ours, 0, coverage);
        return RulesOutcome::Same;
    }
    if let Some((Node::At { name, .. }, rest)) = ours.split_first()
        && name.eq_ignore_ascii_case("charset")
        && same_nodes(rest, &theirs)
    {
        return RulesOutcome::Charset;
    }
    RulesOutcome::Different(ours, theirs)
}

/// What the fixed rule corpus gives, as (agree, `@charset` only, different, sheets): see
/// the module comment for how to update it.
const PINNED_RULES: (usize, usize, usize, usize) = (51_635, 3, 0, 51_638);
const PINNED_COVERAGE: Coverage = Coverage {
    rules: 83_507,
    nested_rules: 20_907,
    declarations: 34_140,
    important: 1_591,
    custom: 2_076,
    mixed_blocks: 9_840,
    max_depth: 6,
};

#[test]
#[cfg_attr(miri, ignore)]
fn differential_rules() {
    let sheets = vendored();
    let (mut pass, mut charset, mut fail, mut total) = (0usize, 0usize, 0usize, 0usize);
    let mut coverage = Coverage::default();
    let mut random = Random(0xD1B5_4A32_D192_ED03);
    let mut check = |sheet: &str| {
        total = total.saturating_add(1);
        match compare_rules(sheet, &mut coverage) {
            RulesOutcome::Same => pass = pass.saturating_add(1),
            RulesOutcome::Charset => charset = charset.saturating_add(1),
            RulesOutcome::Different(ours, theirs) => {
                fail = fail.saturating_add(1);
                if fail <= 25 {
                    println!("DIFFERENT {sheet:?}\n  ours   {ours:?}\n  theirs {theirs:?}");
                }
            }
        }
    };
    for sheet in &sheets {
        check(sheet);
    }
    for _ in 0..5 {
        for sheet in &sheets {
            let changed = mutated(sheet, &mut random);
            check(&changed);
        }
    }
    for _ in 0..50_000 {
        let sheet = random_rule_sheet(&mut random);
        check(&sheet);
    }
    println!(
        "clazel-conformance: suite=\"cssparser rule differential\" pass={pass} xfail={charset} fail={fail} total={total}"
    );
    println!("pinned: {:?} {coverage:?}", (pass, charset, fail, total));
    assert_eq!(fail, 0);
    assert_eq!((pass, charset, fail, total), PINNED_RULES);
    assert_eq!(coverage, PINNED_COVERAGE);
}
