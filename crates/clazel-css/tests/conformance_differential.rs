//! The tokenizer against Servo's `cssparser` (phase-5.md item 5.4), on random and mutated
//! sheets and every `css-parsing-tests` input. Tokens are compared here; rule structure is
//! not compared yet.
//!
//! `cssparser` hands out blocks and functions nested, so our tokens are nested the same
//! way first, as `tests/conformance_tokens.rs` does. Both engines read the same text,
//! after our "filter code points", so a difference is in tokenizing and not in
//! preprocessing.
//!
//! Five known differences, each decided by the pinned text:
//! - `cssparser` has match tokens such as `~=`, from an older draft. They are read here
//!   as their two delim tokens, which is what the pinned text gives.
//! - It takes every non-ASCII code point into an ident, also from an older draft, where
//!   the pinned text lists ranges. Those outside the ranges become U+0001 for both
//!   engines, so the rest of such a sheet is still compared. That they are not ident
//!   code points is tested by the spec's examples and `tests/conformance_tokens.rs`.
//! - It takes `-` before a backslash and a newline as starting an ident, in
//!   `is_ident_start`: it looks for the newline at offset 1, which is the backslash, and
//!   not at offset 2. §4.3.9 needs "the second and third code points" to be a valid
//!   escape, and §4.3.8 says these are not. A difference on a sheet with that sequence
//!   counts as expected.
//! - It gives NaN for zero with a huge exponent, such as `0e99999999999999999999`: it
//!   works out 0 times infinity in floats. §4.3.12 step 6 multiplies by 10 to the power,
//!   which is exactly 0, so NaN is read here as 0.
//! - After whitespace in an unquoted url, its `consume_url_end` consumes the next byte
//!   before it looks for the remnants, so a backslash there is lost and `url(a \)b)` ends
//!   at the first `)`. §4.3.6 consumes the remnants from that code point, where `\)` is a
//!   valid escape. A difference on a sheet with a url and whitespace before a backslash
//!   counts as expected.
//!
//! No other difference is allowed.
//!
//! Skipped under Miri (`#[cfg_attr(miri, ignore)]`, as `clazel-cookie`'s differential
//! is): `cssparser` has `unsafe` of its own, and our tokenizer has none and runs there
//! in `tests/conformance_tokens.rs`.

use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, filter, tokenize_all};
use cssparser::{ParseError, Parser, Token};
use std::iter::Peekable;
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
    is_integer: bool,
    has_sign: bool,
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

fn close_enough(a: f32, b: f32) -> bool {
    let clamp = |v: f32| v.clamp(-f32::MAX, f32::MAX);
    let (a, b) = (clamp(a), clamp(b));
    (a - b).abs() <= a.abs().max(b.abs()) * 1e-5 || (a.abs() < 1e-30 && b.abs() < 1e-30)
}

fn same_number(a: &Numeric, b: &Numeric) -> bool {
    close_enough(a.value, b.value) && a.is_integer == b.is_integer && a.has_sign == b.has_sign
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

fn ours_number(number: &ExecNumber) -> Numeric {
    let mut source = text(&number.number_part);
    if !number.exponent_part.is_empty() {
        source.push('e');
        source.push_str(&text(&number.exponent_part));
    }
    Numeric {
        value: source.parse::<f64>().unwrap_or(f64::NAN) as f32,
        is_integer: number.is_integer,
        has_sign: number.sign_character.is_some(),
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
        ExecToken::Number { number } => Tree::Number(ours_number(&number)),
        ExecToken::Percentage { number } => Tree::Percentage(ours_number(&number)),
        ExecToken::Dimension { number, unit } => Tree::Dimension(ours_number(&number), text(&unit)),
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
        value: if value.is_nan() { 0.0 } else { value },
        is_integer: int_value.is_some(),
        has_sign,
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
                unit_value * 100.0,
                int_value,
                has_sign,
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

/// True if `c` is non-ASCII and the pinned text keeps it out of idents, so that
/// `cssparser` and our tokenizer are known to differ on it.
fn outside_idents(c: u32) -> bool {
    c >= 0x80 && !matches!(tokenize_all(&[c]).first(), Some(ExecToken::Ident { .. }))
}

/// True if `source` has one of the sequences the module comment says `cssparser` reads
/// differently.
fn has_known_difference(source: &str) -> bool {
    let url = source.to_ascii_lowercase().contains("url(");
    source.contains("-\\\n") || (url && [" \\", "\t\\", "\n\\"].iter().any(|s| source.contains(s)))
}

enum Outcome {
    Same,
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
    } else if has_known_difference(&source) {
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
    assert_eq!(fail, 0);
}
