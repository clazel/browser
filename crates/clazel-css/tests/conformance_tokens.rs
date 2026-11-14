//! The tokenizer against the outside world (phase-5.md items 5.2 and 5.4).
//!
//! The proofs show the tokenizer equals `spec.rs`. This file checks both against suites
//! neither was written from:
//!
//! 1. `css-parsing-tests`' `component_value_list.json` and `one_component_value.json`.
//!    Their results are component values, so `values` below nests the tokens into
//!    blocks and functions. That is the parser's job (item 5.3), done here in the
//!    simplest way, only so that these cases can check the tokens inside them.
//! 2. WPT's `input-preprocessing.html`: each input is one identifier once filtered.
//!
//! The rest of both suites needs the parser, and is run by item 5.4.

use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, filter, tokenize_all};
use std::iter::Peekable;
use std::vec::IntoIter;
use syntax::Json;

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

/// The WPT table.
mod wpt {
    /// One helper call of a WPT page.
    pub struct Case {
        pub file: &'static str,
        pub line: usize,
        pub helper: &'static str,
        pub input: &'static [u16],
        pub expected: Option<&'static [u16]>,
    }

    include!("generated/wpt_css_syntax.rs");

    /// The table.
    pub fn cases() -> &'static [Case] {
        WPT
    }

    /// What could not be read.
    pub fn not_run() -> &'static [(&'static str, &'static str)] {
        NOT_RUN
    }
}

/// A result in the suite's shape.
#[derive(Debug, Clone, PartialEq)]
enum Value {
    /// Matches any string: a field that is not compared.
    AnyText,
    Text(String),
    Number(f64),
    List(Vec<Value>),
}

fn text(s: &str) -> Value {
    Value::Text(s.to_owned())
}

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn tagged(tag: &str, value: &[u32]) -> Value {
    Value::List(vec![text(tag), Value::Text(string(value))])
}

fn error(kind: &str) -> Value {
    Value::List(vec![text("error"), text(kind)])
}

/// The number as the suite writes it: representation, value and type. The suite's
/// representation is not the source text (`12e2` is "1200.0" and `.1` is "0.1"), so it is
/// not compared. The value and type are.
fn number_fields(number: &ExecNumber) -> Vec<Value> {
    let mut source = string(&number.number_part);
    if !number.exponent_part.is_empty() {
        source.push('e');
        source.push_str(&string(&number.exponent_part));
    }
    let value = source.parse::<f64>().unwrap_or(f64::NAN);
    let kind = if number.is_integer {
        "integer"
    } else {
        "number"
    };
    vec![Value::AnyText, Value::Number(value), text(kind)]
}

/// A block or function's contents, up to `closer` or the end.
fn values(tokens: &mut Peekable<IntoIter<ExecToken>>, closer: Option<&ExecToken>) -> Vec<Value> {
    let mut out = Vec::new();
    while let Some(token) = tokens.next() {
        if closer == Some(&token) {
            return out;
        }
        out.extend(value(token, tokens));
    }
    out
}

/// One token, and whatever it opens, as the suite writes it. EOF is nothing.
fn value(token: ExecToken, tokens: &mut Peekable<IntoIter<ExecToken>>) -> Option<Value> {
    let block = |tag: &str, inner: Vec<Value>| {
        let mut list = vec![text(tag)];
        list.extend(inner);
        Value::List(list)
    };
    Some(match token {
        ExecToken::Ident { value } => tagged("ident", &value),
        ExecToken::AtKeyword { value } => tagged("at-keyword", &value),
        ExecToken::String { value } => tagged("string", &value),
        ExecToken::Url { value } => tagged("url", &value),
        ExecToken::Hash { value, is_id } => Value::List(vec![
            text("hash"),
            Value::Text(string(&value)),
            text(if is_id { "id" } else { "unrestricted" }),
        ]),
        ExecToken::Function { value } => {
            let mut list = vec![text("function"), Value::Text(string(&value))];
            list.extend(values(tokens, Some(&ExecToken::CloseParen)));
            Value::List(list)
        }
        ExecToken::OpenParen => block("()", values(tokens, Some(&ExecToken::CloseParen))),
        ExecToken::OpenSquare => block("[]", values(tokens, Some(&ExecToken::CloseSquare))),
        ExecToken::OpenCurly => block("{}", values(tokens, Some(&ExecToken::CloseCurly))),
        ExecToken::Number { number } => block("number", number_fields(&number)),
        ExecToken::Percentage { number } => block("percentage", number_fields(&number)),
        ExecToken::Dimension { number, unit } => {
            let mut fields = number_fields(&number);
            fields.push(Value::Text(string(&unit)));
            block("dimension", fields)
        }
        ExecToken::Delim { value } => Value::Text(string(&[value])),
        ExecToken::Whitespace => text(" "),
        ExecToken::Cdo => text("<!--"),
        ExecToken::Cdc => text("-->"),
        ExecToken::Colon => text(":"),
        ExecToken::Semicolon => text(";"),
        ExecToken::Comma => text(","),
        ExecToken::BadString => error("bad-string"),
        ExecToken::BadUrl => error("bad-url"),
        ExecToken::CloseParen => error(")"),
        ExecToken::CloseSquare => error("]"),
        ExecToken::CloseCurly => error("}"),
        ExecToken::UnicodeRange { .. } | ExecToken::Eof => return None,
    })
}

fn component_values(input: &str) -> Vec<Value> {
    let code_points: Vec<u32> = input.chars().map(u32::from).collect();
    let tokens = tokenize_all(&filter(&code_points));
    values(&mut tokens.into_iter().peekable(), None)
}

/// "Parse a component value": one value with whitespace around it.
fn one_component_value(input: &str) -> Value {
    let mut list = component_values(input);
    list.retain(|v| *v != text(" "));
    match list.as_slice() {
        [] => error("empty"),
        [one] => one.clone(),
        _ => error("extra-input"),
    }
}

/// Whether a result is what the suite expects. Numbers compare to within rounding.
fn same(actual: &Value, expected: &Json) -> bool {
    match (actual, expected) {
        (Value::AnyText, Json::Str(_)) => true,
        (Value::Text(a), Json::Str(e)) => a == e,
        (Value::Number(a), Json::Num(e)) => e.parse::<f64>().is_ok_and(|e| {
            let scale = e.abs().max(1.0);
            (a - e).abs() <= scale * 1e-9
        }),
        (Value::List(a), Json::List(e)) => {
            a.len() == e.len() && a.iter().zip(e.iter()).all(|(a, e)| same(a, e))
        }
        // No component value is written as these.
        (_, Json::Null | Json::Bool(_) | Json::Obj(_))
        | (_, Json::Str(_) | Json::Num(_) | Json::List(_)) => false,
    }
}

/// A list of values against a suite's list.
fn same_list(actual: &[Value], expected: &Json) -> bool {
    matches!(expected, Json::List(e) if actual.len() == e.len()
        && actual.iter().zip(e.iter()).all(|(a, e)| same(a, e)))
}

/// Cases that differ from the pinned text, as (file, index, why). `css-parsing-tests`
/// was written for an older draft.
const EXPECTED_FAILURES: &[(&str, usize, &str)] = &[
    (
        "component_value_list.json",
        6,
        "U+0080 and U+0081 are not non-ASCII ident code points in the pinned text, which \
         lists ranges from U+00B7; the suite's draft took every non-ASCII code point",
    ),
    (
        "component_value_list.json",
        38,
        "the pinned text has no match tokens, so \"~=\" is two delim tokens",
    ),
    (
        "component_value_list.json",
        39,
        "the pinned text has no match tokens, so \"^=\" is two delim tokens",
    ),
];

fn report(suite: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
}

fn run(file: &str, suite: &str, check: impl Fn(&str, &Json) -> bool) {
    let (mut pass, mut xfail, mut fail, mut total) = (0usize, 0usize, 0usize, 0usize);
    for case in syntax::cases().iter().filter(|c| c.file == file) {
        total = total.saturating_add(1);
        let Json::Str(input) = case.input else {
            fail = fail.saturating_add(1);
            continue;
        };
        let expected_failure = EXPECTED_FAILURES
            .iter()
            .any(|(f, i, why)| *f == file && *i == case.index && !why.is_empty());
        if check(input, &case.expected) {
            assert!(!expected_failure, "{file} {} now passes", case.index);
            pass = pass.saturating_add(1);
        } else if expected_failure {
            xfail = xfail.saturating_add(1);
        } else {
            println!("FAILED {file} {}: {input:?}", case.index);
            if let Json::List(items) = &case.expected {
                let actual = component_values(input);
                println!("  lengths {} {}", actual.len(), items.len());
                for (a, e) in actual.iter().zip(items.iter()) {
                    if !same(a, e) {
                        println!("  actual {a:?}\n  expected {e:?}");
                        break;
                    }
                }
            }
            fail = fail.saturating_add(1);
        }
    }
    report(suite, pass, xfail, fail, total);
    assert_eq!(fail, 0, "{suite}");
}

#[test]
fn component_value_lists() {
    run(
        "component_value_list.json",
        "css-parsing-tests component_value_list",
        |input, expected| same_list(&component_values(input), expected),
    );
}

#[test]
fn one_component_values() {
    run(
        "one_component_value.json",
        "css-parsing-tests one_component_value",
        |input, expected| same(&one_component_value(input), expected),
    );
}

#[test]
fn wpt_input_preprocessing() {
    let (mut pass, mut fail, mut total) = (0usize, 0usize, 0usize);
    assert!(
        !wpt::not_run()
            .iter()
            .any(|(f, _)| *f == "input-preprocessing.html")
    );
    for case in wpt::cases()
        .iter()
        .filter(|c| c.file == "input-preprocessing.html")
    {
        total = total.saturating_add(1);
        let input: Vec<u32> = case.input.iter().copied().map(u32::from).collect();
        let tokens = tokenize_all(&filter(&input));
        let expected: Vec<u32> = case
            .expected
            .unwrap_or_default()
            .iter()
            .copied()
            .map(u32::from)
            .collect();
        if tokens == [ExecToken::Ident { value: expected }, ExecToken::Eof] {
            pass = pass.saturating_add(1);
        } else {
            println!(
                "FAILED {} line {} {}: {tokens:?}",
                case.file, case.line, case.helper
            );
            fail = fail.saturating_add(1);
        }
    }
    report("WPT css-syntax input-preprocessing", pass, 0, fail, total);
    assert_eq!(fail, 0);
}
