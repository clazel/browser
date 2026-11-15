//! The parser against the outside world (phase-5.md item 5.4).
//!
//! The proofs show the parser equals `parser/spec.rs`. This file checks both against a suite
//! neither was written from: every `css-parsing-tests` file goes through its entry point.
//!
//! The suite was written for the 2013 draft, before nesting, so a rule's block is a list of
//! component values there. The pinned text parses a block into rules and declarations. So
//! the rule files compare the rule's name and prelude with what the parser gives, and a
//! block with the `{}` block at the same place in a second parse of the same input, as a
//! list of component values. What the text says inside a block is not checked here:
//! `parser/examples.rs` has that, evaluated on the spec the parser is proven equal to.
//!
//! Dropped constructs are `["error", …]` entries in the suite and nothing at all in the
//! text, so those entries are left out of what a result is compared with, but only where
//! `DROPPED` lists the case, with how many and the step that drops them: a case that
//! gains or loses one fails. A suite error for a whole input (`one_rule`,
//! `one_declaration`, `one_component_value`) is matched to our error by what the suite
//! calls it, checked by the pinned text's own steps (`error_matches`).
//!
//! Each expected failure also pins what the parser gives (`EXPECTED_FAILURES`'s last
//! field), written by hand from the cited step of the pinned text, so that a case that
//! fails the suite for one reason cannot start to fail for another.
//!
//! `stylesheet_bytes.json` goes from bytes to rules: §3.2 decodes each case, and the rules are
//! checked here. `conformance_input.rs` checks the encoding it chose.
//!
//! WPT's pages run through the same code: `anb-parsing.html` and `anb-serialization.html`
//! through An+B and its serialization, and `urange-parsing.html` through a `unicode-range`
//! declaration. `input-preprocessing.html` is in `conformance_tokens.rs`.

use clazel_css::input::exec::decode_stylesheet;
use clazel_css::parser::exec_anb::{
    ExecAnB, ExecInteger, ExecPart, read_a_n_plus_b, write_a_n_plus_b,
};
use clazel_css::parser::exec_parse::{
    ExecParsed, parse_component_value, parse_component_values, parse_declaration,
    parse_declaration_list, parse_rule, parse_stylesheet_contents,
};
use clazel_css::parser::rows::{
    ExecDeclaration, ExecDeclarationKind, ExecItem, ExecItemKind, ExecRow,
};
use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, next_token};
use clazel_encoding::labels::exec::get_an_encoding;
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
    Bool(bool),
    Null,
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

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn tagged(tag: &str, value: &[u32]) -> Value {
    Value::List(vec![text(tag), Value::Text(string(value))])
}

fn error(kind: &str) -> Value {
    Value::List(vec![text("error"), text(kind)])
}

/// A result as compact JSON-like text, to pin what the parser gives. A number is its
/// value (`0` for either zero) and `_` stands for a field that is not compared.
fn render(value: &Value) -> String {
    match value {
        Value::AnyText => "_".to_owned(),
        Value::Text(s) => format!("{s:?}"),
        Value::Number(n) if *n == 0.0 => "0".to_owned(),
        Value::Number(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Null => "null".to_owned(),
        Value::List(list) => render_list(list),
    }
}

fn render_list(list: &[Value]) -> String {
    let inner: Vec<String> = list.iter().map(render).collect();
    format!("[{}]", inner.join(","))
}

/// The number as the suite writes it: representation, value and type. The suite's
/// representation is not the source text, so it is not compared.
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

fn block(tag: &str, inner: Vec<Value>) -> Value {
    let mut list = vec![text(tag)];
    list.extend(inner);
    Value::List(list)
}

/// What a text and its rows mean, in the suite's shape.
struct Reader<'a> {
    text: &'a [u32],
    rows: &'a [ExecRow],
    flag: bool,
}

impl Reader<'_> {
    fn token(&self, pos: u32) -> ExecToken {
        next_token(self.text, pos as usize, self.flag).0
    }

    /// The values of rows `lo` up to `hi`, walking back as the rows link.
    fn list(&self, lo: usize, hi: usize) -> Vec<Value> {
        let mut out = Vec::new();
        let mut k = hi;
        while k > lo {
            let last = k.saturating_sub(1);
            out.push(self.value(last));
            k = self.rows.get(last).map_or(lo, |row| row.start as usize);
        }
        out.reverse();
        out
    }

    fn value(&self, k: usize) -> Value {
        let Some(row) = self.rows.get(k) else {
            return text("no row");
        };
        let start = row.start as usize;
        match self.token(row.pos) {
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
                list.extend(self.list(start, k));
                Value::List(list)
            }
            ExecToken::OpenParen => block("()", self.list(start, k)),
            ExecToken::OpenSquare => block("[]", self.list(start, k)),
            ExecToken::OpenCurly => block("{}", self.list(start, k)),
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
            ExecToken::UnicodeRange { start, end } => Value::List(vec![
                text("unicode-range"),
                Value::Number(f64::from(start)),
                Value::Number(f64::from(end)),
            ]),
            ExecToken::Eof => text("EOF"),
        }
    }
}

fn reader(parsed: &ExecParsed) -> Reader<'_> {
    Reader {
        text: &parsed.text,
        rows: &parsed.output.rows,
        flag: false,
    }
}

fn component_values(input: &str) -> Vec<Value> {
    let parsed = parse_component_values(&code_points(input));
    let values = reader(&parsed);
    values.list(0, parsed.output.rows.len())
}

/// A declaration in the suite's shape.
fn declaration(parsed: &ExecParsed, decl: &ExecDeclaration) -> Value {
    let name = match next_token(&parsed.text, decl.name_pos as usize, false).0 {
        ExecToken::Ident { value } => string(&value),
        _ => String::new(),
    };
    let (lo, hi) = (decl.value_lo as usize, decl.value_hi as usize);
    let values = if decl.kind == ExecDeclarationKind::UnicodeRange {
        let start = decl.text_start as usize;
        let end = decl.text_end as usize;
        let rows = Reader {
            text: parsed.text.get(start..end).unwrap_or_default(),
            rows: &parsed.output.rows,
            flag: true,
        };
        rows.list(lo, hi)
    } else {
        reader(parsed).list(lo, hi)
    };
    Value::List(vec![
        text("declaration"),
        Value::Text(name),
        Value::List(values),
        Value::Bool(decl.important),
    ])
}

/// The rule of `item`, in the suite's shape, with `content` as its block.
fn rule(parsed: &ExecParsed, item: &ExecItem, content: Value) -> Value {
    let prelude = Value::List(reader(parsed).list(item.lo as usize, item.hi as usize));
    if item.kind == ExecItemKind::QualifiedRule {
        return Value::List(vec![text("qualified rule"), prelude, content]);
    }
    let name = match next_token(&parsed.text, item.pos as usize, false).0 {
        ExecToken::AtKeyword { value } => string(&value),
        _ => String::new(),
    };
    Value::List(vec![text("at-rule"), Value::Text(name), prelude, content])
}

/// The top-level items, first to last.
fn top_level(items: &[ExecItem]) -> Vec<ExecItem> {
    let mut out = Vec::new();
    let mut k = items.len();
    while let Some(item) = items.get(k.wrapping_sub(1)) {
        out.push(*item);
        k = item.start as usize;
    }
    out.reverse();
    out
}

/// The rule's block as the suite has it: the contents of the `{}` block after its prelude
/// in `values`, from `*at`, which moves past it.
fn block_contents(values: &[Value], at: &mut usize, parsed: &ExecParsed, item: &ExecItem) -> Value {
    let skip = [text(" "), text("<!--"), text("-->"), text(";")];
    while values.get(*at).is_some_and(|v| skip.contains(v)) {
        *at = at.saturating_add(1);
    }
    let top = reader(parsed).list(item.lo as usize, item.hi as usize);
    let keyword = usize::from(item.kind != ExecItemKind::QualifiedRule);
    *at = at.saturating_add(keyword).saturating_add(top.len());
    if item.kind == ExecItemKind::StatementAtRule {
        return Value::Null;
    }
    let contents = match values.get(*at) {
        Some(Value::List(list)) if list.first() == Some(&text("{}")) => {
            list.get(1..).unwrap_or_default().to_vec()
        }
        _ => Vec::new(),
    };
    *at = at.saturating_add(1);
    Value::List(contents)
}

/// True for an at-rule named `@charset`. §8.3: "any occurrences of an @charset rule must be
/// treated as an unrecognized rule, and thus dropped as invalid when the stylesheet is
/// grammar-checked". The parser is a generic processor, so the check is its user's, here
/// this test's.
fn is_charset(value: &Value) -> bool {
    matches!(value, Value::List(list) if list.get(..2).is_some_and(
        |head| head.first() == Some(&text("at-rule"))
            && matches!(head.get(1), Some(Value::Text(name))
                if name.eq_ignore_ascii_case("charset"))))
}

/// The rules of `parsed`, whose input was `input`.
fn rules(parsed: &ExecParsed, input: &str) -> Vec<Value> {
    let values = component_values(input);
    let mut at = 0usize;
    top_level(&parsed.output.items)
        .iter()
        .map(|item| {
            let content = block_contents(&values, &mut at, parsed, item);
            rule(parsed, item, content)
        })
        .filter(|value| !is_charset(value))
        .collect()
}

/// Whether a result is what the suite expects. Numbers compare to within rounding.
fn same(actual: &Value, expected: &Json) -> bool {
    match (actual, expected) {
        (Value::AnyText, Json::Str(_)) | (Value::Null, Json::Null) => true,
        (Value::Text(a), Json::Str(e)) => a == e,
        (Value::Bool(a), Json::Bool(e)) => a == e,
        (Value::Number(a), Json::Num(e)) => e.parse::<f64>().is_ok_and(|e| {
            let scale = e.abs().max(1.0);
            (a - e).abs() <= scale * 1e-9
        }),
        (Value::List(a), Json::List(e)) => {
            a.len() == e.len() && a.iter().zip(e.iter()).all(|(a, e)| same(a, e))
        }
        _ => false,
    }
}

/// True for an `["error", …]` entry.
fn is_error(entry: &Json) -> bool {
    matches!(entry, Json::List([Json::Str("error"), ..]))
}

/// A list of results against a suite's list, without its error entries.
fn same_list(actual: &[Value], expected: &Json) -> bool {
    let Json::List(entries) = expected else {
        return false;
    };
    let kept: Vec<&Json> = entries.iter().filter(|e| !is_error(e)).collect();
    actual.len() == kept.len() && actual.iter().zip(kept).all(|(a, e)| same(a, e))
}

/// A list of values against a suite's list, all of it: an error here is a token.
fn same_values(actual: &[Value], expected: &Json) -> bool {
    matches!(expected, Json::List(e) if actual.len() == e.len()
        && actual.iter().zip(e.iter()).all(|(a, e)| same(a, e)))
}

/// Cases that differ from the pinned text, as (file, index, why, what the parser gives, as
/// `render` shows it). `css-parsing-tests` was
/// written for the 2013 draft, and records one parser's reading.
const EXPECTED_FAILURES: &[(&str, usize, &str, &str)] = &[
    (
        "rule_list.json",
        11,
        "the 2013 text's rule lists kept <!-- and --> in preludes when not at the top level; \
         the pinned text has no such list, and \"parse a stylesheet's contents\" skips them",
        r#"[["qualified rule",[],[]]]"#,
    ),
    (
        "one_declaration.json",
        11,
        "step 4 of \"consume a declaration\" discards whitespace after the colon, and step 7 \
         removes it at the end; the 2013 text kept both",
        r#"["declaration","foo",[],false]"#,
    ),
    (
        "one_declaration.json",
        12,
        "step 5 stops at the semicolon, which leaves the stream not empty, so \"parse a \
         declaration\" returns a syntax error; the 2013 text took it into the value",
        r#"["error","invalid"]"#,
    ),
    (
        "one_declaration.json",
        14,
        "as above: step 5 stops at the first semicolon",
        r#"["error","invalid"]"#,
    ),
    (
        "one_declaration.json",
        15,
        "whitespace trimmed by steps 4 and 7, as above",
        r#"["declaration","foo",[["number",_,9000,"integer"]],true]"#,
    ),
    (
        "one_declaration.json",
        16,
        "whitespace trimmed by steps 4 and 7, as above",
        r#"["declaration","foo",[["number",_,9000,"integer"]],true]"#,
    ),
    (
        "one_declaration.json",
        17,
        "whitespace trimmed by step 4, as above",
        r#"["declaration","foo",[["number",_,9000,"integer"]," ","!",["ident","İmportant"]],false]"#,
    ),
    (
        "one_declaration.json",
        18,
        "whitespace trimmed by step 4, as above",
        r#"["declaration","foo",[["number",_,9000,"integer"]," ","!",["ident","important"],"!"],false]"#,
    ),
    (
        "one_declaration.json",
        19,
        "whitespace trimmed by step 4, as above",
        r#"["declaration","foo",[["number",_,9000,"integer"]," ",["ident","important"]],false]"#,
    ),
    (
        "one_declaration.json",
        21,
        "step 8: a {}-block with any other value is not a declaration",
        r#"["error","invalid"]"#,
    ),
    (
        "declaration_list.json",
        6,
        "\"parse a list of declarations\" discards at-rules; the 2013 list returned them",
        r#"[["declaration","a",[["ident","b"]],false]]"#,
    ),
    (
        "declaration_list.json",
        7,
        "as above: at-rules are discarded",
        r#"[["declaration","a",[["ident","b"]],false]]"#,
    ),
    (
        "declaration_list.json",
        8,
        "a list of declarations has no qualified rules in the pinned text: the first item is \
         bad remnants up to the semicolon, and the at-rule after it is discarded",
        "[]",
    ),
    (
        "component_value_list.json",
        6,
        "U+0080 and U+0081 are not non-ASCII ident code points in the pinned text, which \
         lists ranges from U+00B7; the suite's draft took every non-ASCII code point",
        r#"[["ident","-"]," ",["ident","red0"]," ",["ident","-red"]," ",["ident","--red"]," ",["ident","--red blue"]," ",["dimension",_,0,"integer","red"]," ",["dimension",_,0,"integer","red"]," ",["ident","��red"]," ",["ident","_Red"]," ",".",["ident","red"]," ",["ident","rêd"]," ",["ident","rêd"]," ","\u{7f}","\u{80}","\u{81}"]"#,
    ),
    (
        "component_value_list.json",
        38,
        "the pinned text has no match tokens, so \"~=\" is two delim tokens",
        r#"["~","=","|","=","^","=","$","=","*","=","|","|","<!--",["ident","----"],">"," ","|","|"," ","~","="]"#,
    ),
    (
        "component_value_list.json",
        39,
        "the pinned text has no match tokens, so \"^=\" is two delim tokens",
        r#"[["ident","a"],":",["function","not",["[]",["ident","href"],"^","=",["ident","http:"]],","," ",["[]",["ident","href"]," ","^","="," ",["string","https:"]," "]]," ",["{}"," ",["ident","color"],":"," ",["function","rgba",["percentage",_,0,"integer"],","," ",["percentage",_,100,"integer"],","," ",["percentage",_,50,"integer"]],";"," "]]"#,
    ),
];

/// Cases whose expected list has `["error", "invalid"]` entries, which stand for a
/// construct the pinned text drops without a trace, as (file, index, how many, the step
/// that drops them). A case with a different number fails, and so does one not listed.
const DROPPED: &[(&str, usize, usize, &str)] = &[
    (
        "stylesheet.json",
        1,
        1,
        "§5.5.1 anything else: \"consume a qualified rule\" reaches EOF in the prelude `foo`: \"Return nothing\"",
    ),
    ("stylesheet.json", 2, 1, "as above, for `foo 4`"),
    (
        "stylesheet.json",
        5,
        1,
        "`@charset 4 {}` is dropped by `is_charset`, which is §8.3 of the 2013 text, not the pinned text",
    ),
    (
        "stylesheet.json",
        16,
        1,
        "`{}` is a rule with an empty prelude (§5.5.3 `<{-token>`), and `a` is as `foo` above",
    ),
    ("rule_list.json", 1, 1, "as `stylesheet.json` 1"),
    ("rule_list.json", 2, 1, "as `stylesheet.json` 2"),
    (
        "rule_list.json",
        4,
        1,
        "`@charset;` is dropped by `is_charset`, as `stylesheet.json` 5",
    ),
    (
        "rule_list.json",
        13,
        1,
        "§5.5.1 `<CDC-token>`: \"Discard a token\", so the `-->` after `div {}` is nothing",
    ),
    ("rule_list.json", 14, 1, "as `stylesheet.json` 16"),
    (
        "declaration_list.json",
        3,
        1,
        "§5.4.5 then §5.5.6 step 3: after the ident `z` the next token is `;`, not a colon, so \"consume the remnants of a bad declaration\" discards through the `;`",
    ),
    (
        "declaration_list.json",
        5,
        1,
        "§5.5.6 step 3: after the ident `c` the next token is the delim `+`, not a colon: the remnants of `c+:d` are discarded",
    ),
];

/// The files whose cases are lists of results, and so can have dropped entries.
const LIST_FILES: &[&str] = &["stylesheet.json", "rule_list.json", "declaration_list.json"];

/// Our error and the suite's `["error", kind]` agree if the kind is what the text's steps
/// say of `input`. The text has one syntax error for all of them: `empty` is "If input is
/// empty, return a syntax error" after discarding whitespace, `extra-input` is the error of
/// the last step, after a first item was read, and `invalid` is the step before that,
/// where there was no first item. `first_item` says whether the input starts with one.
fn error_matches(
    expected: &Json,
    actual: &Value,
    input: &str,
    first_item: impl Fn(&str) -> bool,
) -> bool {
    let Json::List([Json::Str("error"), Json::Str(kind)]) = expected else {
        return false;
    };
    if !is_error_value(actual) {
        return false;
    }
    let blank = component_values(input).iter().all(|v| *v == text(" "));
    match *kind {
        "empty" => blank,
        "extra-input" => !blank && first_item(input),
        "invalid" => !blank && !first_item(input),
        _ => false,
    }
}

fn report(suite: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
}

/// Runs `file`, whose cases are strings.
fn run(
    file: &str,
    suite: &str,
    check: impl Fn(&str, &Json) -> bool,
    show: impl Fn(&str) -> String,
) {
    let (mut pass, mut xfail, mut fail, mut total) = (0usize, 0usize, 0usize, 0usize);
    let mut dropped_seen = 0usize;
    for case in syntax::cases().iter().filter(|c| c.file == file) {
        total = total.saturating_add(1);
        let Json::Str(input) = case.input else {
            fail = fail.saturating_add(1);
            continue;
        };
        if LIST_FILES.contains(&file)
            && let Json::List(entries) = &case.expected
        {
            let dropped = entries.iter().filter(|e| is_error(e)).count();
            let want = DROPPED
                .iter()
                .find(|(f, i, _, _)| *f == file && *i == case.index)
                .map_or(0, |(_, _, n, _)| *n);
            dropped_seen = dropped_seen.saturating_add(dropped);
            if dropped != want {
                println!(
                    "FAILED {file} {}: {dropped} error entries, DROPPED lists {want}",
                    case.index
                );
                fail = fail.saturating_add(1);
                continue;
            }
        }
        let pinned = EXPECTED_FAILURES
            .iter()
            .find(|(f, i, why, _)| *f == file && *i == case.index && !why.is_empty());
        if check(input, &case.expected) {
            assert!(pinned.is_none(), "{file} {} now passes", case.index);
            pass = pass.saturating_add(1);
        } else if let Some((_, _, _, ours)) = pinned {
            let shown = show(input);
            if shown == *ours {
                xfail = xfail.saturating_add(1);
            } else {
                println!("FAILED {file} {}: {input:?}", case.index);
                println!("  actual   {shown}");
                println!("  pinned   {ours}");
                fail = fail.saturating_add(1);
            }
        } else {
            println!("FAILED {file} {}: {input:?}", case.index);
            println!("  actual   {}", show(input));
            println!("  expected {:?}", case.expected);
            fail = fail.saturating_add(1);
        }
    }
    let listed: usize = DROPPED
        .iter()
        .filter(|(f, _, _, _)| *f == file)
        .map(|(_, _, n, _)| *n)
        .sum();
    assert_eq!(
        dropped_seen, listed,
        "{file}: DROPPED and the suite disagree"
    );
    report(suite, pass, xfail, fail, total);
    assert_eq!(fail, 0, "{suite}");
}

fn stylesheet(input: &str) -> Vec<Value> {
    rules(&parse_stylesheet_contents(&code_points(input)), input)
}

#[test]
fn stylesheets() {
    run(
        "stylesheet.json",
        "css-parsing-tests stylesheet",
        |input, expected| same_list(&stylesheet(input), expected),
        |input| render_list(&stylesheet(input)),
    );
}

#[test]
fn rule_lists() {
    run(
        "rule_list.json",
        "css-parsing-tests rule_list",
        |input, expected| same_list(&stylesheet(input), expected),
        |input| render_list(&stylesheet(input)),
    );
}

fn one_rule(input: &str) -> Value {
    let (parsed, found) = parse_rule(&code_points(input));
    if !found {
        return error("invalid");
    }
    rules(&parsed, input).pop().unwrap_or(error("invalid"))
}

#[test]
fn one_rules() {
    run(
        "one_rule.json",
        "css-parsing-tests one_rule",
        |input, expected| {
            same(&one_rule(input), expected)
                || error_matches(expected, &one_rule(input), input, |input| {
                    !stylesheet(input).is_empty()
                })
        },
        |input| render(&one_rule(input)),
    );
}

fn is_error_value(value: &Value) -> bool {
    matches!(value, Value::List(list) if list.first() == Some(&text("error")))
}

fn one_declaration(input: &str) -> Value {
    let (parsed, found) = parse_declaration(&code_points(input));
    if !found {
        return error("invalid");
    }
    match parsed.output.declarations.first() {
        Some(decl) => declaration(&parsed, decl),
        None => error("invalid"),
    }
}

#[test]
fn one_declarations() {
    run(
        "one_declaration.json",
        "css-parsing-tests one_declaration",
        |input, expected| {
            same(&one_declaration(input), expected)
                || error_matches(expected, &one_declaration(input), input, |input| {
                    !declaration_list(input).is_empty()
                })
        },
        |input| render(&one_declaration(input)),
    );
}

fn declaration_list(input: &str) -> Vec<Value> {
    let parsed = parse_declaration_list(&code_points(input));
    parsed
        .output
        .declarations
        .iter()
        .map(|d| declaration(&parsed, d))
        .collect()
}

#[test]
fn declaration_lists() {
    run(
        "declaration_list.json",
        "css-parsing-tests declaration_list",
        |input, expected| same_list(&declaration_list(input), expected),
        |input| render_list(&declaration_list(input)),
    );
}

fn one_value(input: &str) -> Value {
    let (parsed, found) = parse_component_value(&code_points(input));
    if !found {
        return error("invalid");
    }
    reader(&parsed).value(parsed.output.rows.len().saturating_sub(1))
}

#[test]
fn component_value_lists() {
    run(
        "component_value_list.json",
        "css-parsing-tests component_value_list, parsed",
        |input, expected| same_values(&component_values(input), expected),
        |input| render_list(&component_values(input)),
    );
}

#[test]
fn one_component_values() {
    run(
        "one_component_value.json",
        "css-parsing-tests one_component_value, parsed",
        |input, expected| {
            same(&one_value(input), expected)
                || error_matches(expected, &one_value(input), input, |input| {
                    component_values(input)
                        .iter()
                        .filter(|v| **v != text(" "))
                        .count()
                        > 1
                })
        },
        |input| render(&one_value(input)),
    );
}

/// A part of an An+B result as an integer, whatever its size.
fn part_value(anb: &ExecAnB, part: ExecPart) -> i128 {
    let digits = |v: &[u32]| string(v).parse::<i128>().unwrap_or(i128::MAX);
    match part {
        ExecPart::Literal { value } => i128::from(value),
        ExecPart::Value { index, negated } => {
            let value = match anb.tokens.get(index) {
                Some(ExecToken::Number { number } | ExecToken::Dimension { number, .. }) => {
                    digits(&number.number_part)
                }
                _ => 0,
            };
            if negated {
                value.saturating_neg()
            } else {
                value
            }
        }
        ExecPart::Remainder { index, from } => {
            let word = match anb.tokens.get(index) {
                Some(ExecToken::Ident { value }) => value.as_slice(),
                Some(ExecToken::Dimension { unit, .. }) => unit.as_slice(),
                _ => &[],
            };
            digits(word.get(from..).unwrap_or_default())
        }
    }
}

fn a_n_plus_b(input: &str) -> Option<(i128, i128)> {
    read_a_n_plus_b(&code_points(input))
        .map(|anb| (part_value(&anb, anb.a), part_value(&anb, anb.b)))
}

fn same_a_n_plus_b(input: &str, expected: &Json) -> bool {
    match (a_n_plus_b(input), expected) {
        (None, Json::Null) => true,
        (Some((a, b)), Json::List([Json::Num(ea), Json::Num(eb)])) => {
            ea.parse::<i128>().is_ok_and(|e| e == a) && eb.parse::<i128>().is_ok_and(|e| e == b)
        }
        _ => false,
    }
}

#[test]
fn a_n_plus_b_cases() {
    run(
        "An+B.json",
        "css-parsing-tests An+B",
        same_a_n_plus_b,
        |input| format!("{:?}", a_n_plus_b(input)),
    );
}

/// What a page wants of `value`, an integer as the serializer takes it.
fn integer(value: i128) -> ExecInteger {
    ExecInteger {
        negative: value < 0,
        magnitude: u64::try_from(value.unsigned_abs()).unwrap_or(u64::MAX),
    }
}

/// The input of a WPT case.
fn units(input: &[u16]) -> String {
    String::from_utf16_lossy(input)
}

/// Runs the cases of `page`, where `actual` gives what the page would see, and `None` is
/// what it calls invalid.
fn run_wpt(page: &str, suite: &str, actual: impl Fn(&str) -> Option<String>) {
    let (mut pass, mut xfail, mut fail, mut total) = (0usize, 0usize, 0usize, 0usize);
    for case in wpt::cases().iter().filter(|c| c.file == page) {
        total = total.saturating_add(1);
        let input = units(case.input);
        let expected = case.expected.map(units);
        let pinned = WPT_EXPECTED_FAILURES
            .iter()
            .find(|(f, i, why, _)| *f == page && *i == input && !why.is_empty());
        let got = actual(&input);
        let matches = match (&got, &expected) {
            (Some(g), Some(e)) => g.eq_ignore_ascii_case(e),
            (None, None) => true,
            _ => false,
        };
        if matches {
            assert!(pinned.is_none(), "{page} {input:?} now passes");
            pass = pass.saturating_add(1);
        } else if let Some((_, _, _, ours)) = pinned
            && got.as_deref() == *ours
        {
            xfail = xfail.saturating_add(1);
        } else {
            println!(
                "FAILED {page} line {} {}: {input:?}",
                case.line, case.helper
            );
            println!("  actual   {got:?}");
            println!("  expected {expected:?}");
            fail = fail.saturating_add(1);
        }
    }
    report(suite, pass, xfail, fail, total);
    assert_eq!(fail, 0, "{suite}");
}

/// Cases of WPT that differ from the pinned text, as (page, input, why, what the parser
/// gives). For a `unicode-range` value with a comment between the tokens of the range, the
/// value is not one `<unicode-range-token>`: "would start a unicode-range" looks
/// at the code points after `u`, which are `/**/`, so the value is the tokens `u`, `+`, and
/// so on, and it is no range (`None`).
const WPT_EXPECTED_FAILURES: &[(&str, &str, &str, Option<&str>)] = &[
    (
        "urange-parsing.html",
        "u/**/+/**/a/**/?",
        COMMENT_IN_RANGE,
        None,
    ),
    (
        "urange-parsing.html",
        "u/**/+0a/**/?",
        COMMENT_IN_RANGE,
        None,
    ),
    (
        "urange-parsing.html",
        "u/**/+0/**/?",
        COMMENT_IN_RANGE,
        None,
    ),
    (
        "urange-parsing.html",
        "u/**/+0/**/-0a",
        COMMENT_IN_RANGE,
        None,
    ),
    (
        "urange-parsing.html",
        "u/**/+0/**/-1",
        COMMENT_IN_RANGE,
        None,
    ),
    ("urange-parsing.html", "u/**/+/**/?", COMMENT_IN_RANGE, None),
];

/// Why a range with a comment in it is not one.
const COMMENT_IN_RANGE: &str = "the page tests a <urange> grammar over tokens, where comments can \
     go between them; the pinned text makes the range one token, read with unicode ranges \
     allowed, and \"would start a unicode-range\" looks at adjacent code points";

/// What the WPT table could not read stays as it was. This file runs three of its pages,
/// and the table's one direct `test()` of `urange-parsing.html` is among what is not read.
#[test]
fn what_could_not_be_read_stays_listed() {
    assert!(
        wpt::not_run()
            .iter()
            .any(|(f, _)| *f == "urange-parsing.html")
    );
    assert!(!wpt::not_run().iter().any(|(f, _)| *f == "anb-parsing.html"));
}

fn serialized_a_n_plus_b(input: &str) -> Option<String> {
    let (a, b) = a_n_plus_b(input)?;
    Some(string(&write_a_n_plus_b(integer(a), integer(b))))
}

#[test]
fn wpt_a_n_plus_b_parsing() {
    run_wpt(
        "anb-parsing.html",
        "WPT css-syntax anb-parsing",
        serialized_a_n_plus_b,
    );
}

#[test]
fn wpt_a_n_plus_b_serialization() {
    run_wpt(
        "anb-serialization.html",
        "WPT css-syntax anb-serialization",
        serialized_a_n_plus_b,
    );
}

/// The value of a `unicode-range` declaration, split at its top-level commas: each entry is
/// a range if it is one `<unicode-range-token>` of valid code points.
fn ranges(input: &str) -> Vec<Option<(u32, u32)>> {
    let mut source = String::from("unicode-range:");
    source.push_str(input);
    let (parsed, found) = parse_declaration(&code_points(&source));
    let list = match parsed.output.declarations.first() {
        Some(decl) if found => declaration(&parsed, decl),
        _ => return vec![None],
    };
    let Value::List(fields) = list else {
        return vec![None];
    };
    let Some(Value::List(values)) = fields.get(2) else {
        return vec![None];
    };
    values
        .split(|v| *v == text(","))
        .map(|group| {
            let tokens: Vec<&Value> = group.iter().filter(|v| **v != text(" ")).collect();
            let [Value::List(token)] = tokens.as_slice() else {
                return None;
            };
            match token.as_slice() {
                [tag, Value::Number(start), Value::Number(end)]
                    if *tag == text("unicode-range") =>
                {
                    let (start, end) = (*start as u32, *end as u32);
                    (start <= end && end <= 0x10_FFFF).then_some((start, end))
                }
                _ => None,
            }
        })
        .collect()
}

fn same_ranges(input: &str, expected: &Json) -> bool {
    let actual = ranges(input);
    let Json::List(entries) = expected else {
        return false;
    };
    actual.len() == entries.len()
        && actual
            .iter()
            .zip(entries.iter())
            .all(|(a, e)| match (a, e) {
                (None, Json::Null) => true,
                (Some((s, t)), Json::List([Json::Num(es), Json::Num(et)])) => {
                    es.parse::<u32>().is_ok_and(|e| e == *s)
                        && et.parse::<u32>().is_ok_and(|e| e == *t)
                }
                _ => false,
            })
}

#[test]
fn unicode_ranges() {
    run(
        "urange.json",
        "css-parsing-tests urange",
        same_ranges,
        |input| format!("{:?}", ranges(input)),
    );
}

#[test]
fn wpt_unicode_ranges() {
    run_wpt(
        "urange-parsing.html",
        "WPT css-syntax urange-parsing",
        |input| match ranges(input).as_slice() {
            [Some((start, end))] if start == end => Some(format!("U+{start:X}")),
            [Some((start, end))] => Some(format!("U+{start:X}-{end:X}")),
            _ => None,
        },
    );
}

/// The string under `key` in a case of `stylesheet_bytes.json`, if it is not null.
fn byte_field(input: &Json, key: &str) -> Option<&'static str> {
    match input {
        Json::Obj(fields) => fields.iter().find_map(|(k, value)| match value {
            Json::Str(text) if *k == key => Some(*text),
            _ => None,
        }),
        _ => None,
    }
}

/// The rules of a case's bytes, decoded by §3.2 with the labels the case gives.
fn rules_of_bytes(case: &Json) -> Option<Vec<Value>> {
    let code_points = |text: &str| -> Vec<u32> { text.chars().map(u32::from).collect() };
    let raw: Vec<u8> = byte_field(case, "css_bytes")?
        .chars()
        .map(|c| u8::try_from(u32::from(c)).unwrap_or(0))
        .collect();
    let protocol = byte_field(case, "protocol_encoding").map(code_points);
    let environment =
        byte_field(case, "environment_encoding").and_then(|l| get_an_encoding(&code_points(l)));
    let decoded = decode_stylesheet(&raw, protocol.as_deref(), environment)?;
    let input: String = decoded
        .iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{FFFD}'))
        .collect();
    Some(stylesheet(&input))
}

#[test]
fn stylesheet_bytes_rules() {
    let (mut pass, mut fail, mut total) = (0usize, 0usize, 0usize);
    for case in syntax::cases()
        .iter()
        .filter(|c| c.file == "stylesheet_bytes.json")
    {
        total = total.saturating_add(1);
        let matches = match &case.expected {
            Json::List([expected, _]) => {
                rules_of_bytes(&case.input).is_some_and(|actual| same_list(&actual, expected))
            }
            _ => false,
        };
        if matches {
            pass = pass.saturating_add(1);
        } else {
            println!(
                "FAILED stylesheet_bytes.json {}: {:?}",
                case.index, case.input
            );
            fail = fail.saturating_add(1);
        }
    }
    report(
        "css-parsing-tests stylesheet_bytes, rules",
        pass,
        0,
        fail,
        total,
    );
    assert_eq!(fail, 0, "stylesheet_bytes");
}
