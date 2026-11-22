//! The pattern parser over the regular expression literals of the vendored
//! Test262 syntax tests (`clazel-js-lexer`'s `tests/data/test262/test/language/`
//! and its generated table; phase-7.md item 7.1).
//!
//! The vendored subset holds only `test/language/`: `test/built-ins/RegExp/`
//! (`new RegExp(..)`, `property-escapes/generated/`) is not vendored, so it is
//! not run here. What is run is every regular expression literal of a test,
//! found by tokenizing it with `clazel-js-lexer` (a literal is read where the
//! previous token allows one, with template substitutions tracked), its body
//! and flags parsed here; and the string argument of every `eval("..")` call,
//! tokenized the same way, with the call's expectation read from the text
//! around it: inside `assert.throws(SyntaxError, ..)` it must be rejected,
//! elsewhere accepted.
//!
//! - **Suite "Test262 language/literals/regexp"**: every test under that
//!   directory. A test that is not `negative` passes if every literal in it
//!   is accepted and every `eval` string expected to throw has a literal that
//!   is rejected; a test with `negative: phase: parse` (or `early`) passes if
//!   some literal is rejected.
//! - **Suite "Test262 other tests' regexp literals"**: every other test that
//!   is not `negative` and holds a literal: every literal must be accepted.
//!   (Negative tests elsewhere are negative for other reasons.)
//!
//! A unit is one test. It is an expected failure (`xfail`) if the table marks
//! it (a feature newer than the edition) with that reason, or if [`XFAIL`]
//! lists it with a reason: a test whose error is not in a pattern or flags
//! this crate is given, or which no scan can judge. Every other failure, and
//! every listed test that passes, fails the test.
//!
//! The Unicode property names are checked against the vendored UCD in
//! `conformance_names.rs`; here `\p{sc=..}` names are accepted by syntax.

use clazel_js_lexer::api::{Element, Next, Value};
use clazel_js_lexer::exec::next_token;
use clazel_js_lexer::spec::{ElementKind, Goal, TemplateKind};
use clazel_js_regexp::{Flags, parse};
use std::path::PathBuf;

/// A test's row in the generated table.
struct Case {
    path: &'static str,
    flags: &'static [&'static str],
    features: &'static [&'static str],
    includes: &'static [&'static str],
    negative: Option<(&'static str, &'static str)>,
    expect: Expect,
}

/// Whether a test is expected to pass, and if not why.
enum Expect {
    Run,
    Fail(&'static str),
}

include!("../../clazel-js-lexer/tests/generated/test262.rs");

/// The tests whose error is not a pattern's, by path and why.
const XFAIL: &[(&str, &str)] = &[
    (
        "language/literals/regexp/S7.8.5_A2.2_T2.js",
        "`/a//.source;`: the lexer reads `/a/` then a division; clazel-js-syntax rejects the rest, no pattern is invalid",
    ),
    (
        "language/literals/regexp/early-err-flags-unicode-escape.js",
        "`/./\\u0067;`: the lexer ends the flags at the backslash; clazel-js-syntax rejects the next token, no flag text is invalid",
    ),
];

/// Why a test with nothing to scan is not judged here: it tests the lexical
/// grammar of a literal (a lexical error, clazel-js-lexer's evidence), or
/// builds its pattern by computing a string.
const NOT_SCANNED: &str = "a lexical error (clazel-js-lexer's evidence) or a pattern built by computing a string: no literal to parse";

const DIR: &str = "language/literals/regexp/";

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../clazel-js-lexer/tests/data/test262/test")
}

/// One literal of a test: its body and its flags, UTF-16.
struct Literal {
    body: Vec<u16>,
    flags: Vec<u16>,
}

fn utf16(src: &[u32]) -> Vec<u16> {
    let mut out = Vec::new();
    for &c in src {
        match char::from_u32(c) {
            Some(ch) => {
                let mut buf = [0u16; 2];
                out.extend_from_slice(ch.encode_utf16(&mut buf));
            }
            // A lone surrogate: a source text taken from a string value.
            None => out.push(u16::try_from(c).unwrap_or(0xFFFD)),
        }
    }
    out
}

fn code_points(units: &[u16]) -> Vec<u32> {
    char::decode_utf16(units.iter().copied())
        .map(|r| r.map_or_else(|e| u32::from(e.unpaired_surrogate()), u32::from))
        .collect()
}

fn text_of(src: &[u32], el: &Element) -> String {
    src.get(el.start..el.end)
        .unwrap_or_default()
        .iter()
        .filter_map(|&c| char::from_u32(c))
        .collect()
}

/// Whether a regular expression literal may follow `el`.
fn regexp_allowed_after(text: &str, el: &Element) -> bool {
    match el.kind {
        ElementKind::NumericLiteral
        | ElementKind::StringLiteral
        | ElementKind::RegularExpressionLiteral
        | ElementKind::PrivateIdentifier
        | ElementKind::Template(_) => false,
        ElementKind::IdentifierName => matches!(
            text,
            "return"
                | "typeof"
                | "instanceof"
                | "in"
                | "of"
                | "new"
                | "delete"
                | "void"
                | "throw"
                | "case"
                | "do"
                | "else"
                | "yield"
                | "await"
        ),
        ElementKind::Punctuator
        | ElementKind::DivPunctuator
        | ElementKind::RightBracePunctuator => !matches!(text, ")" | "]"),
        _ => true,
    }
}

/// What `scan` found in a source text.
#[derive(Default)]
struct Scan {
    /// The regular expression literals.
    literals: Vec<Literal>,
    /// The string arguments of `eval("..")` calls, as code points, and whether
    /// the call is inside `assert.throws(SyntaxError, ..)`.
    evals: Vec<(Vec<u32>, bool)>,
}

/// The regular expression literals of `src` and its `eval` strings, or
/// `Err` if the tokenizer gave up.
fn scan(src: &[u32]) -> Result<Scan, ()> {
    let mut out = Scan::default();
    let mut pos = 0usize;
    let mut allowed = true;
    // Open `{` counts, one per template substitution being read.
    let mut templates: Vec<usize> = Vec::new();
    // The last tokens' texts, for `eval (` and `assert . throws ( SyntaxError ,`.
    let mut recent: Vec<String> = Vec::new();
    let mut parens = 0usize;
    // The paren depth inside `assert.throws(SyntaxError, ..`.
    let mut throws: Option<usize> = None;
    // A string right after `eval (`, waiting for the `)`.
    let mut pending: Option<Vec<u32>> = None;
    loop {
        let in_tail = templates.last() == Some(&0);
        let goal = match (pos == 0, in_tail, allowed) {
            (true, _, _) => Goal::InputElementHashbangOrRegExp,
            (_, true, true) => Goal::InputElementRegExpOrTemplateTail,
            (_, true, false) => Goal::InputElementTemplateTail,
            (_, false, true) => Goal::InputElementRegExp,
            (_, false, false) => Goal::InputElementDiv,
        };
        let tok = match next_token(src, pos, goal, false) {
            Ok(Next::Eof { .. }) => return Ok(out),
            Ok(Next::Token(t)) => t,
            Err(_) => return Err(()),
        };
        let el = tok.element;
        pos = el.end;
        let text = text_of(src, &el);
        if let Some(units) = pending.take()
            && text == ")"
        {
            out.evals.push((units, throws.is_some()));
        }
        match &el.value {
            Value::RegExp { body_end } => {
                let body = src
                    .get(el.start.saturating_add(1)..*body_end)
                    .unwrap_or_default();
                let flags = src
                    .get(body_end.saturating_add(1)..el.end)
                    .unwrap_or_default();
                out.literals.push(Literal {
                    body: utf16(body),
                    flags: utf16(flags),
                });
            }
            Value::String { units } => {
                let n = recent.len();
                let after_eval = n >= 2
                    && recent.get(n.saturating_sub(2)).is_some_and(|t| t == "eval")
                    && recent.last().is_some_and(|t| t == "(");
                if after_eval {
                    pending = Some(code_points(units));
                }
            }
            _ => {}
        }
        match el.kind {
            ElementKind::Template(kind) => {
                // Head and Middle open a substitution; Middle and Tail close one.
                match kind {
                    TemplateKind::Head => templates.push(0),
                    TemplateKind::Middle => {
                        templates.pop();
                        templates.push(0);
                    }
                    TemplateKind::Tail => {
                        templates.pop();
                    }
                    TemplateKind::NoSubstitution => {}
                }
            }
            ElementKind::Punctuator => match text.as_str() {
                "{" => {
                    if let Some(n) = templates.last_mut() {
                        *n = n.saturating_add(1);
                    }
                }
                "(" => parens = parens.saturating_add(1),
                ")" => {
                    parens = parens.saturating_sub(1);
                    if throws.is_some_and(|t| parens < t) {
                        throws = None;
                    }
                }
                "," => {
                    // `assert . throws ( SyntaxError ,` ends with this comma.
                    let tail: Vec<&str> = recent.iter().rev().take(5).map(String::as_str).collect();
                    if tail == ["SyntaxError", "(", "throws", ".", "assert"] {
                        throws = Some(parens);
                    }
                }
                _ => {}
            },
            ElementKind::RightBracePunctuator => {
                if let Some(n) = templates.last_mut() {
                    *n = n.saturating_sub(1);
                }
            }
            _ => {}
        }
        allowed = regexp_allowed_after(&text, &el);
        recent.push(text);
        if recent.len() > 8 {
            recent.remove(0);
        }
    }
}

/// Whether the parser accepts a literal: flags, then the pattern.
fn accepts(l: &Literal) -> bool {
    match Flags::parse(&l.flags) {
        Ok(f) => parse(&l.body, f).is_ok(),
        Err(_) => false,
    }
}

/// What a test did.
enum Outcome {
    Pass,
    Fail(String),
    /// There is nothing to judge: no literal, no `eval` string.
    Nothing,
}

fn judge(case: &Case) -> Result<Outcome, String> {
    let path = root().join(case.path);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", case.path))?;
    let src: Vec<u32> = text.chars().map(u32::from).collect();
    let negative =
        matches!(case.negative, Some((phase, _)) if phase == "parse" || phase == "early");
    let Ok(file) = scan(&src) else {
        // A lexical error: for a negative test, the lexer's to judge.
        return Ok(if negative {
            Outcome::Nothing
        } else {
            Outcome::Fail("cannot tokenize".into())
        });
    };
    let rejected = file.literals.iter().filter(|l| !accepts(l)).count();
    if negative {
        if file.literals.is_empty() {
            return Ok(Outcome::Nothing);
        }
        return Ok(if rejected > 0 {
            Outcome::Pass
        } else {
            Outcome::Fail("no literal is rejected".into())
        });
    }
    if rejected > 0 {
        return Ok(Outcome::Fail(format!(
            "{rejected} of {} literals rejected",
            file.literals.len()
        )));
    }
    let mut checks = file.literals.len();
    for (string, must_throw) in &file.evals {
        let Ok(inner) = scan(string) else {
            // A lexical error in the string: the lexer's to judge (whether the
            // test expects it, as the `S7.8.5_*` tests do with try/catch).
            continue;
        };
        if inner.literals.is_empty() {
            continue;
        }
        let inner_rejected = inner.literals.iter().filter(|l| !accepts(l)).count();
        checks = checks.saturating_add(1);
        if *must_throw && inner_rejected == 0 {
            return Ok(Outcome::Fail(
                "an eval string that must throw is accepted".into(),
            ));
        }
        if !*must_throw && inner_rejected > 0 {
            return Ok(Outcome::Fail(
                "an eval string that must parse is rejected".into(),
            ));
        }
    }
    Ok(if checks == 0 {
        Outcome::Nothing
    } else {
        Outcome::Pass
    })
}

struct Suite {
    name: &'static str,
    total: usize,
    pass: usize,
    xfail: usize,
    fail: Vec<String>,
    listed: Vec<String>,
}

impl Suite {
    fn new(name: &'static str) -> Suite {
        Suite {
            name,
            total: 0,
            pass: 0,
            xfail: 0,
            fail: Vec::new(),
            listed: Vec::new(),
        }
    }

    fn count(&mut self) {
        self.total = self.total.saturating_add(1);
    }

    fn xfail(&mut self, path: &str, why: &str) {
        self.xfail = self.xfail.saturating_add(1);
        self.listed.push(format!("{path}: {why}"));
    }

    fn report(&self) {
        for l in &self.listed {
            println!("expected failure: {l}");
        }
        println!(
            "clazel-conformance: suite=\"{}\" pass={} xfail={} fail={} total={}",
            self.name,
            self.pass,
            self.xfail,
            self.fail.len(),
            self.total
        );
    }
}

fn listed(path: &str) -> Option<&'static str> {
    XFAIL.iter().find(|(p, _)| *p == path).map(|&(_, why)| why)
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn test262_regexp_literals() -> Result<(), String> {
    assert_eq!(TREE_SHA256.len(), 64);
    // The table's other frontmatter columns, for the record.
    let with = |f: fn(&Case) -> bool| TEST262.iter().filter(|c| f(c)).count();
    println!(
        "{} tests in the table: {} with includes, {} with features, {} with flags",
        TEST262.len(),
        with(|c| !c.includes.is_empty()),
        with(|c| !c.features.is_empty()),
        with(|c| !c.flags.is_empty()),
    );
    let mut in_dir = Suite::new("Test262 language/literals/regexp");
    let mut elsewhere = Suite::new("Test262 other tests' regexp literals");
    let mut problems: Vec<String> = Vec::new();
    let mut used: Vec<&str> = Vec::new();
    let mut negative_rejected = 0usize;
    for case in TEST262 {
        let negative =
            matches!(case.negative, Some((phase, _)) if phase == "parse" || phase == "early");
        let is_dir = case.path.starts_with(DIR);
        // Elsewhere, only positive tests are judged.
        if !is_dir && negative {
            continue;
        }
        let suite = if is_dir { &mut in_dir } else { &mut elsewhere };
        if let Expect::Fail(reason) = case.expect {
            if is_dir {
                suite.count();
                suite.xfail(case.path, reason);
            }
            continue;
        }
        let outcome = judge(case)?;
        if matches!(outcome, Outcome::Nothing) && !is_dir {
            continue;
        }
        suite.count();
        let entry = listed(case.path);
        if entry.is_some() {
            used.push(case.path);
        }
        match (outcome, entry) {
            (Outcome::Pass, None) => {
                suite.pass = suite.pass.saturating_add(1);
                if negative {
                    negative_rejected = negative_rejected.saturating_add(1);
                }
            }
            (Outcome::Pass, Some(_)) => {
                problems.push(format!("{} passes but is listed in XFAIL", case.path));
            }
            (Outcome::Nothing, None) => suite.xfail(case.path, NOT_SCANNED),
            (Outcome::Nothing | Outcome::Fail(_), Some(why)) => suite.xfail(case.path, why),
            (Outcome::Fail(why), None) => suite.fail.push(format!("{}: {why}", case.path)),
        }
    }
    println!("{negative_rejected} negative tests passed: a literal in each is rejected");
    in_dir.report();
    elsewhere.report();
    problems.extend(in_dir.fail.iter().cloned());
    problems.extend(elsewhere.fail.iter().cloned());
    for &(p, _) in XFAIL {
        if !used.contains(&p) {
            problems.push(format!("{p} is listed in XFAIL but is not a failure"));
        }
    }
    // Every test of the directory is in the suite.
    assert_eq!(
        TEST262.iter().filter(|c| c.path.starts_with(DIR)).count(),
        in_dir.total
    );
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}
