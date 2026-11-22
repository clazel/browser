//! The lexer over the vendored Test262 subset (`tests/data/test262/`, its
//! table `tests/generated/test262.rs`; phase-7.md item 7.1).
//!
//! The proofs show the implementation agrees with `spec.rs` (so far in part:
//! `src/exec.rs`), and `independent.rs` shows where the spec equals UAX #31
//! and ECMA-262 Annex A. This file checks the lexer, and so the spec, against
//! the outside world. It is not Test262's own conformance run: that goes
//! through the parser (phase-7.md 7.3), which chooses each token's goal
//! symbol and applies strict mode and the early errors. Without a parser the
//! goal is guessed from the previous token (as `test262.rs` does), so the
//! suites below only claim what does not depend on the guess or on the
//! parser. Each unit is one test file.
//!
//! - **"Test262 language/ positive tests lex"**: every test that is not
//!   `negative` must lex to the end with no error. Tests the table marks as
//!   expected failures (a feature newer than the edition or excluded by
//!   7.0(b)) are `xfail`, with the table's reason.
//! - **"Test262 lexical negative tests rejected"**: every `negative` test
//!   with phase `parse` under the directories whose syntax is lexical
//!   (`LEXICAL_DIRS`) must make the lexer return an error, except those in
//!   [`NEGATIVE_XFAIL`], whose error is the parser's (a strict-mode early
//!   error, or text that is valid tokens in an invalid order); each is
//!   listed there by name with the reason. A listed test that the lexer
//!   rejects fails the run, so the list cannot go stale. The negative tests
//!   of the other directories (identifiers, keywords, `statements/`,
//!   `expressions/`, regular expression patterns, modules) are not the
//!   lexer's to judge and are not counted.
//! - **"Test262 language/ every test tiles"**: from position 0 in two goal
//!   symbols, the elements the lexer returns (resuming one code point on
//!   after an error) end exactly at the end of the file, none empty and none
//!   overlapping, and `next_token` terminates (span coverage, on 5,212
//!   files).
//! - **"Test262 harness files lex"**: every `harness/**/*.js` file (valid
//!   programs, all written by Test262) lexes to the end.
//!
//! Not done: a diff against another engine's tokenization. No JavaScript
//! engine or tokenizer is vendored as a fixture, and none is an allowlisted
//! dev-dependency (docs/DEPENDENCIES.md): `unicode-ident` is on the list,
//! with class `shipped` for another purpose, and implements XID_Start and
//! XID_Continue, not the ID properties this lexer uses.

use clazel_js_lexer::api::{Element, Next, Step, Value};
use clazel_js_lexer::exec::{next_input_element, next_token};
use clazel_js_lexer::spec::{ElementKind, Goal, TemplateKind};
use std::path::{Path, PathBuf};

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

include!("generated/test262.rs");

/// The directories of `test/` whose syntax errors are lexical errors.
const LEXICAL_DIRS: &[&str] = &[
    "language/comments/",
    "language/line-terminators/",
    "language/literals/bigint/",
    "language/literals/numeric/",
    "language/literals/string/",
    "language/punctuators/",
    "language/types/string/",
    "language/white-space/",
];

const STRICT: &str = "strict mode: the lexer reads this legacy octal or non-octal decimal \
form, which is lexically valid (12.9.3, 12.9.4); rejecting it is an early error (12.9.3.1, \
12.9.4.1) of the parser, which knows the code is strict";
const ADJACENT: &str = "lexically valid: adjacent string literals, which only the parser rejects";
const AFTER_LT: &str = "the text after the line terminator is valid tokens, not a comment; \
only the parser rejects it";
const HTML: &str = "`-->` is a comment only at the start of a line (Annex B.1.1); here it is \
the tokens `--` and `>`, which only the parser rejects";
const DOT: &str = "`.` then an identifier: valid tokens, which only the parser rejects";

/// Negative tests of [`LEXICAL_DIRS`] that the lexer does not reject, and
/// why: their error is not a lexical one.
const NEGATIVE_XFAIL: &[(&str, &str)] = &[
    ("language/comments/multi-line-html-close-extra.js", HTML),
    (
        "language/comments/single-line-html-close-without-lt.js",
        HTML,
    ),
    ("language/line-terminators/S7.3_A3.2_T1.js", AFTER_LT),
    (
        "language/line-terminators/invalid-comment-single-cr.js",
        AFTER_LT,
    ),
    (
        "language/line-terminators/invalid-comment-single-lf.js",
        AFTER_LT,
    ),
    (
        "language/line-terminators/invalid-comment-single-ls.js",
        AFTER_LT,
    ),
    (
        "language/line-terminators/invalid-comment-single-ps.js",
        AFTER_LT,
    ),
    ("language/literals/numeric/7.8.3-1gs.js", STRICT),
    ("language/literals/numeric/7.8.3-2gs.js", STRICT),
    (
        "language/literals/numeric/legacy-octal-integer-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/legacy-octal-integery-000-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/legacy-octal-integery-005-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/legacy-octal-integery-01-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/legacy-octal-integery-010-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/legacy-octal-integery-06-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/legacy-octal-integery-07-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/non-octal-decimal-integer-strict.js",
        STRICT,
    ),
    (
        "language/literals/numeric/numeric-separators/numeric-separator-literal-dot-nsl-ep-err.js",
        DOT,
    ),
    (
        "language/literals/numeric/numeric-separators/numeric-separator-literal-dot-nsl-err.js",
        DOT,
    ),
    ("language/literals/string/S7.8.4_A4.3_T1.js", STRICT),
    ("language/literals/string/S7.8.4_A4.3_T2.js", STRICT),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-1-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-2-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-3-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-4-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-5-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-6-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-7-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-8-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-8-strict.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-9-strict-explicit-pragma.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-9-strict.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-non-octal-escape-sequence-strict.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-octal-escape-sequence-prologue-strict.js",
        STRICT,
    ),
    (
        "language/literals/string/legacy-octal-escape-sequence-strict.js",
        STRICT,
    ),
    ("language/types/string/S8.4_A13_T3.js", ADJACENT),
    ("language/types/string/S8.4_A14_T3.js", ADJACENT),
];

fn test_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/test262/test")
}

fn harness_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/test262/harness")
}

fn read_file(path: &Path) -> Result<Vec<u32>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(text.chars().map(u32::from).collect())
}

/// Annex B.1.1 applies to scripts, not modules.
fn html(case: &Case) -> bool {
    !case.flags.contains(&"module")
}

/// Whether every element from 0 in `goal`, resuming one code point after an
/// error, starts where the last ended and the last ends at the end: the
/// elements and the skipped code points tile the source text.
fn tiles(src: &[u32], goal: Goal, html: bool) -> bool {
    let mut pos: usize = 0;
    loop {
        match next_input_element(src, pos, goal, html) {
            Ok(Step::Eof) => return pos == src.len(),
            Ok(Step::Element(el)) => {
                if !(el.start == pos && pos < el.end && el.end <= src.len()) {
                    return false;
                }
                pos = el.end;
            }
            Err(_) => {
                if pos >= src.len() {
                    return false;
                }
                pos = pos.saturating_add(1);
            }
        }
    }
}

/// The names after which a `/` starts a regular expression.
const BEFORE_EXPRESSION: &[&str] = &[
    "return",
    "typeof",
    "instanceof",
    "in",
    "of",
    "new",
    "delete",
    "void",
    "throw",
    "case",
    "do",
    "else",
    "yield",
    "await",
    "extends",
];

/// Whether a `/` after `el` starts a regular expression, as a guess.
fn regexp_after(el: &Element, src: &[u32]) -> bool {
    let text: String = src
        .get(el.start..el.end)
        .unwrap_or(&[])
        .iter()
        .filter_map(|&c| char::from_u32(c))
        .collect();
    match el.kind {
        ElementKind::Punctuator => !matches!(text.as_str(), ")" | "]"),
        ElementKind::RightBracePunctuator
        | ElementKind::DivPunctuator
        | ElementKind::Template(TemplateKind::Head | TemplateKind::Middle) => true,
        ElementKind::IdentifierName => match &el.value {
            Value::Name {
                escaped: false,
                code_points,
            } => {
                let name: String = code_points
                    .iter()
                    .filter_map(|&c| char::from_u32(c))
                    .collect();
                BEFORE_EXPRESSION.contains(&name.as_str())
            }
            _ => false,
        },
        _ => false,
    }
}

/// Lexes `src` to the end with `next_token`, guessing each goal symbol from
/// the token before (and a stack of open braces, to know when a `}` closes a
/// template substitution). `true` if no error occurs and every token is
/// non-empty and inside the source.
fn lexes(src: &[u32], html: bool) -> bool {
    let mut pos = 0;
    let mut regexp = true;
    let mut braces: Vec<bool> = Vec::new();
    loop {
        let in_template = braces.last() == Some(&true);
        let goal = if pos == 0 {
            Goal::InputElementHashbangOrRegExp
        } else {
            match (regexp, in_template) {
                (true, true) => Goal::InputElementRegExpOrTemplateTail,
                (false, true) => Goal::InputElementTemplateTail,
                (true, false) => Goal::InputElementRegExp,
                (false, false) => Goal::InputElementDiv,
            }
        };
        match next_token(src, pos, goal, html) {
            Ok(Next::Eof { .. }) => return true,
            Ok(Next::Token(tok)) => {
                let el = &tok.element;
                if !(pos <= el.start && el.start < el.end && el.end <= src.len()) {
                    return false;
                }
                match el.kind {
                    ElementKind::Punctuator if src.get(el.start) == Some(&u32::from('{')) => {
                        braces.push(false);
                    }
                    ElementKind::Template(TemplateKind::Head) => braces.push(true),
                    ElementKind::RightBracePunctuator
                    | ElementKind::Template(TemplateKind::Tail) => {
                        braces.pop();
                    }
                    _ => {}
                }
                regexp = regexp_after(el, src);
                pos = el.end;
            }
            Err(_) => return false,
        }
    }
}

/// The `.js` files below `dir`, sorted.
fn js_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            js_files(&p, out)?;
        } else if p.extension().is_some_and(|e| e == "js") {
            out.push(p);
        }
    }
    Ok(())
}

/// One suite's tally.
#[derive(Default)]
struct Tally {
    pass: u64,
    xfail: u64,
    fail: Vec<String>,
}

fn report(name: &str, t: &Tally, total: usize) {
    println!(
        "clazel-conformance: suite=\"{name}\" pass={} xfail={} fail={} total={total}",
        t.pass,
        t.xfail,
        t.fail.len()
    );
}

fn check(name: &str, t: &Tally, total: usize) {
    report(name, t, total);
    assert_eq!(
        t.pass
            .saturating_add(t.xfail)
            .saturating_add(u64::try_from(t.fail.len()).unwrap_or(u64::MAX)),
        u64::try_from(total).unwrap_or(u64::MAX),
        "{name}: the counts do not add up"
    );
    assert!(
        t.fail.is_empty(),
        "{name}: {} unexpected failures:\n{}",
        t.fail.len(),
        t.fail.join("\n")
    );
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn positive_tests_lex() -> Result<(), String> {
    assert_eq!(TREE_SHA256.len(), 64);
    let cases: Vec<&Case> = TEST262.iter().filter(|c| c.negative.is_none()).collect();
    let mut t = Tally::default();
    let features: std::collections::BTreeSet<&str> = cases
        .iter()
        .flat_map(|c| c.features.iter().copied())
        .collect();
    let with_includes = cases.iter().filter(|c| !c.includes.is_empty()).count();
    println!(
        "{} positive tests, {} features, {with_includes} with harness includes",
        cases.len(),
        features.len()
    );
    for case in &cases {
        if let Expect::Fail(reason) = case.expect {
            assert!(!reason.is_empty());
            t.xfail += 1;
            continue;
        }
        let src = read_file(&test_root().join(case.path))?;
        if lexes(&src, html(case)) {
            t.pass += 1;
        } else {
            t.fail.push(case.path.to_owned());
        }
    }
    check("Test262 language/ positive tests lex", &t, cases.len());
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn lexical_negative_tests_rejected() -> Result<(), String> {
    let cases: Vec<&Case> = TEST262
        .iter()
        .filter(|c| {
            matches!(c.negative, Some(("parse", _)))
                && LEXICAL_DIRS.iter().any(|d| c.path.starts_with(d))
        })
        .collect();
    // Every listed expected failure is a test of the suite, once.
    for (i, (path, reason)) in NEGATIVE_XFAIL.iter().enumerate() {
        assert!(
            cases.iter().any(|c| c.path == *path),
            "{path} is not a lexical negative test"
        );
        assert!(!reason.is_empty());
        assert!(
            NEGATIVE_XFAIL.iter().take(i).all(|(p, _)| p != path),
            "{path} is listed twice"
        );
    }
    let mut t = Tally::default();
    for case in &cases {
        let listed = NEGATIVE_XFAIL.iter().any(|(p, _)| *p == case.path);
        let marked = matches!(case.expect, Expect::Fail(_));
        let src = read_file(&test_root().join(case.path))?;
        let rejected = !lexes(&src, html(case));
        match (rejected, listed || marked) {
            (true, false) => t.pass += 1,
            (false, true) => t.xfail += 1,
            (true, true) => t.fail.push(format!(
                "{}: listed as an expected failure, but rejected",
                case.path
            )),
            (false, false) => t.fail.push(format!(
                "{}: a lexical error the lexer does not report",
                case.path
            )),
        }
    }
    check("Test262 lexical negative tests rejected", &t, cases.len());
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn every_test_tiles() -> Result<(), String> {
    let mut t = Tally::default();
    for case in TEST262 {
        let src = read_file(&test_root().join(case.path))?;
        let h = html(case);
        if tiles(&src, Goal::InputElementDiv, h)
            && tiles(&src, Goal::InputElementRegExp, h)
            && tiles(&src, Goal::InputElementHashbangOrRegExp, h)
        {
            // `next_token` ends too (an error resumes where `lexes` stops).
            let _ = lexes(&src, h);
            t.pass += 1;
        } else {
            t.fail.push(case.path.to_owned());
        }
    }
    check("Test262 language/ every test tiles", &t, TEST262.len());
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn harness_files_lex() -> Result<(), String> {
    let mut files = Vec::new();
    js_files(&harness_root(), &mut files)?;
    let mut t = Tally::default();
    for path in &files {
        let src = read_file(path)?;
        if lexes(&src, true) {
            t.pass += 1;
        } else {
            t.fail.push(path.display().to_string());
        }
    }
    check("Test262 harness files lex", &t, files.len());
    Ok(())
}
