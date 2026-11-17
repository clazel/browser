//! The lexer over the vendored Test262 subset (`tests/data/test262/`, its
//! table `tests/generated/test262.rs`).
//!
//! This is not yet Test262's conformance run: that goes through the parser
//! (phase-7.md 7.3), which chooses each token's goal symbol. Without a
//! parser the goal is guessed from the previous token (below), so these
//! tests check what does not depend on the guess:
//!
//! - **Totality and span coverage**, on every file: from every position the
//!   lexer reaches, `next_input_element` returns, and the elements tile the
//!   file (after an error it resumes one code point on).
//! - **No spurious error**: every test that must parse (no `negative:`, not
//!   an expected failure) lexes to the end with the guessed goals. (Were
//!   the guess wrong for one, a parser's goal would differ; none is.)

use clazel_js_lexer::api::{Element, Next, Step, Value};
use clazel_js_lexer::exec::{next_input_element, next_token};
use clazel_js_lexer::spec::{ElementKind, Goal, TemplateKind};
use std::collections::BTreeSet;
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

include!("generated/test262.rs");

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data/test262/test")
}

fn read(case: &Case) -> Result<Vec<u32>, String> {
    let path = root().join(case.path);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", case.path))?;
    Ok(text.chars().map(u32::from).collect())
}

/// Annex B.1.1 applies to scripts, not modules.
fn html(case: &Case) -> bool {
    !case.flags.contains(&"module")
}

/// Every element from 0 in `goal`, resuming one code point after an error:
/// the elements and the skipped code points tile the source text.
fn tile(src: &[u32], goal: Goal, html: bool) {
    let mut pos: usize = 0;
    loop {
        match next_input_element(src, pos, goal, html) {
            Ok(Step::Eof) => {
                assert_eq!(pos, src.len());
                return;
            }
            Ok(Step::Element(el)) => {
                assert!(el.start == pos && pos < el.end && el.end <= src.len());
                pos = el.end;
            }
            Err(_) => {
                assert!(pos < src.len());
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
/// the token before (and a stack of open braces, to know when a `}` closes
/// a template substitution). Returns the error's position, if any.
fn lex_tokens(src: &[u32], html: bool) -> Result<(), usize> {
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
            Ok(Next::Eof { .. }) => return Ok(()),
            Ok(Next::Token(tok)) => {
                let el = &tok.element;
                assert!(pos <= el.start && el.start < el.end && el.end <= src.len());
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
            Err(_) => {
                // The position of the token that failed: after its trivia.
                let mut p = pos;
                while let Ok(Step::Element(el)) = next_input_element(src, p, goal, html) {
                    p = el.end;
                }
                return Err(p);
            }
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn test262_lexes_total_and_tiled() -> Result<(), String> {
    assert_eq!(TREE_SHA256.len(), 64);
    let mut spurious = Vec::new();
    let mut rejected_negative = 0;
    let mut negative = 0;
    let mut features = BTreeSet::new();
    let mut with_includes = 0;
    let mut expected_failures = 0;
    let mut reasons = BTreeSet::new();
    for case in TEST262 {
        let src = read(case)?;
        let html = html(case);
        features.extend(case.features.iter().copied());
        if !case.includes.is_empty() {
            with_includes += 1;
        }
        for goal in [Goal::InputElementDiv, Goal::InputElementRegExp] {
            tile(&src, goal, html);
        }
        let result = lex_tokens(&src, html);
        if let Expect::Fail(reason) = case.expect {
            reasons.insert(reason);
        }
        match (case.negative, &case.expect) {
            (Some(_), _) => {
                negative += 1;
                if result.is_err() {
                    rejected_negative += 1;
                }
            }
            (None, Expect::Run) => {
                if let Err(at) = result {
                    spurious.push(format!("{} at {at}", case.path));
                }
            }
            (None, Expect::Fail(_)) => expected_failures += 1,
        }
    }
    println!(
        "{} tests ({} features, {with_includes} with includes); {negative} negative, \
         {rejected_negative} of them rejected by the lexer; {expected_failures} positive \
         expected failures skipped; {} reasons for expected failures",
        TEST262.len(),
        features.len(),
        reasons.len()
    );
    assert!(
        spurious.is_empty(),
        "{} tests that must parse do not lex:\n{}",
        spurious.len(),
        spurious.join("\n")
    );
    Ok(())
}
