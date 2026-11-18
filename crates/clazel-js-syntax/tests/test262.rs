//! The parser over the vendored Test262 syntax tests (`clazel-js-lexer`'s
//! `tests/data/test262/` and its generated table).
//!
//! Every test that must parse (no `negative:` of phase `parse` or `early`) is
//! parsed in each mode its flags allow, and every negative one must be
//! rejected in each. Tests that expect a failure (a feature newer than the
//! edition) are skipped. The set of tests the parser gets wrong is compared to
//! `tests/expected_failures.txt`: a test that starts failing, or one that
//! starts passing and is still listed, fails this test, so the list only
//! shrinks. Set `UPDATE_EXPECTED=1` to rewrite it.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use std::collections::BTreeSet;
use std::path::PathBuf;

/// A test's row in the generated table.
#[allow(dead_code)]
struct Case {
    path: &'static str,
    flags: &'static [&'static str],
    features: &'static [&'static str],
    includes: &'static [&'static str],
    negative: Option<(&'static str, &'static str)>,
    expect: Expect,
}

/// Whether a test is expected to pass, and if not why.
#[allow(dead_code)]
enum Expect {
    Run,
    Fail(&'static str),
}

include!("../../clazel-js-lexer/tests/generated/test262.rs");

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../clazel-js-lexer/tests/data/test262/test")
}

fn read(case: &Case) -> Result<Vec<u32>, String> {
    let path = root().join(case.path);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", case.path))?;
    Ok(text.chars().map(u32::from).collect())
}

/// Whether `src` is accepted as `goal`.
fn accepts(src: &[u32], goal: SourceGoal) -> bool {
    parse(src, goal).is_ok()
}

/// The runs of a test: its goal and whether to prefix a Use Strict Directive.
fn runs(case: &Case) -> Vec<(SourceGoal, bool)> {
    let has = |f: &str| case.flags.contains(&f);
    if has("module") {
        vec![(SourceGoal::Module, false)]
    } else if has("raw") || has("noStrict") {
        vec![(SourceGoal::Script, false)]
    } else if has("onlyStrict") {
        vec![(SourceGoal::Script, true)]
    } else {
        vec![(SourceGoal::Script, false), (SourceGoal::Script, true)]
    }
}

/// Whether the test is judged by the parser: it is not an expected failure,
/// and a negative one is of phase `parse` or `early`.
fn judged(case: &Case) -> bool {
    matches!(case.expect, Expect::Run)
        && !matches!(case.negative, Some((phase, _)) if phase != "parse" && phase != "early")
}

fn passes(case: &Case) -> Result<bool, String> {
    let src = read(case)?;
    for (goal, strict) in runs(case) {
        let mut s: Vec<u32> = Vec::new();
        if strict {
            s.extend("\"use strict\";\n".chars().map(u32::from));
        }
        s.extend(src.iter().copied());
        let ok = accepts(&s, goal);
        if ok == case.negative.is_some() {
            return Ok(false);
        }
    }
    Ok(true)
}

fn expected_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/expected_failures.txt")
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn test262_parse_and_early_errors() -> Result<(), String> {
    let mut failing = BTreeSet::new();
    let (mut total, mut neg_total, mut neg_fail, mut pos_fail) = (0, 0, 0, 0);
    for case in TEST262 {
        if !judged(case) {
            continue;
        }
        total += 1;
        if case.negative.is_some() {
            neg_total += 1;
        }
        if !passes(case)? {
            if case.negative.is_some() {
                neg_fail += 1;
            } else {
                pos_fail += 1;
                if std::env::var("SHOW_POSITIVE").is_ok() {
                    println!("POSITIVE-FAIL {}", case.path);
                }
            }
            failing.insert(case.path.to_string());
        }
    }
    println!(
        "{total} judged tests: {neg_total} negative ({neg_fail} not rejected), {} positive ({pos_fail} not accepted)",
        total - neg_total
    );
    let listing: String = failing.iter().map(|p| format!("{p}\n")).collect();
    if std::env::var("UPDATE_EXPECTED").is_ok() {
        std::fs::write(expected_path(), &listing).map_err(|e| e.to_string())?;
        return Ok(());
    }
    let expected: BTreeSet<String> = std::fs::read_to_string(expected_path())
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect();
    let newly: Vec<_> = failing.difference(&expected).collect();
    let fixed: Vec<_> = expected.difference(&failing).collect();
    assert!(newly.is_empty(), "{} tests newly fail:\n{}", newly.len(), newly.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"));
    assert!(fixed.is_empty(), "{} listed tests now pass (remove them):\n{}", fixed.len(), fixed.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"));
    Ok(())
}
