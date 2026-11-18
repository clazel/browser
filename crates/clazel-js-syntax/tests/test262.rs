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
    assert_eq!(TREE_SHA256.len(), 64);
    let mut failing = BTreeSet::new();
    let (mut total, mut neg_total, mut neg_fail, mut pos_fail) = (0, 0, 0, 0);
    let mut features = BTreeSet::new();
    let mut with_includes = 0;
    let mut reasons = BTreeSet::new();
    for case in TEST262 {
        features.extend(case.features.iter().copied());
        if !case.includes.is_empty() {
            with_includes += 1;
        }
        if let Expect::Fail(reason) = case.expect {
            reasons.insert(reason);
        }
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
        "{total} judged tests: {neg_total} negative ({neg_fail} not rejected), {} positive ({pos_fail} not accepted); \
         {} features, {with_includes} tests with includes, {} reasons for expected failures",
        total - neg_total,
        features.len(),
        reasons.len()
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
    assert!(
        newly.is_empty(),
        "{} tests newly fail:\n{}",
        newly.len(),
        newly
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        fixed.is_empty(),
        "{} listed tests now pass (remove them):\n{}",
        fixed.len(),
        fixed
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
    Ok(())
}

fn all_js(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = rd.filter_map(Result::ok).collect();
    entries.sort_by_key(|e| e.path());
    for e in entries {
        let p = e.path();
        if p.is_dir() {
            all_js(&p, out);
        } else if p.extension().is_some_and(|x| x == "js") {
            out.push(p);
        }
    }
}

/// Test262's harness is real JavaScript (about 600 KB of it): every file
/// must parse as a `Script`.
#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn test262_harness_parses() -> Result<(), String> {
    let dir = root().join("../harness");
    let mut files = Vec::new();
    all_js(&dir, &mut files);
    assert!(files.len() > 20);
    let mut bad = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).map_err(|e| e.to_string())?;
        let src: Vec<u32> = text.chars().map(u32::from).collect();
        if !accepts(&src, SourceGoal::Script) {
            bad.push(f.display().to_string());
        }
    }
    assert!(
        bad.is_empty(),
        "harness files that do not parse:\n{}",
        bad.join("\n")
    );
    Ok(())
}

/// The fixtures that are meant to be syntax errors (`break;`, `0++;`, ...):
/// the modules that tests of linking import to get an error.
const ERRONEOUS_FIXTURES: &[&str] = &[
    "language/import/import-attributes/text-javascript_FIXTURE.js",
    "language/import/import-defer/errors/syntax-error/syntax-error_FIXTURE.js",
    "language/module-code/instn-resolve-empty-export_FIXTURE.js",
    "language/module-code/instn-resolve-empty-import_FIXTURE.js",
    "language/module-code/instn-resolve-err-syntax-1_FIXTURE.js",
    "language/module-code/instn-resolve-err-syntax-2_FIXTURE.js",
    "language/module-code/instn-resolve-order-depth-reference_FIXTURE.js",
    "language/module-code/instn-resolve-order-depth-syntax_FIXTURE.js",
    "language/module-code/instn-resolve-order-src-reference_FIXTURE.js",
    "language/module-code/instn-resolve-order-src-syntax_FIXTURE.js",
];

/// The `_FIXTURE.js` files that tests import parse as a `Module` or a
/// `Script`, except those that are meant to be syntax errors.
#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn test262_fixtures_parse() -> Result<(), String> {
    let mut files = Vec::new();
    all_js(&root(), &mut files);
    let mut rejected = BTreeSet::new();
    let mut n = 0;
    for f in files
        .iter()
        .filter(|f| f.to_string_lossy().ends_with("_FIXTURE.js"))
    {
        n += 1;
        let text = std::fs::read_to_string(f).map_err(|e| e.to_string())?;
        let src: Vec<u32> = text.chars().map(u32::from).collect();
        if !accepts(&src, SourceGoal::Module) && !accepts(&src, SourceGoal::Script) {
            let rel = f.strip_prefix(root()).map_err(|e| e.to_string())?;
            rejected.insert(rel.to_string_lossy().replace('\\', "/"));
        }
    }
    assert!(n > 100);
    let expected: BTreeSet<String> = ERRONEOUS_FIXTURES.iter().map(|s| s.to_string()).collect();
    assert_eq!(rejected, expected);
    Ok(())
}
