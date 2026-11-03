//! Conformance pass rates for the status table (Phase 1 item 1.12).
//!
//! Every `tests/conformance*.rs` reports each vendored suite it runs with one
//! summary line on stdout. This is the only definition of the format:
//!
//! ```text
//! clazel-conformance: suite="WPT encoding/ UTF-8 decode" pass=57 xfail=0 fail=0 total=57
//! ```
//!
//! - The line starts with `clazel-conformance: ` and has exactly these five
//!   fields, in this order, separated by single spaces.
//! - `suite` names the suite: printable ASCII without `"`, `|`, `<` or `>`,
//!   unique within the crate. It is what the table shows.
//! - `pass`, `xfail` and `fail` count the units of the suite (cases, or the
//!   checks they contain, as the test's doc comment says) that pass, that
//!   are expected failures (listed in the test with a reason), and that fail
//!   unexpectedly. `total` is the size of the suite, counted independently
//!   (usually the length of the generated table), and must equal
//!   `pass + xfail + fail`. Expected failures never count as passes.
//!
//! Print the line *before* asserting, so a failing run still reports. A
//! test reports a suite like this:
//!
//! ```text
//! println!(
//!     "clazel-conformance: suite=\"WPT …\" pass={pass} xfail={xfail} fail={} total={}",
//!     failed, WPT.len()
//! );
//! ```
//!
//! `cargo xtask verify` and `cargo xtask report` run each conformance test
//! target on its own with `--show-output`, read these lines and fail if a
//! target prints none, if a line is malformed, or if any suite has `fail`
//! above zero. The numbers go into the status table's "Conformance" column
//! (docs/STATUS.md), and `verify` reports when the committed table differs
//! from the run.

use std::path::PathBuf;
use std::process::Command;

use crate::workspace::{self, Crate};

/// Start of every summary line.
pub const PREFIX: &str = "clazel-conformance: ";

/// One suite's result, as printed by a conformance test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Suite {
    pub name: String,
    pub pass: u64,
    pub xfail: u64,
    pub fail: u64,
    pub total: u64,
}

/// Parse one summary line (with its prefix). Errors say what is wrong.
pub fn parse_line(line: &str) -> Result<Suite, String> {
    let rest = line
        .strip_prefix(PREFIX)
        .ok_or_else(|| format!("does not start with {PREFIX:?}"))?;
    let rest = rest
        .strip_prefix("suite=\"")
        .ok_or("expected suite=\"…\" first")?;
    let (name, rest) = rest.split_once('"').ok_or("unterminated suite name")?;
    if name.is_empty()
        || !name
            .bytes()
            .all(|b| (b' '..=b'~').contains(&b) && !b"|<>".contains(&b))
    {
        return Err(format!("bad suite name {name:?}"));
    }
    let fields: Vec<&str> = rest.split(' ').collect();
    let mut numbers = [0u64; 4];
    match fields.as_slice() {
        ["", a, b, c, d] => {
            for ((slot, field), key) in numbers
                .iter_mut()
                .zip([a, b, c, d])
                .zip(["pass", "xfail", "fail", "total"])
            {
                let value = field
                    .strip_prefix(key)
                    .and_then(|v| v.strip_prefix('='))
                    .ok_or_else(|| format!("expected {key}=N, found {field:?}"))?;
                if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(format!("{key}: not a number: {value:?}"));
                }
                *slot = value
                    .parse()
                    .map_err(|e| format!("{key}: {value:?}: {e}"))?;
            }
        }
        _ => return Err("expected exactly pass=N xfail=N fail=N total=N".into()),
    }
    let [pass, xfail, fail, total] = numbers;
    let sum = pass
        .checked_add(xfail)
        .and_then(|s| s.checked_add(fail))
        .ok_or("counts overflow")?;
    if sum != total {
        return Err(format!("pass + xfail + fail = {sum}, but total = {total}"));
    }
    Ok(Suite {
        name: name.to_owned(),
        pass,
        xfail,
        fail,
        total,
    })
}

/// Every summary line in `output`, in order. A line that starts with the
/// prefix but does not parse is an error.
pub fn parse_output(output: &str) -> Result<Vec<Suite>, String> {
    output
        .lines()
        .filter(|l| l.starts_with(PREFIX))
        .map(|l| parse_line(l).map_err(|e| format!("{l:?}: {e}")))
        .collect()
}

/// The conformance test files of a crate (`tests/conformance*.rs`), sorted.
pub fn test_files(c: &Crate) -> Result<Vec<PathBuf>, String> {
    let tests = c.dir.join("tests");
    let mut files: Vec<PathBuf> = workspace::rust_files(&c.dir)?
        .into_iter()
        .filter(|p| p.parent() == Some(tests.as_path()))
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("conformance"))
        })
        .collect();
    files.sort();
    Ok(files)
}

/// Run one crate's conformance tests and collect their summaries, sorted
/// by suite name. Ok(empty) if the crate has none.
pub fn run(c: &Crate) -> Result<Vec<Suite>, Vec<String>> {
    let files = test_files(c).map_err(|e| vec![e])?;
    let mut suites: Vec<Suite> = Vec::new();
    let mut problems = Vec::new();
    for file in &files {
        let shown = workspace::relative(file);
        let Some(target) = file.file_stem().and_then(|s| s.to_str()) else {
            problems.push(format!("{shown}: file name is not UTF-8"));
            continue;
        };
        match run_target(&c.name, target) {
            Ok(found) if found.is_empty() => problems.push(format!(
                "{shown}: printed no `{}` summary line (format: xtask/src/conformance.rs)",
                PREFIX.trim_end()
            )),
            Ok(found) => {
                for s in found {
                    if s.fail > 0 {
                        problems.push(format!(
                            "{shown}: {}: {} unexpected failures",
                            s.name, s.fail
                        ));
                    }
                    if suites.iter().any(|t| t.name == s.name) {
                        problems.push(format!("{shown}: suite {:?} reported twice", s.name));
                    }
                    suites.push(s);
                }
            }
            Err(e) => problems.push(format!("{shown}: {e}")),
        }
    }
    if !problems.is_empty() {
        return Err(problems);
    }
    suites.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(suites)
}

fn run_target(package: &str, target: &str) -> Result<Vec<Suite>, String> {
    let out = Command::new("cargo")
        .args([
            "test", "--locked", "--quiet", "-p", package, "--test", target,
        ])
        .args(["--", "--show-output"])
        .output()
        .map_err(|e| format!("cannot run cargo test: {e}"))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    if !out.status.success() {
        return Err(format!("cargo test failed:\n{text}"));
    }
    parse_output(&text)
}

/// The table cell for one crate's suites.
pub fn cell(suites: &[Suite]) -> String {
    if suites.is_empty() {
        return "none".to_owned();
    }
    suites
        .iter()
        .map(|s| {
            let mut c = format!("{}: {} / {}", s.name, s.pass, s.total);
            if s.xfail > 0 {
                c.push_str(&format!(" ({} expected failures)", s.xfail));
            }
            if s.fail > 0 {
                c.push_str(&format!(" ({} failing)", s.fail));
            }
            c
        })
        .collect::<Vec<_>>()
        .join("<br>")
}

#[cfg(test)]
mod tests {
    use super::{Suite, cell, parse_line, parse_output};

    #[test]
    fn parses_the_documented_example() {
        let s = parse_line(
            "clazel-conformance: suite=\"WPT encoding/ UTF-8 decode\" pass=57 xfail=0 fail=0 total=57",
        );
        assert_eq!(
            s,
            Ok(Suite {
                name: "WPT encoding/ UTF-8 decode".into(),
                pass: 57,
                xfail: 0,
                fail: 0,
                total: 57,
            })
        );
    }

    #[test]
    fn rejects_bad_lines() {
        for bad in [
            "clazel-conformance: suite=\"a\" pass=1 xfail=0 fail=0 total=2",
            "clazel-conformance: suite=\"a\" pass=1 fail=0 xfail=0 total=1",
            "clazel-conformance: suite=\"a\" pass=1 xfail=0 fail=0",
            "clazel-conformance: suite=\"a\" pass=1 xfail=0 fail=0 total=1 extra=1",
            "clazel-conformance: suite=\"a\" pass=-1 xfail=0 fail=0 total=1",
            "clazel-conformance: suite=\"a|b\" pass=1 xfail=0 fail=0 total=1",
            "clazel-conformance: suite=\"\" pass=1 xfail=0 fail=0 total=1",
            "clazel-conformance: suite=a pass=1 xfail=0 fail=0 total=1",
        ] {
            assert!(parse_line(bad).is_err(), "accepted {bad:?}");
        }
        assert!(parse_output("noise\nclazel-conformance: garbage\n").is_err());
    }

    #[test]
    fn expected_failures_are_not_passes() {
        let s = Suite {
            name: "x".into(),
            pass: 23,
            xfail: 9,
            fail: 0,
            total: 32,
        };
        assert_eq!(cell(&[s]), "x: 23 / 32 (9 expected failures)");
        assert_eq!(cell(&[]), "none");
    }
}
