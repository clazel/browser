//! Vendored conformance suites as Rust tables (Phase 1 item 1.0).
//!
//! Browser crates may not ship a parser for test-data formats (CLAUDE.md
//! rule 8), so tests never read JSON or JavaScript at run time. Each suite
//! vendored under a crate's `tests/data/<suite>/` is converted here into
//! `tests/generated/<suite>.rs`, a plain Rust table that is committed.
//! `cargo xtask testdata` writes the tables; `check` and `verify` fail if a
//! committed table differs from what the converter produces, so the tables
//! can never drift from the vendored files.
//!
//! Every suite directory holds a `SOURCE.md` with `Upstream:`, `Commit:`
//! (a full 40-hex commit) and `License:` lines.

mod cbor_appendix_a;
mod html5lib_tree;
mod http_state_dates;
mod http_state_parser;
mod js;
mod llhttp;
mod wpt_base64;
mod wpt_cookies;
mod wpt_encoding;
mod wpt_idna;
mod wpt_mime_types;
mod wpt_mimesniff;
mod wpt_url_hosts;
mod wpt_url_percent;
mod wpt_url_setters;
mod wpt_urltestdata;
mod wpt_webstorage;
mod wycheproof_rsa;
mod x509_limbo;

use std::path::{Path, PathBuf};

use crate::workspace::{self, Crate};

/// A converter: suite directory to the generated file's contents.
type Convert = fn(&Path) -> Result<String, String>;

/// Every suite the converter knows, by directory name, with the files it
/// expects to find there.
const CONVERTERS: &[(&str, Convert, &[&str])] = &[
    (
        "cbor-appendix-a",
        cbor_appendix_a::convert,
        cbor_appendix_a::FILES,
    ),
    (
        "html5lib-tree-construction",
        html5lib_tree::convert,
        html5lib_tree::FILES,
    ),
    (
        "http-state-dates",
        http_state_dates::convert,
        http_state_dates::FILES,
    ),
    (
        "http-state-parser",
        http_state_parser::convert,
        http_state_parser::FILES,
    ),
    ("llhttp", llhttp::convert, llhttp::FILES),
    ("wpt-base64", wpt_base64::convert, wpt_base64::FILES),
    ("wpt-cookies", wpt_cookies::convert, wpt_cookies::FILES),
    ("wpt-encoding", wpt_encoding::convert, wpt_encoding::FILES),
    ("wpt-url-idna", wpt_idna::convert, wpt_idna::FILES),
    (
        "wpt-mime-types",
        wpt_mime_types::convert,
        wpt_mime_types::FILES,
    ),
    (
        "wpt-mimesniff",
        wpt_mimesniff::convert,
        wpt_mimesniff::FILES,
    ),
    (
        "wpt-url-hosts",
        wpt_url_hosts::convert,
        wpt_url_hosts::FILES,
    ),
    (
        "wpt-url-percent-encoding",
        wpt_url_percent::convert,
        wpt_url_percent::FILES,
    ),
    (
        "wpt-url-setters",
        wpt_url_setters::convert,
        wpt_url_setters::FILES,
    ),
    (
        "wpt-webstorage",
        wpt_webstorage::convert,
        wpt_webstorage::FILES,
    ),
    (
        "wpt-urltestdata",
        wpt_urltestdata::convert,
        wpt_urltestdata::FILES,
    ),
    (
        "wycheproof-rsa-pkcs1",
        wycheproof_rsa::convert,
        wycheproof_rsa::FILES,
    ),
    ("x509-limbo", x509_limbo::convert, x509_limbo::FILES),
];

/// A converter for a binary artefact written beside a suite's Rust table.
type ConvertBytes = fn(&Path) -> Result<Vec<u8>, String>;

/// Binary artefacts, by suite directory name: the file name under
/// `tests/generated/` and its converter. They are checked exactly like the
/// Rust tables (stale or missing is a problem; orphans are rejected).
const EXTRA_OUTPUTS: &[(&str, &str, ConvertBytes)] = &[(
    "x509-limbo",
    x509_limbo::CERTS_BIN,
    x509_limbo::convert_certs,
)];

/// Files every suite directory has besides the converter's inputs.
const ALWAYS: &[&str] = &["SOURCE.md", "LICENSE.md"];

struct Suite {
    dir: PathBuf,
    generated: PathBuf,
    convert: Convert,
    files: &'static [&'static str],
}

/// The suites vendored in `c`, plus problems found while listing them.
fn suites(c: &Crate) -> Result<Vec<Suite>, String> {
    let data = c.dir.join("tests").join("data");
    if !data.is_dir() {
        return Ok(Vec::new());
    }
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&data).map_err(|e| format!("{}: {e}", data.display()))? {
        let dir = entry
            .map_err(|e| format!("{}: {e}", data.display()))?
            .path();
        let name = dir
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or_default()
            .to_owned();
        if !dir.is_dir() {
            return Err(format!(
                "{}: only suite directories belong in tests/data/",
                workspace::relative(&dir)
            ));
        }
        let Some((_, convert, files)) = CONVERTERS.iter().find(|(n, _, _)| *n == name) else {
            return Err(format!(
                "{}: no converter for suite {name:?} in xtask/src/testdata.rs",
                workspace::relative(&dir)
            ));
        };
        out.push(Suite {
            generated: c
                .dir
                .join("tests")
                .join("generated")
                .join(format!("{}.rs", name.replace('-', "_"))),
            dir,
            convert: *convert,
            files,
        });
    }
    out.sort_by(|a, b| a.dir.cmp(&b.dir));
    Ok(out)
}

/// Check `SOURCE.md` and that the directory holds exactly the expected files.
fn check_suite_dir(s: &Suite) -> Vec<String> {
    let mut problems = Vec::new();
    let rel = workspace::relative(&s.dir);
    let source = s.dir.join("SOURCE.md");
    match std::fs::read_to_string(&source) {
        Ok(text) => problems.extend(
            source_problems(&text)
                .into_iter()
                .map(|p| format!("{rel}/SOURCE.md: {p}")),
        ),
        Err(e) => problems.push(format!("{rel}/SOURCE.md: {e}")),
    }
    let expected: Vec<&str> = s.files.iter().chain(ALWAYS).copied().collect();
    match std::fs::read_dir(&s.dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !expected.contains(&name.as_str()) {
                    problems.push(format!(
                        "{rel}/{name}: not an input of the converter; remove it or convert it"
                    ));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

/// What is missing from a `SOURCE.md`.
fn source_problems(text: &str) -> Vec<String> {
    let field = |key: &str| {
        text.lines()
            .find_map(|l| l.trim().strip_prefix(key).map(str::trim))
            .filter(|v| !v.is_empty())
    };
    let mut problems = Vec::new();
    if !field("Upstream:").is_some_and(|u| u.starts_with("https://")) {
        problems.push("no \"Upstream: https://...\" line".to_owned());
    }
    if !field("Commit:")
        .is_some_and(|c| c.len() == 40 && c.chars().all(|ch| ch.is_ascii_hexdigit()))
    {
        problems.push("no \"Commit:\" line with a full 40-hex commit".to_owned());
    }
    if field("License:").is_none() {
        problems.push("no \"License:\" line".to_owned());
    }
    problems
}

/// Generated files with no suite behind them.
fn orphans(c: &Crate, suites: &[Suite]) -> Vec<String> {
    let dir = c.dir.join("tests").join("generated");
    let Ok(entries) = std::fs::read_dir(&dir) else {
        return Vec::new();
    };
    entries
        .flatten()
        .map(|e| e.path())
        .filter(|p| !suites.iter().any(|s| &s.generated == p))
        .filter(|p| {
            !EXTRA_OUTPUTS.iter().any(|(suite, file, _)| {
                suites
                    .iter()
                    .any(|s| s.dir.file_name().is_some_and(|n| n == *suite) && dir.join(file) == *p)
            })
        })
        .map(|p| {
            format!(
                "{}: generated file with no suite in tests/data/",
                workspace::relative(&p)
            )
        })
        .collect()
}

/// Compare (or, with `write`, rewrite) every generated table. Returns
/// (problems, notes).
pub fn run(crates: &[Crate], write: bool) -> (Vec<String>, Vec<String>) {
    let mut problems = Vec::new();
    let mut notes = Vec::new();
    for c in crates {
        let suites = match suites(c) {
            Ok(s) => s,
            Err(e) => {
                problems.push(e);
                continue;
            }
        };
        problems.extend(orphans(c, &suites));
        for s in &suites {
            problems.extend(check_suite_dir(s));
            let rel = workspace::relative(&s.generated);
            let fresh = match (s.convert)(&s.dir) {
                Ok(f) => f,
                Err(e) => {
                    problems.push(format!("{}: {e}", workspace::relative(&s.dir)));
                    continue;
                }
            };
            let cases = fresh
                .lines()
                .filter(|l| l.trim_start().starts_with("Case {"))
                .count();
            let current = std::fs::read_to_string(&s.generated).ok();
            if current.as_deref() == Some(fresh.as_str()) {
                notes.push(format!("{rel}: up to date ({cases} cases)"));
            } else if write {
                let res = s
                    .generated
                    .parent()
                    .map_or(Ok(()), std::fs::create_dir_all)
                    .and_then(|()| std::fs::write(&s.generated, &fresh));
                match res {
                    Ok(()) => notes.push(format!("{rel}: written ({cases} cases)")),
                    Err(e) => problems.push(format!("{rel}: {e}")),
                }
            } else if current.is_none() {
                problems.push(format!("{rel}: missing; run `cargo xtask testdata`"));
            } else {
                problems.push(format!(
                    "{rel}: stale (differs from what the converter produces); \
                     run `cargo xtask testdata` and commit the result"
                ));
            }
            for (_, file, convert) in EXTRA_OUTPUTS
                .iter()
                .filter(|(suite, _, _)| s.dir.file_name().is_some_and(|n| n == *suite))
            {
                let path = s.generated.with_file_name(file);
                let rel = workspace::relative(&path);
                let fresh = match convert(&s.dir) {
                    Ok(f) => f,
                    Err(e) => {
                        problems.push(format!("{}: {e}", workspace::relative(&s.dir)));
                        continue;
                    }
                };
                let current = std::fs::read(&path).ok();
                if current.as_deref() == Some(fresh.as_slice()) {
                    notes.push(format!("{rel}: up to date ({} bytes)", fresh.len()));
                } else if write {
                    match std::fs::write(&path, &fresh) {
                        Ok(()) => notes.push(format!("{rel}: written ({} bytes)", fresh.len())),
                        Err(e) => problems.push(format!("{rel}: {e}")),
                    }
                } else if current.is_none() {
                    problems.push(format!("{rel}: missing; run `cargo xtask testdata`"));
                } else {
                    problems.push(format!(
                        "{rel}: stale (differs from what the converter produces); \
                         run `cargo xtask testdata` and commit the result"
                    ));
                }
            }
        }
    }
    (problems, notes)
}

#[cfg(test)]
mod tests {
    use super::source_problems;

    #[test]
    fn source_md_fields() {
        let good = "Upstream: https://github.com/web-platform-tests/wpt\n\
                    Commit: 4ad507b28db0a636f528def9161d109fe11b93a3\n\
                    License: BSD-3-Clause\n";
        assert!(source_problems(good).is_empty());
        assert_eq!(source_problems("").len(), 3);
        let short = good.replace("4ad507b28db0a636f528def9161d109fe11b93a3", "4ad507b");
        assert_eq!(source_problems(&short).len(), 1);
    }
}
