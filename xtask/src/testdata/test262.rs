//! Test262 (`tc39/test262`): every test's frontmatter as a table, with the
//! tests outside the language scope of phase-7.md 7.0(b) marked as expected
//! failures and the reason.
//!
//! The suite is a tree: `harness/` (the files a test `includes`), `test/` (one
//! `.js` file per test, grouped in directories, plus `*_FIXTURE.js` modules
//! that other tests import and that are not tests) and `features.txt` (the
//! list of every `features` tag, which this converter uses to reject a tag it
//! has not classified). Only the frontmatter is read here, by the small
//! reader below; the test body is never parsed (rule 8: the engine's own
//! lexer and parser will run it).
//!
//! Frontmatter is a YAML comment, `/*---` to `---*/`. The reader accepts the
//! shapes Test262's own `INTERPRETING.md` lists, and nothing else, so a
//! changed upstream file fails the conversion instead of being half read:
//!
//! - scalars (`esid: ...`, `author: ...`, one-line `description: ...`);
//! - block scalars (`info: |`, `description: >`), skipped;
//! - flow lists (`flags: [a, b]`, possibly over several lines);
//! - block lists (`features:` then `  - a` lines);
//! - `negative:` with an indented `phase:` and `type:`.
//!
//! The keys read are `flags`, `features`, `includes` and `negative`; the other
//! documented keys are skipped, and an undocumented one is an error.
//!
//! **Which tests are expected failures.** A test is when
//!
//! - one of its `features` tags is excluded by 7.0(b): `SharedArrayBuffer`,
//!   `Atomics` and its parts (no threads, and no cross-origin isolation),
//!   `Temporal`, `canonical-tz` (time zones), or anything of ECMA-402
//!   (`Intl`, an `Intl.*` tag or `intl-*`); or
//! - one of its tags names a feature newer than the edition pinned in
//!   `SPEC-PIN.md` (the stage 3 proposals Test262 already has tests for), listed in
//!   [`BEYOND_EDITION`]; or
//! - it `includes` a helper that needs `$262.agent`, which needs threads.
//!
//! Every tag must also be in the vendored `features.txt`, or the conversion
//! fails: a new tag is a new decision about scope. The tags in
//! [`BEYOND_EDITION`] were each checked against the pinned edition's text: none
//! of its algorithms or names appear in it.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

/// The top-level entries vendored for this suite (besides LICENSE.md and
/// SOURCE.md): directories are read recursively.
pub const FILES: &[&str] = &["features.txt", "harness", "test"];

/// Tags of features in Test262 that the pinned edition (ECMA-262 2026) does
/// not have: stage 3 proposals and stage 2.7 ones with tests. Checked against
/// the edition's source: `regexp-duplicate-named-groups` is not here because
/// the edition has it, though `features.txt` still lists it as proposed.
const BEYOND_EDITION: &[&str] = &[
    "ShadowRealm",
    "decorators",
    "explicit-resource-management",
    "source-phase-imports",
    "source-phase-imports-module-source",
    "import-defer",
    "import-text",
    "import-bytes",
    "immutable-arraybuffer",
    "nonextensible-applies-to-private",
    "joint-iteration",
    "await-dictionary",
    "legacy-regexp",
];

/// Tags excluded by 7.0(b), with the reason, matched by [`excluded`].
const EXCLUDED_REASON_THREADS: &str =
    "excluded by 7.0(b): no threads and no cross-origin isolation (SharedArrayBuffer, Atomics)";
const EXCLUDED_REASON_TEMPORAL: &str = "excluded by 7.0(b): Temporal";
const EXCLUDED_REASON_TZ: &str =
    "excluded by 7.0(b): time zones need tzdb data read by our own parser";
const EXCLUDED_REASON_INTL: &str = "excluded by 7.0(b): ECMA-402 (Intl)";
const EXCLUDED_REASON_NEWER: &str = "newer than the pinned edition (ECMA-262 2026)";
const EXCLUDED_REASON_AGENT: &str =
    "excluded by 7.0(b) and 7.0(e): $262.agent needs threads (helper included)";

/// Includes that need `$262.agent`.
const AGENT_HELPERS: &[&str] = &["atomicsHelper.js"];

/// The documented frontmatter keys this reader skips.
const SKIPPED_KEYS: &[&str] = &[
    "description",
    "info",
    "esid",
    "es5id",
    "es6id",
    "author",
    "locale",
    "timeout",
];

/// The flags INTERPRETING.md lists.
const FLAGS: &[&str] = &[
    "onlyStrict",
    "noStrict",
    "module",
    "raw",
    "async",
    "generated",
    "CanBlockIsFalse",
    "CanBlockIsTrue",
    "non-deterministic",
];

/// Why a feature tag is out of scope, if it is.
fn excluded(tag: &str) -> Option<&'static str> {
    match tag {
        "SharedArrayBuffer" | "Atomics" | "Atomics.waitAsync" | "Atomics.pause" => {
            Some(EXCLUDED_REASON_THREADS)
        }
        "Temporal" => Some(EXCLUDED_REASON_TEMPORAL),
        "canonical-tz" => Some(EXCLUDED_REASON_TZ),
        t if t.starts_with("Intl") || t.starts_with("intl-") => Some(EXCLUDED_REASON_INTL),
        t if BEYOND_EDITION.contains(&t) => Some(EXCLUDED_REASON_NEWER),
        _ => None,
    }
}

/// What the frontmatter says that the table keeps.
#[derive(Debug, Default, PartialEq, Eq)]
struct Meta {
    flags: Vec<String>,
    features: Vec<String>,
    includes: Vec<String>,
    /// `(phase, type)` of `negative:`.
    negative: Option<(String, String)>,
}

/// The text between `/*---` and `---*/`.
fn frontmatter(text: &str) -> Result<&str, String> {
    let start = text.find("/*---").ok_or("no /*--- frontmatter")?;
    let body = text
        .get(start.saturating_add(5)..)
        .ok_or("bad frontmatter")?;
    let end = body.find("---*/").ok_or("frontmatter is not closed")?;
    body.get(..end).ok_or_else(|| "bad frontmatter".to_owned())
}

fn indented(line: &str) -> bool {
    line.starts_with(' ') || line.starts_with('\t')
}

/// Unquote one list item.
fn item(raw: &str) -> String {
    let t = raw.trim();
    let quoted = t.len() >= 2
        && ((t.starts_with('"') && t.ends_with('"')) || (t.starts_with('\'') && t.ends_with('\'')));
    if quoted {
        t.get(1..t.len().saturating_sub(1)).unwrap_or(t).to_owned()
    } else {
        t.to_owned()
    }
}

/// Read the keys the table keeps from a frontmatter.
fn parse_meta(front: &str) -> Result<Meta, String> {
    let lines: Vec<&str> = front.lines().collect();
    let mut meta = Meta::default();
    let mut i = 0usize;
    while let Some(&line) = lines.get(i) {
        i = i.saturating_add(1);
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        if indented(line) {
            // A continuation of a plain or block scalar of a skipped key.
            continue;
        }
        let (key, value) = line
            .split_once(':')
            .ok_or_else(|| format!("not a `key: value` line: {line:?}"))?;
        let value = value.trim();
        match key {
            "flags" | "features" | "includes" => {
                let mut items: Vec<String> = Vec::new();
                if let Some(rest) = value.strip_prefix('[') {
                    // A flow list, perhaps over several lines.
                    let mut acc = rest.to_owned();
                    while !acc.contains(']') {
                        let next = lines
                            .get(i)
                            .ok_or_else(|| format!("{key}: unterminated list"))?;
                        i = i.saturating_add(1);
                        acc.push(' ');
                        acc.push_str(next.trim());
                    }
                    let (list, after) = acc
                        .split_once(']')
                        .ok_or_else(|| format!("{key}: unterminated list"))?;
                    if !after.trim().is_empty() {
                        return Err(format!("{key}: text after the list: {after:?}"));
                    }
                    items.extend(list.split(',').map(item).filter(|s| !s.is_empty()));
                } else if value.is_empty() {
                    // A block list.
                    while let Some(&next) = lines.get(i) {
                        let t = next.trim();
                        if t.is_empty() {
                            i = i.saturating_add(1);
                            continue;
                        }
                        let Some(rest) = t.strip_prefix("- ") else {
                            break;
                        };
                        items.push(item(rest));
                        i = i.saturating_add(1);
                    }
                } else {
                    return Err(format!("{key}: expected a list, found {value:?}"));
                }
                let slot = match key {
                    "flags" => &mut meta.flags,
                    "features" => &mut meta.features,
                    _ => &mut meta.includes,
                };
                if !slot.is_empty() {
                    return Err(format!("{key} given twice"));
                }
                *slot = items;
            }
            "negative" => {
                if !value.is_empty() {
                    return Err(format!("negative: expected a block, found {value:?}"));
                }
                let mut phase: Option<String> = None;
                let mut kind: Option<String> = None;
                while let Some(&next) = lines.get(i) {
                    if next.trim().is_empty() {
                        i = i.saturating_add(1);
                        continue;
                    }
                    if !indented(next) {
                        break;
                    }
                    i = i.saturating_add(1);
                    let (k, v) = next
                        .trim()
                        .split_once(':')
                        .ok_or_else(|| format!("negative: bad line {next:?}"))?;
                    match k {
                        "phase" => phase = Some(v.trim().to_owned()),
                        "type" => kind = Some(v.trim().to_owned()),
                        other => return Err(format!("negative: unknown key {other:?}")),
                    }
                }
                let (Some(phase), Some(kind)) = (phase, kind) else {
                    return Err("negative: needs a phase and a type".to_owned());
                };
                if !["parse", "early", "resolution", "runtime"].contains(&phase.as_str()) {
                    return Err(format!("negative: unknown phase {phase:?}"));
                }
                if meta.negative.is_some() {
                    return Err("negative given twice".to_owned());
                }
                meta.negative = Some((phase, kind));
            }
            k if SKIPPED_KEYS.contains(&k) => {}
            other => return Err(format!("undocumented frontmatter key {other:?}")),
        }
    }
    for f in &meta.flags {
        if !FLAGS.contains(&f.as_str()) {
            return Err(format!("unknown flag {f:?}"));
        }
    }
    Ok(meta)
}

/// Every `.js` under `dir`, as (path relative to `root` with `/`, file),
/// sorted by path.
fn walk(root: &Path, dir: &Path, out: &mut Vec<(String, PathBuf)>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let path = entry.map_err(|e| format!("{}: {e}", dir.display()))?.path();
        if path.is_dir() {
            walk(root, &path, out)?;
        } else if path.extension().is_some_and(|e| e == "js") {
            let rel = path
                .strip_prefix(root)
                .map_err(|e| e.to_string())?
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/");
            out.push((rel, path));
        }
    }
    Ok(())
}

/// The tags of `features.txt`: every non-comment line's first word.
fn known_tags(text: &str) -> BTreeSet<String> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or_default().trim())
        .filter(|l| !l.is_empty())
        .map(str::to_owned)
        .collect()
}

/// A Rust list of string literals.
fn list(items: &[String]) -> String {
    let parts: Vec<String> = items.iter().map(|s| format!("{s:?}")).collect();
    format!("&[{}]", parts.join(", "))
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let features_path = dir.join("features.txt");
    let known = known_tags(
        &std::fs::read_to_string(&features_path)
            .map_err(|e| format!("{}: {e}", features_path.display()))?,
    );
    let mut files = Vec::new();
    walk(dir, &dir.join("test"), &mut files)?;
    files.sort();

    let mut out = String::from(
        "// @generated by `cargo xtask testdata` from tests/data/test262/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/test262.rs) produces.\n\
         // Source, commit and license: tests/data/test262/SOURCE.md.\n\n\
         /// Every test of test/**/*.js (not the `_FIXTURE` modules): its frontmatter,\n\
         /// and whether it is an expected failure, with the reason.\n\
         const TEST262: &[Case] = &[\n",
    );
    let mut tests = 0usize;
    let mut expected_failures = 0usize;
    let mut by_reason: std::collections::BTreeMap<&'static str, usize> =
        std::collections::BTreeMap::new();
    for (rel, path) in &files {
        let name = rel.rsplit('/').next().unwrap_or(rel);
        if name.contains("_FIXTURE") {
            continue;
        }
        let bytes = std::fs::read(path).map_err(|e| format!("{rel}: {e}"))?;
        let text = String::from_utf8_lossy(&bytes);
        let meta = frontmatter(&text)
            .and_then(parse_meta)
            .map_err(|e| format!("{rel}: {e}"))?;
        let mut reasons: Vec<&'static str> = Vec::new();
        for tag in &meta.features {
            if !known.contains(tag) {
                return Err(format!(
                    "{rel}: feature {tag:?} is not in features.txt; classify it in \
                     xtask/src/testdata/test262.rs"
                ));
            }
            if let Some(r) = excluded(tag)
                && !reasons.contains(&r)
            {
                reasons.push(r);
            }
        }
        for inc in &meta.includes {
            if !dir.join("harness").join(inc).is_file() {
                return Err(format!(
                    "{rel}: includes {inc:?}, which harness/ does not have"
                ));
            }
            if AGENT_HELPERS.contains(&inc.as_str()) && !reasons.contains(&EXCLUDED_REASON_AGENT) {
                reasons.push(EXCLUDED_REASON_AGENT);
            }
        }
        let test_path = rel.strip_prefix("test/").unwrap_or(rel);
        let negative = match &meta.negative {
            Some((p, t)) => format!("Some(({p:?}, {t:?}))"),
            None => "None".to_owned(),
        };
        let expect = if reasons.is_empty() {
            "Expect::Run".to_owned()
        } else {
            expected_failures = expected_failures.saturating_add(1);
            for r in &reasons {
                let n = by_reason.entry(r).or_insert(0);
                *n = n.saturating_add(1);
            }
            format!("Expect::Fail({:?})", reasons.join("; "))
        };
        tests = tests.saturating_add(1);
        writeln!(
            out,
            "    Case {{ path: {test_path:?}, flags: {}, features: {}, includes: {}, \
             negative: {negative}, expect: {expect} }},",
            list(&meta.flags),
            list(&meta.features),
            list(&meta.includes),
        )
        .map_err(|e| e.to_string())?;
    }
    writeln!(out, "];").map_err(|e| e.to_string())?;
    writeln!(
        out,
        "\n// {tests} tests, {expected_failures} expected failures (a test with several reasons counts once; the counts below count each reason):"
    )
    .map_err(|e| e.to_string())?;
    for (reason, n) in &by_reason {
        writeln!(out, "//   {n:>6}  {reason}").map_err(|e| e.to_string())?;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_shapes_of_interpreting_md() -> Result<(), String> {
        let front = "\nesid: sec-x\ndescription: One line.\ninfo: |\n  text\n  more\nflags: [onlyStrict, module]\nfeatures:\n  - a\n  - b\nincludes: [x.js,\n  y.js]\nnegative:\n  phase: parse\n  type: SyntaxError\n";
        let m = parse_meta(front)?;
        assert_eq!(m.flags, ["onlyStrict", "module"]);
        assert_eq!(m.features, ["a", "b"]);
        assert_eq!(m.includes, ["x.js", "y.js"]);
        assert_eq!(
            m.negative,
            Some(("parse".to_owned(), "SyntaxError".to_owned()))
        );
        Ok(())
    }

    #[test]
    fn rejects_what_it_does_not_know() {
        assert!(parse_meta("bogus: 1\n").is_err());
        assert!(parse_meta("flags: [nope]\n").is_err());
        assert!(parse_meta("negative:\n  phase: sometime\n  type: X\n").is_err());
    }

    #[test]
    fn classifies_features() {
        assert!(excluded("SharedArrayBuffer").is_some());
        assert!(excluded("Intl.Locale").is_some());
        assert!(excluded("intl-normative-optional").is_some());
        assert!(excluded("decorators").is_some());
        assert!(excluded("regexp-duplicate-named-groups").is_none());
        assert!(excluded("class").is_none());
    }
}
