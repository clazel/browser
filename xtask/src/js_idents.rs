//! The `ID_Start` and `ID_Continue` tables of `clazel-js-lexer` (Phase 7
//! item 7.2).
//!
//! ECMA-262 §12.7 defines `UnicodeIDStart` and `UnicodeIDContinue` as the
//! code points with the Unicode properties `ID_Start` and `ID_Continue`.
//! The lexer's spec defines them for ASCII and leaves the rest
//! uninterpreted; the executable lexer reads them from
//! `crates/clazel-js-lexer/src/unicode_data.rs`, which this module writes
//! from `DerivedCoreProperties.txt` of Unicode 18.0.0, the copy vendored for
//! `clazel-js-regexp` (`crates/clazel-js-regexp/tests/data/ucd-regexp/`;
//! `cargo xtask testdata` checks that directory's inventory). `cargo xtask
//! tables` writes it; `check` and `verify` fail if the file's SHA-256
//! differs from that `SOURCE.md` or the committed table differs from what
//! this produces.
//!
//! What it derives (also listed in the generated file's header): for each
//! of the two properties, the code points above U+007F listed with it, as
//! maximal ranges, sorted and disjoint.

use std::path::{Path, PathBuf};

use crate::reviews;
use crate::unicode::{Table, data_lines, emit_chunked, range, read};

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-js-regexp/tests/data/ucd-regexp";
/// The one file read.
const FILE: &str = "DerivedCoreProperties.txt";
/// The generated file, relative to the repository root.
const OUTPUT: &str = "crates/clazel-js-lexer/src/unicode_data.rs";

const MAX_CODE_POINT: u32 = 0x10_FFFF;

/// Compare (or, with `write`, rewrite) the generated table. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut notes = Vec::new();
    if let Err(e) = check_hash(&dir) {
        return (vec![e], notes);
    }
    let fresh = match generate(&dir) {
        Ok(f) => f,
        Err(e) => return (vec![format!("{DATA_DIR}: {e}")], notes),
    };
    let mut problems = Vec::new();
    let current = std::fs::read_to_string(OUTPUT).ok();
    if current.as_deref() == Some(fresh.as_str()) {
        notes.push(format!("{OUTPUT}: up to date"));
    } else if write {
        match std::fs::write(OUTPUT, &fresh) {
            Ok(()) => notes.push(format!("{OUTPUT}: written")),
            Err(e) => problems.push(format!("{OUTPUT}: {e}")),
        }
    } else if current.is_none() {
        problems.push(format!("{OUTPUT}: missing; run `cargo xtask tables`"));
    } else {
        problems.push(format!(
            "{OUTPUT}: stale (differs from what xtask/src/js_idents.rs produces); \
             run `cargo xtask tables` and commit the result"
        ));
    }
    (problems, notes)
}

/// The file's SHA-256 is the one its `SOURCE.md` lists, and its header
/// names Unicode 18.0.0.
fn check_hash(dir: &Path) -> Result<(), String> {
    let source = std::fs::read_to_string(dir.join("SOURCE.md"))
        .map_err(|e| format!("{DATA_DIR}/SOURCE.md: {e}"))?;
    let listed = source
        .lines()
        .find_map(|l| {
            let rest = l.trim().strip_prefix("SHA-256:")?.trim();
            let (hash, name) = rest.split_once(char::is_whitespace)?;
            (name.trim().trim_matches('`') == FILE).then(|| hash.to_ascii_lowercase())
        })
        .ok_or(format!(
            "{DATA_DIR}/SOURCE.md: no \"SHA-256: <hash> {FILE}\" line"
        ))?;
    let actual = reviews::sha256(&dir.join(FILE))?;
    if actual != listed {
        return Err(format!(
            "{DATA_DIR}/{FILE}: SHA-256 {actual} differs from SOURCE.md ({listed})"
        ));
    }
    let text = read(dir, FILE)?;
    if !text
        .lines()
        .next()
        .is_some_and(|l| l.contains("DerivedCoreProperties-18.0.0.txt"))
    {
        return Err(format!("{DATA_DIR}/{FILE}: not Unicode 18.0.0"));
    }
    Ok(())
}

/// The maximal ranges above U+007F of the code points `FILE` lists with
/// property `name`.
fn ranges(text: &str, name: &str) -> Result<Vec<(u32, u32)>, String> {
    let len = usize::try_from(MAX_CODE_POINT)
        .map_err(|e| e.to_string())?
        .saturating_add(1);
    let mut has = vec![false; len];
    let mut found = false;
    for (line, f) in data_lines(text) {
        if f.get(1).copied() != Some(name) {
            continue;
        }
        found = true;
        let (a, b) = range(f.first().copied().unwrap_or(""), FILE, line)?;
        if a > b || b > MAX_CODE_POINT {
            return Err(format!("{FILE}:{line}: bad range"));
        }
        for c in a..=b {
            let i = usize::try_from(c).map_err(|e| e.to_string())?;
            if let Some(slot) = has.get_mut(i) {
                *slot = true;
            }
        }
    }
    if !found {
        return Err(format!("{FILE}: no {name} lines"));
    }
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (c, &v) in (0u32..).zip(&has) {
        if !v || c < 0x80 {
            continue;
        }
        match out.last_mut() {
            Some((_, last)) if last.checked_add(1) == Some(c) => *last = c,
            _ => out.push((c, c)),
        }
    }
    Ok(out)
}

/// Rows per constant array (the accessors search across chunks, and the
/// sortedness proof reads one chunk at a time).
const CHUNK_ROWS: usize = 350;

fn generate(dir: &Path) -> Result<String, String> {
    let text = read(dir, FILE)?;
    let id_start = ranges(&text, "ID_Start")?;
    let id_continue = ranges(&text, "ID_Continue")?;
    let mut out = String::new();
    out.push_str(HEADER);
    table(
        &mut out,
        "id_start",
        "`ID_Start` above U+007F (DerivedCoreProperties.txt), as maximal ranges.",
        &id_start,
    );
    table(
        &mut out,
        "id_continue",
        "`ID_Continue` above U+007F (DerivedCoreProperties.txt), as maximal ranges.",
        &id_continue,
    );
    out.push_str("} // verus!\n");
    Ok(out)
}

const HEADER: &str = "\
//! The Unicode `ID_Start` and `ID_Continue` tables of the lexer (§12.7).
//!
// @generated by `cargo xtask tables` (xtask/src/js_idents.rs) from
// crates/clazel-js-regexp/tests/data/ucd-regexp/DerivedCoreProperties.txt
// (Unicode 18.0.0; URL and SHA-256 in SOURCE.md there). Do not edit:
// `cargo xtask check` fails if this differs from what the generator
// produces.
//
// What the generator derives: for each of ID_Start and ID_Continue, the
// code points above U+007F that DerivedCoreProperties.txt lists with it, as
// maximal ranges (first, last), sorted and disjoint. Each table is split
// into constant arrays of at most 350 rows; `<name>_at(i)` is row `i` as the
// spec sees it and `<name>_at_exec(i)` returns it, proven equal.

use super::unicode::Range;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
";

fn table(out: &mut String, name: &str, doc: &str, rows: &[(u32, u32)]) {
    out.push('\n');
    emit_chunked(
        out,
        &Table {
            name,
            doc,
            row_type: "Range",
            row_bytes: 8,
            rows: rows
                .iter()
                .map(|(a, b)| format!("Range {{ first: 0x{a:X}, last: 0x{b:X} }}"))
                .collect(),
        },
        CHUNK_ROWS,
    );
}
