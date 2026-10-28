//! The named character references table for `clazel-html` (Phase 4 item
//! 4.1; HTML §13.5).
//!
//! WHATWG's `entities.json` is vendored, byte for byte, under
//! `crates/clazel-html/data/entities-<commit>/` with a `SOURCE.md` giving the
//! upstream commit, URL and SHA-256. This module turns it into
//! `crates/clazel-html/src/charref/data.rs`, a Rust file of constant arrays
//! that is committed (the chunked opaque tables of `unicode.rs`). `cargo
//! xtask tables` writes it; `check` and `verify` fail if the vendored file's
//! hash differs from `SOURCE.md` or the committed file differs from what
//! this produces.
//!
//! The proofs are relative to these tables, so what this module derives is
//! kept to simple, stated steps (each is listed in the generated file's
//! header):
//! - one row per key of the JSON object, in byte order of the keys
//!   (`serde_json`'s map is sorted; the vendored file lists its keys in
//!   that order too, and the order of rows changes no result: the matching
//!   rule takes the longest name, which is unique);
//! - a row's name is the key without its leading `&`, exactly as the first
//!   column of the standard's table lists it: with its `;` where the table
//!   has one, so a name that may match without a semicolon is the one that
//!   has a second row without it;
//! - a row's code points are the key's `codepoints` array, one or two of
//!   them; a single code point has `ENTITY_CP2` 0.
//!
//! It also rejects, so the tables can rely on it: a key that does not start
//! with `&`; a name that is empty or has anything but ASCII alphanumerics
//! and one final `;`; a name longer than 255; zero or more than two code
//! points; a code point that is 0, a surrogate or above U+10FFFF; a
//! `characters` string that is not those code points; a duplicate name; a
//! name without `;` whose `;` form is missing or maps elsewhere.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::reviews;
use crate::unicode::{Table, emit};
use crate::workspace;

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-html/data/entities-283a3531";
/// The generated file, relative to the repository root.
const OUTPUT: &str = "crates/clazel-html/src/charref/data.rs";
/// The files `SOURCE.md` must list, besides itself and LICENSE.
const FILES: &[&str] = &["entities.json"];
/// The number of rows the standard's table has (HTML §13.5).
const ROWS: usize = 2231;

/// Compare (or, with `write`, rewrite) the generated tables. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_sources(&dir);
    let mut notes = Vec::new();
    if !problems.is_empty() {
        return (problems, notes);
    }
    let fresh = match std::fs::read_to_string(dir.join("entities.json"))
        .map_err(|e| e.to_string())
        .and_then(|t| generate(&t))
    {
        Ok(f) => f,
        Err(e) => return (vec![format!("{DATA_DIR}: {e}")], notes),
    };
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
            "{OUTPUT}: stale (differs from what xtask/src/entities.rs produces); \
             run `cargo xtask tables` and commit the result"
        ));
    }
    (problems, notes)
}

/// Every vendored file is listed in `SOURCE.md` with its SHA-256, and
/// matches it; nothing else is in the directory.
fn check_sources(dir: &Path) -> Vec<String> {
    let rel = workspace::relative(dir);
    let source = match std::fs::read_to_string(dir.join("SOURCE.md")) {
        Ok(s) => s,
        Err(e) => return vec![format!("{rel}/SOURCE.md: {e}")],
    };
    let mut problems = Vec::new();
    for file in FILES {
        let listed = source.lines().find_map(|l| {
            let rest = l.trim().strip_prefix("SHA-256:")?.trim();
            let (hash, name) = rest.split_once(char::is_whitespace)?;
            (name.trim().trim_matches('`') == *file).then(|| hash.to_ascii_lowercase())
        });
        let Some(listed) = listed else {
            problems.push(format!(
                "{rel}/SOURCE.md: no \"SHA-256: <hash> {file}\" line"
            ));
            continue;
        };
        match reviews::sha256(&dir.join(file)) {
            Ok(actual) if actual == listed => {}
            Ok(actual) => problems.push(format!(
                "{rel}/{file}: SHA-256 {actual} differs from SOURCE.md ({listed})"
            )),
            Err(e) => problems.push(e),
        }
    }
    if !source.lines().any(|l| l.trim().starts_with("License:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"License:\" line"));
    }
    if !source.lines().any(|l| l.trim().starts_with("Commit:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"Commit:\" line"));
    }
    match std::fs::read_dir(dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !FILES.contains(&name.as_str()) && name != "SOURCE.md" && name != "LICENSE" {
                    problems.push(format!(
                        "{rel}/{name}: not an input of xtask/src/entities.rs"
                    ));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

/// One row of the table: the name (without `&`) and its code points.
struct Row {
    name: String,
    cps: Vec<u32>,
}

/// Read and check `entities.json`.
fn rows(text: &str) -> Result<Vec<Row>, String> {
    let json: Value = serde_json::from_str(text).map_err(|e| e.to_string())?;
    let obj = json
        .as_object()
        .ok_or("entities.json: expected a JSON object")?;
    let mut out: Vec<Row> = Vec::new();
    for (key, value) in obj {
        let name = key
            .strip_prefix('&')
            .ok_or_else(|| format!("{key:?}: does not start with &"))?;
        let body = name.strip_suffix(';').unwrap_or(name);
        if body.is_empty() || !body.bytes().all(|b| b.is_ascii_alphanumeric()) {
            return Err(format!(
                "{key:?}: not ASCII alphanumerics and an optional final ;"
            ));
        }
        if name.len() > 255 {
            return Err(format!("{key:?}: longer than 255"));
        }
        let cps: Vec<u32> = value
            .get("codepoints")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("{key:?}: no \"codepoints\" array"))?
            .iter()
            .map(|v| {
                v.as_u64()
                    .and_then(|n| u32::try_from(n).ok())
                    .ok_or_else(|| format!("{key:?}: a code point is not a number"))
            })
            .collect::<Result<_, _>>()?;
        if cps.is_empty() || cps.len() > 2 {
            return Err(format!("{key:?}: {} code points", cps.len()));
        }
        if let Some(c) = cps
            .iter()
            .find(|&&c| c == 0 || (0xD800..=0xDFFF).contains(&c) || c > 0x10_FFFF)
        {
            return Err(format!(
                "{key:?}: code point {c:#X} is 0, a surrogate or out of range"
            ));
        }
        let chars: Vec<u32> = value
            .get("characters")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{key:?}: no \"characters\" string"))?
            .chars()
            .map(u32::from)
            .collect();
        if chars != cps {
            return Err(format!(
                "{key:?}: \"characters\" differs from \"codepoints\""
            ));
        }
        if out.iter().any(|r| r.name == name) {
            return Err(format!("{key:?}: duplicate name"));
        }
        out.push(Row {
            name: name.to_owned(),
            cps,
        });
    }
    for r in &out {
        if !r.name.ends_with(';') {
            let with = format!("{};", r.name);
            match out.iter().find(|s| s.name == with) {
                Some(s) if s.cps == r.cps => {}
                _ => {
                    return Err(format!("&{}: no &{with} with the same code points", r.name));
                }
            }
        }
    }
    if out.len() != ROWS {
        return Err(format!("{} rows, expected {ROWS}", out.len()));
    }
    Ok(out)
}

fn generate(text: &str) -> Result<String, String> {
    let rows = rows(text)?;
    let mut starts = Vec::new();
    let mut lens = Vec::new();
    let mut cp1 = Vec::new();
    let mut cp2 = Vec::new();
    let mut chars: Vec<u8> = Vec::new();
    for r in &rows {
        starts.push(u32::try_from(chars.len()).map_err(|e| e.to_string())?);
        lens.push(u8::try_from(r.name.len()).map_err(|e| e.to_string())?);
        chars.extend(r.name.bytes());
        cp1.push(r.cps.first().copied().unwrap_or(0));
        cp2.push(r.cps.get(1).copied().unwrap_or(0));
    }
    let semicolonless = rows.iter().filter(|r| !r.name.ends_with(';')).count();
    let mut out = String::from(HEADER);
    let _ = writeln!(
        out,
        "/// Rows of the table whose name has no final `;`: the names that may\n\
         /// match without a semicolon.\n\
         pub const ENTITY_ROWS_WITHOUT_SEMICOLON: usize = {semicolonless};\n"
    );
    let hex = |v: &[u32]| v.iter().map(|c| format!("0x{c:X}")).collect();
    emit(
        &mut out,
        &Table {
            name: "entity_name_start",
            doc: "Where each row's name starts in ENTITY_CHARS.",
            row_type: "u32",
            row_bytes: 4,
            rows: starts.iter().map(|s| format!("{s}")).collect(),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "entity_name_len",
            doc: "The length of each row's name.",
            row_type: "u8",
            row_bytes: 1,
            rows: lens.iter().map(|l| format!("{l}")).collect(),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "entity_cp1",
            doc: "Each row's first code point.",
            row_type: "u32",
            row_bytes: 4,
            rows: hex(&cp1),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "entity_cp2",
            doc: "Each row's second code point, or 0 if it has one.",
            row_type: "u32",
            row_bytes: 4,
            rows: hex(&cp2),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "entity_chars",
            doc: "The names' characters, row after row (ASCII).",
            row_type: "u8",
            row_bytes: 1,
            rows: chars.iter().map(|c| format!("0x{c:X}")).collect(),
        },
    );
    let _ = writeln!(out, "}} // verus!");
    Ok(out)
}

const HEADER: &str = "\
//! The named character references table (HTML §13.5).
//!
// @generated by `cargo xtask tables` (xtask/src/entities.rs) from
// crates/clazel-html/data/entities-283a3531/ (the whatwg/html-build commit
// and SHA-256 of entities.json are in SOURCE.md there). Do not edit: `cargo
// xtask check` fails if this differs from what the generator produces.
//
// What the generator derives (the proofs are relative to these tables):
// - One row per key of entities.json, in byte order of the keys: 2231 rows,
//   the rows of the standard's table.
// - Row i's name is the key without its leading `&`, as the standard's
//   first column lists it (with its final `;` where it has one): the
//   characters ENTITY_CHARS[ENTITY_NAME_START[i] .. ENTITY_NAME_START[i] +
//   ENTITY_NAME_LEN[i]]. A name that may match without a semicolon is one
//   that also has a row without the `;`.
// - Row i's code points are ENTITY_CP1[i], then ENTITY_CP2[i] unless it is 0.
// - Checked when generating: every name is ASCII alphanumerics with an
//   optional final `;`, non-empty, at most 255 long, and unique; one or two
//   code points, none 0, a surrogate or above U+10FFFF, equal to the
//   `characters` string; every name without `;` has a `;` row with the same
//   code points.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

";
