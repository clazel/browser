//! Unicode data tables for `clazel-layout`'s line breaking (Phase 5 item 5.12).
//!
//! UAX #14 needs Line_Break, and its rules read East_Asian_Width,
//! Extended_Pictographic and a few General_Category values; CSS Text 3 reads
//! two more categories. The data files are vendored, byte for byte, under
//! `crates/clazel-layout/data/unicode-<version>/`, with a `SOURCE.md` giving
//! each file's upstream URL and SHA-256. This module turns them into
//! `crates/clazel-layout/src/text/data.rs`, a Rust file of constant arrays
//! that is committed. `cargo xtask tables` writes it; `check` and `verify`
//! fail if a vendored file's hash differs from `SOURCE.md` or the committed
//! file differs from what this produces.
//!
//! What it derives is kept to simple, stated steps (each is listed in the
//! generated file's header):
//! - LINE_BREAK: LineBreak.txt with its `@missing` default applied first,
//!   then its data lines, as maximal ranges of one class covering
//!   U+0000..U+10FFFF.
//! - EAST_ASIAN: maximal ranges of East_Asian_Width F, W or H
//!   (EastAsianWidth.txt; its `@missing` default is N, outside the set).
//! - EXTENDED_PICTOGRAPHIC: maximal ranges of Extended_Pictographic
//!   (emoji-data.txt).
//! - GENERAL_CATEGORY: maximal ranges of each of Mn, Mc, Pi, Pf, Cn, Zs and
//!   Cc (DerivedGeneralCategory.txt, which lists every code point; one that
//!   it omitted would be Cn).
//!
//! `LineBreakTest.txt` is hashed but not converted: the conformance test
//! includes it as it is.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::unicode::{check_vendored, data_lines, range, read};

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-layout/data/unicode-18.0.0";
/// The generated file, relative to the repository root.
const OUTPUT: &str = "crates/clazel-layout/src/text/data.rs";
/// The files `SOURCE.md` must list, besides itself and LICENSE.md.
const FILES: &[&str] = &[
    "LineBreak.txt",
    "LineBreakTest.txt",
    "EastAsianWidth.txt",
    "emoji-data.txt",
    "DerivedGeneralCategory.txt",
];

const MAX_CODE_POINT: u32 = 0x10_FFFF;

/// The Line_Break values of UAX #14 §5.1, as the short names LineBreak.txt
/// uses. They are also the names of `clazel_layout::text::Lb`'s variants.
const LINE_BREAK_CLASSES: &[&str] = &[
    "AI", "AK", "AL", "AP", "AS", "B2", "BA", "BB", "BK", "CB", "CJ", "CL", "CM", "CP", "CR", "EB",
    "EM", "EX", "GL", "H2", "H3", "HH", "HL", "HY", "ID", "IN", "IS", "JL", "JT", "JV", "LF", "NL",
    "NS", "NU", "OP", "PO", "PR", "QU", "RI", "SA", "SG", "SP", "SY", "VF", "VI", "WJ", "XX", "ZW",
    "ZWJ",
];

/// The General_Category values the tables keep, in `Gc`'s order.
const CATEGORIES: &[&str] = &["Mn", "Mc", "Pi", "Pf", "Cn", "Zs", "Cc"];

/// Compare (or, with `write`, rewrite) the generated tables. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_vendored(&dir, FILES, "xtask/src/linebreak.rs");
    let mut notes = Vec::new();
    if !problems.is_empty() {
        return (problems, notes);
    }
    let fresh = match generate(&dir) {
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
            "{OUTPUT}: stale (differs from what xtask/src/linebreak.rs produces); \
             run `cargo xtask tables` and commit the result"
        ));
    }
    (problems, notes)
}

/// A value for every code point, from a file's `@missing` lines (in file
/// order) and then its data lines; `value` maps a field to the value kept.
fn per_code_point<T: Copy>(
    text: &str,
    file: &str,
    initial: T,
    value: impl Fn(&str, usize) -> Result<T, String>,
) -> Result<Vec<T>, String> {
    let len = usize::try_from(MAX_CODE_POINT)
        .map_err(|e| e.to_string())?
        .saturating_add(1);
    let mut all = vec![initial; len];
    let mut set = |a: u32, b: u32, v: T, line: usize| -> Result<(), String> {
        if a > b || b > MAX_CODE_POINT {
            return Err(format!("{file}:{line}: bad range"));
        }
        for c in a..=b {
            let i = usize::try_from(c).map_err(|e| e.to_string())?;
            if let Some(slot) = all.get_mut(i) {
                *slot = v;
            }
        }
        Ok(())
    };
    for (i, l) in text.lines().enumerate() {
        let line = i.saturating_add(1);
        if let Some(rest) = l.strip_prefix("# @missing:") {
            let f: Vec<&str> = rest.split(';').map(str::trim).collect();
            let (a, b) = range(f.first().copied().unwrap_or(""), file, line)?;
            let v = value(f.get(1).copied().unwrap_or(""), line)?;
            set(a, b, v, line)?;
        }
    }
    for (line, f) in data_lines(text) {
        let (a, b) = range(f.first().copied().unwrap_or(""), file, line)?;
        let v = value(f.get(1).copied().unwrap_or(""), line)?;
        set(a, b, v, line)?;
    }
    Ok(all)
}

/// Maximal ranges of equal value, leaving out `skip`.
fn runs<T: Copy + PartialEq>(values: &[T], skip: Option<T>) -> Vec<(u32, u32, T)> {
    let mut out: Vec<(u32, u32, T)> = Vec::new();
    for (c, &v) in (0u32..).zip(values) {
        if Some(v) == skip {
            continue;
        }
        match out.last_mut() {
            Some((_, last, prev)) if *prev == v && last.checked_add(1) == Some(c) => *last = c,
            _ => out.push((c, c, v)),
        }
    }
    out
}

fn generate(dir: &Path) -> Result<String, String> {
    // LineBreak.txt: every value must be one of UAX #14's classes.
    let lb_text = read(dir, "LineBreak.txt")?;
    let lb = per_code_point(&lb_text, "LineBreak.txt", None, |v, line| {
        LINE_BREAK_CLASSES
            .iter()
            .position(|c| *c == v)
            .map(Some)
            .ok_or(format!("LineBreak.txt:{line}: unknown class {v:?}"))
    })?;
    if lb.iter().any(Option::is_none) {
        return Err("LineBreak.txt: a code point has no class (no @missing line?)".into());
    }
    let line_break = runs(&lb, None);

    let ea_text = read(dir, "EastAsianWidth.txt")?;
    let ea = per_code_point(&ea_text, "EastAsianWidth.txt", false, |v, line| match v {
        "F" | "W" | "H" => Ok(true),
        "N" | "Na" | "A" => Ok(false),
        other => Err(format!(
            "EastAsianWidth.txt:{line}: unknown width {other:?}"
        )),
    })?;
    let east_asian = runs(&ea, Some(false));

    let emoji_text = read(dir, "emoji-data.txt")?;
    let mut ext = vec![false; ea.len()];
    for (line, f) in data_lines(&emoji_text) {
        if f.get(1).copied() == Some("Extended_Pictographic") {
            let (a, b) = range(f.first().copied().unwrap_or(""), "emoji-data.txt", line)?;
            for c in a..=b {
                let i = usize::try_from(c).map_err(|e| e.to_string())?;
                *ext.get_mut(i)
                    .ok_or(format!("emoji-data.txt:{line}: beyond U+10FFFF"))? = true;
            }
        }
    }
    let extended_pictographic = runs(&ext, Some(false));

    let gc_text = read(dir, "DerivedGeneralCategory.txt")?;
    // Unlisted code points would be Cn (index 4); every listed category other
    // than the kept ones is "other" (None).
    let gc = per_code_point(
        &gc_text,
        "DerivedGeneralCategory.txt",
        Some(4usize),
        |v, line| {
            const ALL: &[&str] = &[
                "Lu", "Ll", "Lt", "Lm", "Lo", "Mn", "Mc", "Me", "Nd", "Nl", "No", "Pc", "Pd", "Ps",
                "Pe", "Pi", "Pf", "Po", "Sm", "Sc", "Sk", "So", "Zs", "Zl", "Zp", "Cc", "Cf", "Cs",
                "Co", "Cn",
            ];
            if !ALL.contains(&v) {
                return Err(format!(
                    "DerivedGeneralCategory.txt:{line}: unknown category {v:?}"
                ));
            }
            Ok(CATEGORIES.iter().position(|c| *c == v))
        },
    )?;
    let general_category = runs(&gc, None)
        .into_iter()
        .filter_map(|(a, b, v)| v.map(|v| (a, b, v)))
        .collect::<Vec<_>>();

    let mut out = String::new();
    out.push_str(HEADER);
    let name = |i: usize, names: &[&str]| names.get(i).copied().unwrap_or("?").to_owned();
    table(
        &mut out,
        "LINE_BREAK",
        "Line_Break (LineBreak.txt), as maximal ranges covering U+0000..U+10FFFF.",
        "(u32, u32, Lb)",
        line_break
            .iter()
            .map(|&(a, b, v)| {
                let v = v.map_or_else(|| "?".to_owned(), |v| name(v, LINE_BREAK_CLASSES));
                format!("(0x{a:X}, 0x{b:X}, Lb::{v})")
            })
            .collect(),
    );
    table(
        &mut out,
        "EAST_ASIAN",
        "East_Asian_Width F, W or H (EastAsianWidth.txt): UAX #14's `$EastAsian`.",
        "(u32, u32)",
        east_asian
            .iter()
            .map(|&(a, b, _)| format!("(0x{a:X}, 0x{b:X})"))
            .collect(),
    );
    table(
        &mut out,
        "EXTENDED_PICTOGRAPHIC",
        "Extended_Pictographic (emoji-data.txt).",
        "(u32, u32)",
        extended_pictographic
            .iter()
            .map(|&(a, b, _)| format!("(0x{a:X}, 0x{b:X})"))
            .collect(),
    );
    table(
        &mut out,
        "GENERAL_CATEGORY",
        "General_Category Mn, Mc, Pi, Pf, Cn, Zs and Cc (DerivedGeneralCategory.txt); \
         a code point in no range has another category.",
        "(u32, u32, Gc)",
        general_category
            .iter()
            .map(|&(a, b, v)| format!("(0x{a:X}, 0x{b:X}, Gc::{})", name(v, CATEGORIES)))
            .collect(),
    );
    Ok(out)
}

const HEADER: &str = "\
//! The Unicode tables of line breaking (UAX #14 and CSS Text 3).
//!
// @generated by `cargo xtask tables` (xtask/src/linebreak.rs) from
// crates/clazel-layout/data/unicode-18.0.0/ (Unicode 18.0.0; files, URLs and
// SHA-256 in SOURCE.md there). Do not edit: `cargo xtask check` fails if
// this differs from what the generator produces.
//
// What the generator derives:
// - LINE_BREAK: LineBreak.txt with its @missing default (XX) applied first,
//   then its data lines, as maximal ranges of one class covering
//   U+0000..U+10FFFF.
// - EAST_ASIAN: maximal ranges of East_Asian_Width F, W or H
//   (EastAsianWidth.txt; its @missing default, N, is outside the set).
// - EXTENDED_PICTOGRAPHIC: maximal ranges of Extended_Pictographic
//   (emoji-data.txt).
// - GENERAL_CATEGORY: maximal ranges of each of Mn, Mc, Pi, Pf, Cn, Zs and
//   Cc (DerivedGeneralCategory.txt).
// Every table is sorted and its ranges are disjoint.

use super::classes::{Gc, Lb};
";

fn table(out: &mut String, name: &str, doc: &str, row: &str, rows: Vec<String>) {
    let _ = write!(
        out,
        "\n/// {doc}\npub static {name}: [{row}; {}] = [\n",
        rows.len()
    );
    for r in rows {
        let _ = writeln!(out, "    {r},");
    }
    out.push_str("];\n");
}
