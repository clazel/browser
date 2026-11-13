//! Unicode data tables for `clazel-idna` (Phase 1 item 1.8).
//!
//! UTS #46 processing needs the IDNA Mapping Table and several Unicode
//! Character Database properties. The data files are vendored, byte for
//! byte, under `crates/clazel-idna/data/unicode-<version>/`, with a
//! `SOURCE.md` giving each file's upstream URL and SHA-256. This module
//! turns them into `crates/clazel-idna/src/uts46/data.rs`, a Rust file of
//! constant arrays that is committed. `cargo xtask tables` writes it;
//! `check` and `verify` fail if a vendored file's hash differs from
//! `SOURCE.md` or the committed file differs from what this produces.
//!
//! The proofs are relative to these tables, so what this module derives
//! is part of the trusted base and is kept to simple, stated steps (each
//! is listed in the generated file's header):
//! - IDNA mapping: one row per data line of IdnaMappingTable.txt, in file
//!   order, with its status and mapping. The rows must be sorted, disjoint
//!   and cover U+0000..U+10FFFF.
//! - Canonical decomposition: for each code point with a canonical
//!   Decomposition_Mapping in UnicodeData.txt (field 5 without a `<tag>`),
//!   the full canonical decomposition: the mapping with every code point
//!   in it replaced by its own full canonical decomposition, recursively
//!   (Unicode §3.7 D68). Hangul syllables have no mapping in UnicodeData
//!   and are decomposed algorithmically by the spec.
//! - Composition: for each code point P whose canonical
//!   Decomposition_Mapping is exactly two code points <L, C> and which is
//!   not Full_Composition_Exclusion (DerivedNormalizationProps.txt), the
//!   row (L, C, P), sorted by (L, C). These are the primary composites
//!   (§3.11 D114) other than Hangul syllables.
//! - Canonical_Combining_Class: maximal ranges of equal non-zero class
//!   from UnicodeData.txt field 3.
//! - General_Category=Mark: maximal ranges of Mn, Mc and Me from
//!   UnicodeData.txt field 2.
//! - Bidi_Class: DerivedBidiClass.txt, its `@missing` defaults applied in
//!   file order and then its data lines, as maximal ranges covering
//!   U+0000..U+10FFFF.
//! - Joining_Type: DerivedJoiningType.txt, maximal ranges of each type
//!   other than U (Non_Joining, the `@missing` default).

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::reviews;
use crate::workspace;

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-idna/data/unicode-18.0.0";
/// The generated file, relative to the repository root.
const OUTPUT: &str = "crates/clazel-idna/src/uts46/data.rs";
/// The files `SOURCE.md` must list, besides itself and LICENSE.md.
const FILES: &[&str] = &[
    "IdnaMappingTable.txt",
    "UnicodeData.txt",
    "DerivedNormalizationProps.txt",
    "DerivedBidiClass.txt",
    "DerivedJoiningType.txt",
];

const MAX_CODE_POINT: u32 = 0x10_FFFF;

/// Compare (or, with `write`, rewrite) the generated tables. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_sources(&dir);
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
            "{OUTPUT}: stale (differs from what xtask/src/unicode.rs produces); \
             run `cargo xtask tables` and commit the result"
        ));
    }
    (problems, notes)
}

/// Every vendored file is listed in `SOURCE.md` with its SHA-256, and
/// matches it; nothing else is in the directory.
fn check_sources(dir: &Path) -> Vec<String> {
    check_vendored(dir, FILES, "xtask/src/unicode.rs")
}

/// Every one of `files` in `dir` is listed in its `SOURCE.md` with its
/// SHA-256, and matches it; nothing else but `SOURCE.md` and `LICENSE.md`
/// is in the directory. `generator` names the module that reads them.
pub(crate) fn check_vendored(dir: &Path, files: &[&str], generator: &str) -> Vec<String> {
    let rel = workspace::relative(dir);
    let source = match std::fs::read_to_string(dir.join("SOURCE.md")) {
        Ok(s) => s,
        Err(e) => return vec![format!("{rel}/SOURCE.md: {e}")],
    };
    let mut problems = Vec::new();
    for file in files {
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
    match std::fs::read_dir(dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !files.contains(&name.as_str()) && name != "SOURCE.md" && name != "LICENSE.md" {
                    problems.push(format!("{rel}/{name}: not an input of {generator}"));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

pub(crate) fn read(dir: &Path, file: &str) -> Result<String, String> {
    std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))
}

pub(crate) fn hex(s: &str, file: &str, line: usize) -> Result<u32, String> {
    u32::from_str_radix(s.trim(), 16)
        .map_err(|e| format!("{file}:{line}: bad code point {s:?}: {e}"))
}

/// `XXXX` or `XXXX..YYYY`.
pub(crate) fn range(s: &str, file: &str, line: usize) -> Result<(u32, u32), String> {
    match s.trim().split_once("..") {
        Some((a, b)) => Ok((hex(a, file, line)?, hex(b, file, line)?)),
        None => {
            let c = hex(s, file, line)?;
            Ok((c, c))
        }
    }
}

/// Data lines: (1-based line number, fields split at `;`, trimmed), with
/// comments removed.
pub(crate) fn data_lines(text: &str) -> impl Iterator<Item = (usize, Vec<&str>)> {
    text.lines().enumerate().filter_map(|(i, l)| {
        let l = l.split('#').next().unwrap_or("").trim();
        (!l.is_empty()).then(|| (i.saturating_add(1), l.split(';').map(str::trim).collect()))
    })
}

struct IdnaRow {
    first: u32,
    last: u32,
    status: &'static str,
    mapping: Vec<u32>,
}

fn idna_rows(text: &str) -> Result<Vec<IdnaRow>, String> {
    const FILE: &str = "IdnaMappingTable.txt";
    let mut rows: Vec<IdnaRow> = Vec::new();
    for (line, f) in data_lines(text) {
        let (first, last) = range(f.first().copied().unwrap_or(""), FILE, line)?;
        let status = match f.get(1).copied() {
            Some("valid") => "Valid",
            Some("ignored") => "Ignored",
            Some("mapped") => "Mapped",
            Some("deviation") => "Deviation",
            Some("disallowed") => "Disallowed",
            other => return Err(format!("{FILE}:{line}: unknown status {other:?}")),
        };
        let mapping = match f.get(2).copied() {
            Some(m) if !m.is_empty() && (status == "Mapped" || status == "Deviation") => m
                .split_whitespace()
                .map(|c| hex(c, FILE, line))
                .collect::<Result<Vec<_>, _>>()?,
            _ => Vec::new(),
        };
        if status == "Mapped" && mapping.is_empty() {
            return Err(format!("{FILE}:{line}: mapped with no mapping"));
        }
        let expected = rows.last().map_or(0, |r| r.last.saturating_add(1));
        if first != expected || last < first {
            return Err(format!(
                "{FILE}:{line}: rows must be sorted, disjoint and contiguous (expected U+{expected:04X})"
            ));
        }
        rows.push(IdnaRow {
            first,
            last,
            status,
            mapping,
        });
    }
    if rows.last().map(|r| r.last) != Some(MAX_CODE_POINT) {
        return Err(format!("{FILE}: does not end at U+10FFFF"));
    }
    Ok(rows)
}

struct UnicodeData {
    /// Canonical Decomposition_Mapping, by code point.
    decomposition: BTreeMap<u32, Vec<u32>>,
    /// Non-zero Canonical_Combining_Class, by code point.
    ccc: BTreeMap<u32, u8>,
    /// Code points with General_Category Mn, Mc or Me.
    marks: Vec<u32>,
}

fn unicode_data(text: &str) -> Result<UnicodeData, String> {
    const FILE: &str = "UnicodeData.txt";
    let mut data = UnicodeData {
        decomposition: BTreeMap::new(),
        ccc: BTreeMap::new(),
        marks: Vec::new(),
    };
    let mut range_start: Option<u32> = None;
    for (i, l) in text.lines().enumerate() {
        let line = i.saturating_add(1);
        let f: Vec<&str> = l.split(';').collect();
        if f.len() != 15 {
            return Err(format!("{FILE}:{line}: expected 15 fields"));
        }
        let field = |n: usize| f.get(n).copied().unwrap_or("");
        let cp = hex(field(0), FILE, line)?;
        let name = field(1);
        let (first, last) = if name.ends_with(", First>") {
            range_start = Some(cp);
            continue;
        } else if name.ends_with(", Last>") {
            let start = range_start
                .take()
                .ok_or(format!("{FILE}:{line}: Last without First"))?;
            (start, cp)
        } else {
            (cp, cp)
        };
        let gc = field(2);
        let ccc: u8 = field(3)
            .parse()
            .map_err(|e| format!("{FILE}:{line}: bad combining class: {e}"))?;
        let decomposition = field(5);
        if first != last && (ccc != 0 || !decomposition.is_empty()) {
            return Err(format!("{FILE}:{line}: a range with a class or mapping"));
        }
        for c in first..=last {
            if gc.starts_with('M') {
                data.marks.push(c);
            }
            if ccc != 0 {
                data.ccc.insert(c, ccc);
            }
        }
        if !decomposition.is_empty() && !decomposition.starts_with('<') {
            let mapping = decomposition
                .split_whitespace()
                .map(|c| hex(c, FILE, line))
                .collect::<Result<Vec<_>, _>>()?;
            data.decomposition.insert(cp, mapping);
        }
    }
    Ok(data)
}

/// D68: the mapping with each code point replaced by its own full
/// canonical decomposition, recursively.
fn full_decomposition(
    map: &BTreeMap<u32, Vec<u32>>,
    c: u32,
    depth: u32,
) -> Result<Vec<u32>, String> {
    if depth > 32 {
        return Err(format!("decomposition of U+{c:04X} does not terminate"));
    }
    match map.get(&c) {
        None => Ok(vec![c]),
        Some(m) => {
            let mut out = Vec::new();
            for &d in m {
                out.extend(full_decomposition(map, d, depth.saturating_add(1))?);
            }
            Ok(out)
        }
    }
}

/// Code points with a binary property in a UCD file (`XXXX..YYYY ; Name`).
fn binary_property(text: &str, file: &str, property: &str) -> Result<Vec<u32>, String> {
    let mut out = Vec::new();
    for (line, f) in data_lines(text) {
        if f.get(1).copied() == Some(property) {
            let (a, b) = range(f.first().copied().unwrap_or(""), file, line)?;
            out.extend(a..=b);
        }
    }
    Ok(out)
}

/// An enumerated property over U+0000..U+10FFFF, with `@missing`
/// defaults (long value names) applied in file order, then data lines
/// (short names). `names` maps long names to short ones.
fn enumerated_property(
    text: &str,
    file: &str,
    names: &[(&str, &'static str)],
) -> Result<Vec<&'static str>, String> {
    let short = |v: &str, line: usize| -> Result<&'static str, String> {
        names
            .iter()
            .find(|(long, s)| *long == v || *s == v)
            .map(|(_, s)| *s)
            .ok_or(format!("{file}:{line}: unknown value {v:?}"))
    };
    let size = usize::try_from(MAX_CODE_POINT)
        .unwrap_or(0)
        .saturating_add(1);
    let mut values: Vec<Option<&'static str>> = vec![None; size];
    let mut set = |a: u32, b: u32, v: &'static str| {
        for c in a..=b {
            if let Some(slot) = values.get_mut(usize::try_from(c).unwrap_or(usize::MAX)) {
                *slot = Some(v);
            }
        }
    };
    for (i, l) in text.lines().enumerate() {
        let line = i.saturating_add(1);
        if let Some(rest) = l.strip_prefix("# @missing:") {
            let (r, v) = rest
                .split_once(';')
                .ok_or(format!("{file}:{line}: bad @missing line"))?;
            let (a, b) = range(r, file, line)?;
            set(a, b, short(v.trim(), line)?);
        }
    }
    for (line, f) in data_lines(text) {
        let (a, b) = range(f.first().copied().unwrap_or(""), file, line)?;
        set(a, b, short(f.get(1).copied().unwrap_or(""), line)?);
    }
    values
        .into_iter()
        .enumerate()
        .map(|(c, v)| v.ok_or(format!("{file}: no value for U+{c:04X}")))
        .collect()
}

/// Maximal runs of equal values: (first, last, value), skipping `skip`.
fn runs<T: Copy + PartialEq>(values: &[(u32, T)], skip: Option<T>) -> Vec<(u32, u32, T)> {
    let mut out: Vec<(u32, u32, T)> = Vec::new();
    for &(c, v) in values {
        if Some(v) == skip {
            continue;
        }
        match out.last_mut() {
            Some((_, last, value)) if *value == v && last.checked_add(1) == Some(c) => *last = c,
            _ => out.push((c, c, v)),
        }
    }
    out
}

const BIDI_CLASSES: &[(&str, &str)] = &[
    ("Left_To_Right", "L"),
    ("Right_To_Left", "R"),
    ("Arabic_Letter", "AL"),
    ("European_Number", "EN"),
    ("European_Separator", "ES"),
    ("European_Terminator", "ET"),
    ("Arabic_Number", "AN"),
    ("Common_Separator", "CS"),
    ("Nonspacing_Mark", "NSM"),
    ("Boundary_Neutral", "BN"),
    ("Paragraph_Separator", "B"),
    ("Segment_Separator", "S"),
    ("White_Space", "WS"),
    ("Other_Neutral", "ON"),
    ("Left_To_Right_Embedding", "LRE"),
    ("Left_To_Right_Override", "LRO"),
    ("Right_To_Left_Embedding", "RLE"),
    ("Right_To_Left_Override", "RLO"),
    ("Pop_Directional_Format", "PDF"),
    ("Left_To_Right_Isolate", "LRI"),
    ("Right_To_Left_Isolate", "RLI"),
    ("First_Strong_Isolate", "FSI"),
    ("Pop_Directional_Isolate", "PDI"),
];

const JOINING_TYPES: &[(&str, &str)] = &[
    ("Non_Joining", "U"),
    ("Join_Causing", "C"),
    ("Dual_Joining", "D"),
    ("Left_Joining", "L"),
    ("Right_Joining", "R"),
    ("Transparent", "T"),
];

fn generate(dir: &Path) -> Result<String, String> {
    let idna = idna_rows(&read(dir, "IdnaMappingTable.txt")?)?;
    let ucd = unicode_data(&read(dir, "UnicodeData.txt")?)?;
    let exclusions = binary_property(
        &read(dir, "DerivedNormalizationProps.txt")?,
        "DerivedNormalizationProps.txt",
        "Full_Composition_Exclusion",
    )?;
    let bidi = enumerated_property(
        &read(dir, "DerivedBidiClass.txt")?,
        "DerivedBidiClass.txt",
        BIDI_CLASSES,
    )?;
    let joining = enumerated_property(
        &read(dir, "DerivedJoiningType.txt")?,
        "DerivedJoiningType.txt",
        JOINING_TYPES,
    )?;

    let mut out = String::new();
    out.push_str(HEADER);

    // IDNA mapping table.
    let mut mapping_data: Vec<u32> = Vec::new();
    let mut rows = Vec::new();
    for r in &idna {
        let start = mapping_data.len();
        mapping_data.extend(&r.mapping);
        rows.push(format!(
            "IdnaRow {{ first: 0x{:X}, last: 0x{:X}, status: Status::{}, mapping_start: {start}, mapping_len: {} }}",
            r.first,
            r.last,
            r.status,
            r.mapping.len()
        ));
    }
    let table = |out: &mut String, t: Table<'_>| emit(out, &t);
    table(
        &mut out,
        Table {
            name: "idna_mapping",
            doc: "IdnaMappingTable.txt, one row per data line.",
            row_type: "IdnaRow",
            row_bytes: 20,
            rows,
        },
    );
    table(
        &mut out,
        u32_table(
            "idna_mapping_data",
            "The mappings of the IDNA mapping table, concatenated.",
            &mapping_data,
        ),
    );

    // Full canonical decompositions.
    let mut decomposition_data: Vec<u32> = Vec::new();
    let mut rows = Vec::new();
    for &c in ucd.decomposition.keys() {
        let full = full_decomposition(&ucd.decomposition, c, 0)?;
        rows.push(format!(
            "DecompositionRow {{ code_point: 0x{c:X}, start: {}, len: {} }}",
            decomposition_data.len(),
            full.len()
        ));
        decomposition_data.extend(full);
    }
    table(
        &mut out,
        Table {
            name: "decomposition",
            doc: "Full canonical decompositions (D68), by code point.",
            row_type: "DecompositionRow",
            row_bytes: 12,
            rows,
        },
    );
    table(
        &mut out,
        u32_table(
            "decomposition_data",
            "The full canonical decompositions, concatenated.",
            &decomposition_data,
        ),
    );

    // Primary composites.
    let mut composition: Vec<(u32, u32, u32)> = ucd
        .decomposition
        .iter()
        .filter(|(c, m)| m.len() == 2 && exclusions.binary_search(c).is_err())
        .filter_map(|(&c, m)| Some((*m.first()?, *m.get(1)?, c)))
        .collect();
    composition.sort_unstable();
    if composition.windows(2).any(|w| match w {
        [a, b] => (a.0, a.1) == (b.0, b.1),
        _ => false,
    }) {
        return Err("two primary composites share a decomposition".into());
    }
    table(
        &mut out,
        Table {
            name: "composition",
            doc: "Primary composites other than Hangul (D114), by (L, C).",
            row_type: "CompositionRow",
            row_bytes: 12,
            rows: composition
                .iter()
                .map(|(l, c, p)| {
                    format!(
                        "CompositionRow {{ first: 0x{l:X}, second: 0x{c:X}, composite: 0x{p:X} }}"
                    )
                })
                .collect(),
        },
    );

    // Canonical_Combining_Class.
    let ccc: Vec<(u32, u8)> = ucd.ccc.iter().map(|(&c, &v)| (c, v)).collect();
    table(
        &mut out,
        Table {
            name: "combining_class",
            doc: "Non-zero Canonical_Combining_Class, as ranges.",
            row_type: "ClassRow",
            row_bytes: 12,
            rows: runs(&ccc, None)
                .iter()
                .map(|(a, b, v)| {
                    format!("ClassRow {{ first: 0x{a:X}, last: 0x{b:X}, class: {v} }}")
                })
                .collect(),
        },
    );

    // General_Category=Mark.
    let marks: Vec<(u32, ())> = ucd.marks.iter().map(|&c| (c, ())).collect();
    table(
        &mut out,
        Table {
            name: "mark",
            doc: "General_Category=Mark (Mn, Mc, Me), as ranges.",
            row_type: "RangeRow",
            row_bytes: 8,
            rows: runs(&marks, None)
                .iter()
                .map(|(a, b, ())| format!("RangeRow {{ first: 0x{a:X}, last: 0x{b:X} }}"))
                .collect(),
        },
    );

    // Bidi_Class and Joining_Type, with UAX #44 long value names.
    let long = |names: &[(&'static str, &'static str)], v: &str| {
        names
            .iter()
            .find(|(_, short)| *short == v)
            .map_or(String::new(), |(l, _)| l.replace('_', ""))
    };
    let bidi: Vec<(u32, &str)> = (0..=MAX_CODE_POINT).zip(bidi).collect();
    table(
        &mut out,
        Table {
            name: "bidi_class",
            doc: "Bidi_Class, as ranges covering U+0000..U+10FFFF.",
            row_type: "BidiRow",
            row_bytes: 12,
            rows: runs(&bidi, None)
                .iter()
                .map(|(a, b, v)| {
                    format!(
                        "BidiRow {{ first: 0x{a:X}, last: 0x{b:X}, class: BidiClass::{} }}",
                        long(BIDI_CLASSES, v)
                    )
                })
                .collect(),
        },
    );
    let joining: Vec<(u32, &str)> = (0..=MAX_CODE_POINT).zip(joining).collect();
    table(&mut out, Table {
        name: "joining_type",
        doc: "Joining_Type other than U (Non_Joining), as ranges.",
        row_type: "JoiningRow",
        row_bytes: 12,
        rows: runs(&joining, Some("U"))
            .iter()
            .map(|(a, b, v)| {
                format!(
                    "JoiningRow {{ first: 0x{a:X}, last: 0x{b:X}, joining_type: JoiningType::{} }}",
                    long(JOINING_TYPES, v)
                )
            })
            .collect(),
    });
    out.push_str("} // verus!\n");
    Ok(out)
}

/// One generated table: its rows as Rust expressions.
pub(crate) struct Table<'a> {
    /// snake_case name; the constants are its SCREAMING_CASE.
    pub(crate) name: &'a str,
    pub(crate) doc: &'a str,
    pub(crate) row_type: &'a str,
    /// `size_of` the row type, to keep each chunk within clippy's
    /// `large_const_arrays` limit (16 KiB).
    pub(crate) row_bytes: usize,
    pub(crate) rows: Vec<String>,
}

fn u32_table<'a>(name: &'a str, doc: &'a str, values: &[u32]) -> Table<'a> {
    Table {
        name,
        doc,
        row_type: "u32",
        row_bytes: 4,
        rows: values.iter().map(|v| format!("0x{v:X}")).collect(),
    }
}

/// Each table is split into constant arrays of at most 16 000 bytes
/// (clippy's `large_const_arrays` allows 16 KiB; Verus can read only
/// constants, not statics, in specs). `<name>_at(i)` is the spec's view of
/// row `i`, and `<name>_at_exec(i)` returns it, proven equal.
pub(crate) fn emit(out: &mut String, t: &Table<'_>) {
    let upper = t.name.to_ascii_uppercase();
    let per_chunk = 16_000usize.checked_div(t.row_bytes).unwrap_or(1).max(1);
    let chunks: Vec<&[String]> = t.rows.chunks(per_chunk).collect();
    let _ = writeln!(out, "/// The number of rows in the {} table.", t.name);
    let _ = writeln!(out, "pub const {upper}_LEN: usize = {};\n", t.rows.len());
    for (k, chunk) in chunks.iter().enumerate() {
        let _ = writeln!(
            out,
            "/// {} (rows {} to {}.)",
            t.doc,
            k.saturating_mul(per_chunk),
            k.saturating_mul(per_chunk)
                .saturating_add(chunk.len())
                .saturating_sub(1)
        );
        let _ = writeln!(out, "#[verifier::opaque]");
        let _ = writeln!(
            out,
            "pub const {upper}_{k}: [{}; {}] = [",
            t.row_type,
            chunk.len()
        );
        if t.row_type == "u32" || t.row_type == "u8" {
            for line in chunk.chunks(12) {
                let _ = writeln!(out, "    {},", line.join(", "));
            }
        } else {
            for r in *chunk {
                let _ = writeln!(out, "    {r},");
            }
        }
        out.push_str("];\n\n");
    }
    // Spec view: total, with the dummy row outside the table.
    let dummy = dummy(t.row_type);
    let _ = writeln!(
        out,
        "/// Row `i` of the {} table: {} Outside the table, a fixed dummy row.",
        t.name, t.doc
    );
    let _ = writeln!(
        out,
        "pub open spec fn {}_at(i: int) -> {} {{\n    if i < 0 || i >= {upper}_LEN {{\n        {dummy}",
        t.name, t.row_type
    );
    for (k, _) in chunks.iter().enumerate() {
        let start = k.saturating_mul(per_chunk);
        let end = start.saturating_add(per_chunk);
        if k.saturating_add(1) == chunks.len() {
            let _ = writeln!(
                out,
                "    }} else {{\n        {upper}_{k}@[i - {start}]\n    }}"
            );
        } else {
            let _ = writeln!(
                out,
                "    }} else if i < {end} {{\n        {upper}_{k}@[i - {start}]"
            );
        }
    }
    out.push_str("}\n\n");
    // Exec access.
    let _ = writeln!(out, "/// Row `i` of the {} table.", t.name);
    let _ = writeln!(
        out,
        "pub fn {}_at_exec(i: usize) -> (r: {})\n    ensures\n        r == {}_at(i as int),\n{{",
        t.name, t.row_type, t.name
    );
    let _ = writeln!(
        out,
        "    if i >= {upper}_LEN {{\n        {dummy}\n    }}{}\n}}\n",
        exec_body(&upper, chunks.len(), per_chunk, &dummy)
    );
}

/// A value of the row type, for the `None` arm of `get` (unreachable:
/// the index is in range, which Verus checks).
fn dummy(row_type: &str) -> String {
    match row_type {
        "u32" | "u8" => "0".into(),
        "RuleRow" => "RuleRow { first: 0, count: 0, exception: false }".into(),
        "LabelRow" => "LabelRow { start: 0, len: 0 }".into(),
        "IdnaRow" => "IdnaRow { first: 0, last: 0, status: Status::Disallowed, mapping_start: 0, mapping_len: 0 }".into(),
        "DecompositionRow" => "DecompositionRow { code_point: 0, start: 0, len: 0 }".into(),
        "CompositionRow" => "CompositionRow { first: 0, second: 0, composite: 0 }".into(),
        "ClassRow" => "ClassRow { first: 0, last: 0, class: 0 }".into(),
        "RangeRow" => "RangeRow { first: 0, last: 0 }".into(),
        "BidiRow" => "BidiRow { first: 0, last: 0, class: BidiClass::LeftToRight }".into(),
        _ => "JoiningRow { first: 0, last: 0, joining_type: JoiningType::Transparent }".into(),
    }
}

/// The body of `<name>_at_exec`: pick the chunk, then the row.
fn exec_body(upper: &str, chunks: usize, per_chunk: usize, dummy: &str) -> String {
    let mut body = String::new();
    for k in 0..chunks {
        let start = k.saturating_mul(per_chunk);
        let end = start.saturating_add(per_chunk);
        let get = format!(
            "let chunk: &[_] = &{upper}_{k};\n        match chunk.get(i.saturating_sub({start})) {{\n            Some(r) => *r,\n            None => {dummy},\n        }}"
        );
        if k.saturating_add(1) == chunks {
            let _ = write!(body, " else {{\n        {get}\n    }}");
        } else {
            let _ = write!(body, " else if i < {end} {{\n        {get}\n    }}");
        }
    }
    body
}

const HEADER: &str = "\
//! The Unicode tables UTS #46 processing uses.
//!
// @generated by `cargo xtask tables` (xtask/src/unicode.rs) from
// crates/clazel-idna/data/unicode-18.0.0/ (Unicode 18.0.0; files, URLs and
// SHA-256 in SOURCE.md there). Do not edit: `cargo xtask check` fails if
// this differs from what the generator produces.
//
// What the generator derives (the proofs are relative to these tables):
// - IDNA_MAPPING: one row per data line of IdnaMappingTable.txt, in file
//   order (checked sorted, disjoint and covering U+0000..U+10FFFF), with
//   IDNA_MAPPING_DATA[mapping_start .. mapping_start + mapping_len] its
//   mapping (empty unless mapped or deviation).
// - DECOMPOSITION: each code point with a canonical Decomposition_Mapping
//   (UnicodeData.txt field 5 without a <tag>), sorted, with its full
//   canonical decomposition: the mapping with each code point replaced by
//   its own full canonical decomposition, recursively (Unicode §3.7 D68).
// - COMPOSITION: (L, C, P) for each P whose canonical Decomposition_Mapping
//   is exactly <L, C> and that is not Full_Composition_Exclusion
//   (DerivedNormalizationProps.txt), sorted by (L, C).
// - COMBINING_CLASS: maximal ranges of equal non-zero
//   Canonical_Combining_Class (UnicodeData.txt field 3).
// - MARK: maximal ranges of General_Category Mn, Mc or Me (field 2).
// - BIDI_CLASS: DerivedBidiClass.txt with its @missing defaults applied
//   first, as maximal ranges covering U+0000..U+10FFFF.
// - JOINING_TYPE: DerivedJoiningType.txt, maximal ranges of each type other
//   than U (Non_Joining, the @missing default).

use super::tables::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

";
