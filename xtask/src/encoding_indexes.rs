//! The Encoding Standard's labels table and single-byte indexes for
//! `clazel-encoding` (Phase 4 item 4.1; Encoding §4.2, §5, §9).
//!
//! The standard's `encodings.json` (its table of encodings and labels, §4.2)
//! and `indexes.json` (every index of §5) are vendored, byte for byte, under
//! `crates/clazel-encoding/data/encoding-<commit>/` with a `SOURCE.md` giving
//! the upstream commit, URL and SHA-256. This module turns them into two
//! committed Rust files of constant arrays, in the chunked opaque form of
//! `unicode.rs`:
//! - `crates/clazel-encoding/src/labels/data.rs`: the labels table;
//! - `crates/clazel-encoding/src/single_byte/data.rs`: the 27 single-byte
//!   indexes.
//!
//! `cargo xtask tables` writes them; `check` and `verify` fail if a vendored
//! file's hash differs from `SOURCE.md` or a committed file differs from
//! what this produces. The multi-byte indexes are vendored (they are in
//! the same `indexes.json`) and not generated: their decoders are item 4.4.
//!
//! The proofs are relative to these tables, so what this module derives is
//! kept to simple, stated steps (each is listed in the generated files'
//! headers):
//! - the encodings are numbered in the order `encodings.json` lists them,
//!   which must be [`ENCODINGS`] (the order of `spec::Encoding`, so a
//!   reordered upstream file fails here rather than mislabelling);
//! - one label row per label, sorted by its bytes, with the number of the
//!   encoding it belongs to; then each encoding's name, in the same
//!   character array;
//! - one table of 128 entries per single-byte index (`indexes.json` arrays
//!   of length 128), entry `p` the code point for pointer `p`, or
//!   [`NULL`] where the index has none.
//!
//! The single-byte indexes are also checked against a second body's
//! tables: the Unicode Consortium's mapping files for the ISO 8859,
//! Microsoft and KOI8 encodings, vendored under
//! `crates/clazel-encoding/data/unicode-mappings/` ([`check_mappings`]).
//! Every difference is listed in [`DIFFERENCES`] or follows the one stated
//! rule for Microsoft's undefined bytes, and each listed difference must
//! occur. A swapped or missing entry in `indexes.json` fails here.
//!
//! It also rejects, so the tables can rely on it: a label that is empty,
//! longer than 255, or has a byte that is not lowercase ASCII, a digit or
//! one of `-_.:`; a duplicate label; an encoding whose ASCII-lowercased name
//! is not one of its labels (§4.2 notes that it always is); an index entry
//! that is below 0x80, a surrogate, above U+10FFFF, or a duplicate within
//! its index; a single-byte index other than the 27 of [`SINGLE_BYTE`].
//! Nothing relies on these checks being right: `labels/lemmas.rs` and
//! `single_byte/lemmas.rs` prove what is used of them.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::reviews;
use crate::unicode::{Table, emit};
use crate::workspace;

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-encoding/data/encoding-dd794344";
/// The generated labels table, relative to the repository root.
const LABELS_OUTPUT: &str = "crates/clazel-encoding/src/labels/data.rs";
/// The generated single-byte indexes, relative to the repository root.
const INDEXES_OUTPUT: &str = "crates/clazel-encoding/src/single_byte/data.rs";
/// The files `SOURCE.md` must list, besides itself and LICENSE.
const FILES: &[&str] = &["encodings.json", "indexes.json"];
/// The vendored Unicode mapping files, relative to the repository root.
const MAPPINGS_DIR: &str = "crates/clazel-encoding/data/unicode-mappings";
/// Each mapping file and the single-byte index it describes.
const MAPPINGS: &[(&str, &str)] = &[
    ("ibm866", "CP866.TXT"),
    ("iso-8859-2", "8859-2.TXT"),
    ("iso-8859-3", "8859-3.TXT"),
    ("iso-8859-4", "8859-4.TXT"),
    ("iso-8859-5", "8859-5.TXT"),
    ("iso-8859-6", "8859-6.TXT"),
    ("iso-8859-7", "8859-7.TXT"),
    ("iso-8859-8", "8859-8.TXT"),
    ("iso-8859-10", "8859-10.TXT"),
    ("iso-8859-13", "8859-13.TXT"),
    ("iso-8859-14", "8859-14.TXT"),
    ("iso-8859-15", "8859-15.TXT"),
    ("iso-8859-16", "8859-16.TXT"),
    ("koi8-r", "KOI8-R.TXT"),
    ("koi8-u", "KOI8-U.TXT"),
    ("windows-874", "CP874.TXT"),
    ("windows-1250", "CP1250.TXT"),
    ("windows-1251", "CP1251.TXT"),
    ("windows-1252", "CP1252.TXT"),
    ("windows-1253", "CP1253.TXT"),
    ("windows-1254", "CP1254.TXT"),
    ("windows-1255", "CP1255.TXT"),
    ("windows-1256", "CP1256.TXT"),
    ("windows-1257", "CP1257.TXT"),
    ("windows-1258", "CP1258.TXT"),
];
/// The single-byte indexes with no second body's file vendored (Apple's
/// files grant no permission to redistribute; see that directory's
/// `SOURCE.md`).
const NO_MAPPING: &[&str] = &["macintosh", "x-mac-cyrillic"];
/// Differences between the Encoding Standard's index and the mapping file,
/// besides the rule for Microsoft's undefined bytes: (index, byte, the
/// standard's code point, the file's code point or `None` if undefined,
/// why).
const DIFFERENCES: &[(&str, u8, u32, Option<u32>, &str)] = &[
    (
        "windows-1255",
        0xCA,
        0x05BA,
        None,
        "HEBREW POINT HOLAM HASER FOR VAV, added after Microsoft's file",
    ),
    (
        "koi8-u",
        0xAE,
        0x045E,
        Some(0x255D),
        "Belarusian short u (KOI8-RU) where RFC 2319 has box drawing",
    ),
    (
        "koi8-u",
        0xBE,
        0x040E,
        Some(0x256C),
        "Belarusian short U (KOI8-RU) where RFC 2319 has box drawing",
    ),
];

/// The encodings in the order of `encodings.json` (and of the standard's
/// table in §4.2), which is the order of `spec::Encoding`'s variants.
pub const ENCODINGS: [&str; 40] = [
    "UTF-8",
    "IBM866",
    "ISO-8859-2",
    "ISO-8859-3",
    "ISO-8859-4",
    "ISO-8859-5",
    "ISO-8859-6",
    "ISO-8859-7",
    "ISO-8859-8",
    "ISO-8859-8-I",
    "ISO-8859-10",
    "ISO-8859-13",
    "ISO-8859-14",
    "ISO-8859-15",
    "ISO-8859-16",
    "KOI8-R",
    "KOI8-U",
    "macintosh",
    "windows-874",
    "windows-1250",
    "windows-1251",
    "windows-1252",
    "windows-1253",
    "windows-1254",
    "windows-1255",
    "windows-1256",
    "windows-1257",
    "windows-1258",
    "x-mac-cyrillic",
    "GBK",
    "gb18030",
    "Big5",
    "EUC-JP",
    "ISO-2022-JP",
    "Shift_JIS",
    "EUC-KR",
    "replacement",
    "UTF-16BE",
    "UTF-16LE",
    "x-user-defined",
];

/// The single-byte indexes, by their `indexes.json` key, in the order of
/// the standard's table in §9 (ISO-8859-8-I shares `iso-8859-8`). Each
/// becomes the table `INDEX_<KEY>` (upper case, `-` as `_`).
pub const SINGLE_BYTE: [&str; 27] = [
    "ibm866",
    "iso-8859-2",
    "iso-8859-3",
    "iso-8859-4",
    "iso-8859-5",
    "iso-8859-6",
    "iso-8859-7",
    "iso-8859-8",
    "iso-8859-10",
    "iso-8859-13",
    "iso-8859-14",
    "iso-8859-15",
    "iso-8859-16",
    "koi8-r",
    "koi8-u",
    "macintosh",
    "windows-874",
    "windows-1250",
    "windows-1251",
    "windows-1252",
    "windows-1253",
    "windows-1254",
    "windows-1255",
    "windows-1256",
    "windows-1257",
    "windows-1258",
    "x-mac-cyrillic",
];

/// The table entry for a pointer the index does not have.
pub const NULL: u32 = 0xFFFF_FFFF;

/// Compare (or, with `write`, rewrite) the generated tables. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_sources(&dir, FILES);
    let mapping_files: Vec<&str> = MAPPINGS.iter().map(|(_, f)| *f).collect();
    problems.extend(check_sources(&PathBuf::from(MAPPINGS_DIR), &mapping_files));
    let mut notes = Vec::new();
    if !problems.is_empty() {
        return (problems, notes);
    }
    match std::fs::read_to_string(dir.join("indexes.json"))
        .map_err(|e| format!("indexes.json: {e}"))
        .and_then(|t| check_mappings(&t))
    {
        Ok(note) => notes.push(note),
        Err(e) => problems.push(format!("{MAPPINGS_DIR}: {e}")),
    }
    let read = |f: &str| std::fs::read_to_string(dir.join(f)).map_err(|e| format!("{f}: {e}"));
    let labels = read("encodings.json").and_then(|t| generate_labels(&t));
    let indexes = read("indexes.json").and_then(|t| generate_indexes(&t));
    for (output, fresh) in [(LABELS_OUTPUT, labels), (INDEXES_OUTPUT, indexes)] {
        let fresh = match fresh {
            Ok(f) => f,
            Err(e) => {
                problems.push(format!("{DATA_DIR}: {e}"));
                continue;
            }
        };
        let current = std::fs::read_to_string(output).ok();
        if current.as_deref() == Some(fresh.as_str()) {
            notes.push(format!("{output}: up to date"));
        } else if write {
            match std::fs::write(output, &fresh) {
                Ok(()) => notes.push(format!("{output}: written")),
                Err(e) => problems.push(format!("{output}: {e}")),
            }
        } else if current.is_none() {
            problems.push(format!("{output}: missing; run `cargo xtask tables`"));
        } else {
            problems.push(format!(
                "{output}: stale (differs from what xtask/src/encoding_indexes.rs produces); \
                 run `cargo xtask tables` and commit the result"
            ));
        }
    }
    (problems, notes)
}

/// Every vendored file is listed in `SOURCE.md` with its SHA-256, and
/// matches it; nothing else is in the directory.
fn check_sources(dir: &Path, files: &[&str]) -> Vec<String> {
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
    if !source.lines().any(|l| l.trim().starts_with("Commit:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"Commit:\" line"));
    }
    match std::fs::read_dir(dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !files.contains(&name.as_str()) && name != "SOURCE.md" && name != "LICENSE" {
                    problems.push(format!(
                        "{rel}/{name}: not an input of xtask/src/encoding_indexes.rs"
                    ));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

/// A label byte the generated table allows: lowercase ASCII letters,
/// digits, and `-_.:`.
fn label_byte(b: u8) -> bool {
    b.is_ascii_lowercase() || b.is_ascii_digit() || matches!(b, b'-' | b'_' | b'.' | b':')
}

/// A label and the number of its encoding.
type LabelRow = (String, u8);

/// Read and check `encodings.json`: label rows sorted by label, and the
/// encodings' names.
fn label_rows(text: &str) -> Result<(Vec<LabelRow>, Vec<String>), String> {
    let json: Value = serde_json::from_str(text).map_err(|e| e.to_string())?;
    let groups = json
        .as_array()
        .ok_or("encodings.json: expected a JSON array")?;
    let mut names = Vec::new();
    let mut rows: Vec<LabelRow> = Vec::new();
    for group in groups {
        let encodings = group
            .get("encodings")
            .and_then(Value::as_array)
            .ok_or("encodings.json: a group without an \"encodings\" array")?;
        for e in encodings {
            let name = e
                .get("name")
                .and_then(Value::as_str)
                .ok_or("encodings.json: an encoding without a \"name\"")?;
            let number = u8::try_from(names.len()).map_err(|e| e.to_string())?;
            if ENCODINGS.get(usize::from(number)) != Some(&name) {
                return Err(format!(
                    "encodings.json: encoding {number} is {name:?}, expected {:?} \
                     (the order of spec::Encoding)",
                    ENCODINGS.get(usize::from(number))
                ));
            }
            let labels = e
                .get("labels")
                .and_then(Value::as_array)
                .ok_or_else(|| format!("{name}: no \"labels\" array"))?;
            for l in labels {
                let l = l
                    .as_str()
                    .ok_or_else(|| format!("{name}: a label is not a string"))?;
                if l.is_empty() || l.len() > 255 || !l.bytes().all(label_byte) {
                    return Err(format!(
                        "{name}: label {l:?} is empty, longer than 255, or not lowercase ASCII \
                         letters, digits and -_.:"
                    ));
                }
                if rows.iter().any(|(r, _)| r == l) {
                    return Err(format!("{name}: duplicate label {l:?}"));
                }
                rows.push((l.to_owned(), number));
            }
            if !rows
                .iter()
                .any(|(r, n)| *n == number && *r == name.to_ascii_lowercase())
            {
                return Err(format!(
                    "{name}: its ASCII-lowercased name is not one of its labels"
                ));
            }
            names.push(name.to_owned());
        }
    }
    if names.len() != ENCODINGS.len() {
        return Err(format!(
            "encodings.json: {} encodings, expected {}",
            names.len(),
            ENCODINGS.len()
        ));
    }
    rows.sort();
    Ok((rows, names))
}

fn generate_labels(text: &str) -> Result<String, String> {
    let (rows, names) = label_rows(text)?;
    let mut chars: Vec<u8> = Vec::new();
    let mut starts = Vec::new();
    let mut lens = Vec::new();
    let mut encodings = Vec::new();
    for (label, number) in &rows {
        starts.push(u32::try_from(chars.len()).map_err(|e| e.to_string())?);
        lens.push(u8::try_from(label.len()).map_err(|e| e.to_string())?);
        chars.extend(label.bytes());
        encodings.push(*number);
    }
    let mut name_starts = Vec::new();
    let mut name_lens = Vec::new();
    for name in &names {
        name_starts.push(u32::try_from(chars.len()).map_err(|e| e.to_string())?);
        name_lens.push(u8::try_from(name.len()).map_err(|e| e.to_string())?);
        chars.extend(name.bytes());
    }
    let mut out = String::from(LABELS_HEADER);
    let dec = |v: &[u32]| v.iter().map(|c| format!("{c}")).collect();
    let dec8 = |v: &[u8]| v.iter().map(|c| format!("{c}")).collect();
    emit(
        &mut out,
        &Table {
            name: "label_start",
            doc: "Where each label row's label starts in LABEL_CHARS.",
            row_type: "u32",
            row_bytes: 4,
            rows: dec(&starts),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "label_len",
            doc: "The length of each label row's label.",
            row_type: "u8",
            row_bytes: 1,
            rows: dec8(&lens),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "label_encoding",
            doc: "The number of each label row's encoding (the order of spec::Encoding).",
            row_type: "u8",
            row_bytes: 1,
            rows: dec8(&encodings),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "name_start",
            doc: "By encoding number: where its name starts in LABEL_CHARS.",
            row_type: "u32",
            row_bytes: 4,
            rows: dec(&name_starts),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "name_len",
            doc: "By encoding number: the length of its name.",
            row_type: "u8",
            row_bytes: 1,
            rows: dec8(&name_lens),
        },
    );
    emit(
        &mut out,
        &Table {
            name: "label_chars",
            doc: "The labels' characters, row after row, then the names' (ASCII).",
            row_type: "u8",
            row_bytes: 1,
            rows: chars.iter().map(|c| format!("0x{c:X}")).collect(),
        },
    );
    let _ = writeln!(out, "}} // verus!");
    Ok(out)
}

/// Read and check the 27 single-byte indexes of `indexes.json`.
fn single_byte_indexes(text: &str) -> Result<Vec<(&'static str, Vec<u32>)>, String> {
    let json: Value = serde_json::from_str(text).map_err(|e| e.to_string())?;
    let obj = json
        .as_object()
        .ok_or("indexes.json: expected a JSON object")?;
    for (key, value) in obj {
        let single = value.as_array().is_some_and(|a| a.len() == 128);
        if single != SINGLE_BYTE.contains(&key.as_str()) {
            return Err(format!(
                "indexes.json: {key:?} is {}a 128-entry index but {}in SINGLE_BYTE",
                if single { "" } else { "not " },
                if single { "not " } else { "" }
            ));
        }
    }
    let mut out = Vec::new();
    for key in SINGLE_BYTE {
        let entries = obj
            .get(key)
            .and_then(Value::as_array)
            .ok_or_else(|| format!("indexes.json: no index {key:?}"))?;
        let mut table = Vec::new();
        for (pointer, v) in entries.iter().enumerate() {
            let cp = match v {
                Value::Null => NULL,
                v => {
                    let cp = v
                        .as_u64()
                        .and_then(|n| u32::try_from(n).ok())
                        .ok_or_else(|| format!("{key}[{pointer}]: not a number or null"))?;
                    if cp < 0x80 || (0xD800..=0xDFFF).contains(&cp) || cp > 0x10_FFFF {
                        return Err(format!(
                            "{key}[{pointer}]: {cp:#X} is ASCII, a surrogate or out of range"
                        ));
                    }
                    if table.contains(&cp) {
                        return Err(format!("{key}[{pointer}]: {cp:#X} appears twice"));
                    }
                    cp
                }
            };
            table.push(cp);
        }
        out.push((key, table));
    }
    Ok(out)
}

fn generate_indexes(text: &str) -> Result<String, String> {
    let indexes = single_byte_indexes(text)?;
    let mut out = String::from(INDEXES_HEADER);
    for (key, table) in &indexes {
        let name = format!("index_{}", key.replace('-', "_"));
        let doc = format!("index {key}: the code point for each pointer, or NULL.");
        emit(
            &mut out,
            &Table {
                name: &name,
                doc: &doc,
                row_type: "u32",
                row_bytes: 4,
                rows: table.iter().map(|c| format!("0x{c:X}")).collect(),
            },
        );
    }
    let _ = writeln!(out, "}} // verus!");
    Ok(out)
}

/// Read a Unicode mapping file (format A: lines of `0xBB<TAB>0xCCCC<TAB>#
/// name`, `#` comments, an undefined byte with no second column; a final
/// DOS end-of-file byte 0x1A, which `CP866.TXT` has, ends the file): the
/// code point for each byte it defines.
fn read_mapping(file: &str, text: &str) -> Result<Vec<Option<u32>>, String> {
    let mut table = vec![None; 256];
    for (n, line) in text.lines().enumerate() {
        let data = line.split('#').next().unwrap_or_default().trim();
        if data == "\u{1a}" {
            break;
        }
        if data.is_empty() {
            continue;
        }
        let mut cols = data.split_whitespace();
        let hex = |s: &str| {
            s.strip_prefix("0x")
                .and_then(|h| u32::from_str_radix(h, 16).ok())
                .ok_or_else(|| format!("{file}:{}: bad number {s:?}", n.saturating_add(1)))
        };
        let byte = cols.next().map(hex).transpose()?.unwrap_or(0);
        let cp = cols.next().map(hex).transpose()?;
        if cols.next().is_some() {
            return Err(format!(
                "{file}:{}: more than two columns",
                n.saturating_add(1)
            ));
        }
        let slot = usize::try_from(byte)
            .ok()
            .and_then(|b| table.get_mut(b))
            .ok_or_else(|| {
                format!(
                    "{file}:{}: byte {byte:#X} out of range",
                    n.saturating_add(1)
                )
            })?;
        if slot.is_some() {
            return Err(format!(
                "{file}:{}: byte {byte:#X} listed twice",
                n.saturating_add(1)
            ));
        }
        *slot = cp;
    }
    Ok(table)
}

/// Check each single-byte index against its Unicode mapping file. Returns
/// a note with the counts.
fn check_mappings(indexes_json: &str) -> Result<String, String> {
    let indexes = single_byte_indexes(indexes_json)?;
    let mut problems = Vec::new();
    let (mut same, mut c1, mut listed) = (0usize, 0usize, 0usize);
    for (key, index) in &indexes {
        let Some((_, file)) = MAPPINGS.iter().find(|(k, _)| k == key) else {
            if !NO_MAPPING.contains(key) {
                problems.push(format!("{key}: no mapping file and not in NO_MAPPING"));
            }
            continue;
        };
        let text = std::fs::read_to_string(PathBuf::from(MAPPINGS_DIR).join(file))
            .map_err(|e| format!("{file}: {e}"))?;
        let theirs = read_mapping(file, &text)?;
        for (byte, cp) in theirs.iter().enumerate().take(0x80) {
            if cp.is_some_and(|c| usize::try_from(c).ok() != Some(byte)) {
                problems.push(format!("{file}: byte {byte:#04X} is not ASCII"));
            }
        }
        for (pointer, ours) in index.iter().enumerate() {
            let byte = pointer.saturating_add(0x80);
            let ours = (*ours != NULL).then_some(*ours);
            let theirs = theirs.get(byte).copied().flatten();
            let b = u8::try_from(byte).map_err(|e| e.to_string())?;
            if ours == theirs {
                same = same.saturating_add(1);
            } else if key.starts_with("windows-")
                && theirs.is_none()
                && ours.and_then(|c| usize::try_from(c).ok()) == Some(byte)
                && (0x80..=0x9F).contains(&byte)
            {
                // Microsoft leaves the byte undefined; the Encoding
                // Standard maps it to the C1 control of the same value.
                c1 = c1.saturating_add(1);
            } else if DIFFERENCES
                .iter()
                .any(|(k, db, o, t, _)| k == key && *db == b && Some(*o) == ours && *t == theirs)
            {
                listed = listed.saturating_add(1);
            } else {
                problems.push(format!(
                    "{key} byte {byte:#04X}: indexes.json has {ours:X?}, {file} has {theirs:X?}, \
                     and DIFFERENCES does not list it"
                ));
            }
        }
    }
    if listed != DIFFERENCES.len() {
        problems.push(format!(
            "{} of the {} listed DIFFERENCES occur; remove the ones that no longer do",
            listed,
            DIFFERENCES.len()
        ));
    }
    if problems.is_empty() {
        Ok(format!(
            "single-byte indexes against the Unicode mapping files: {same} entries agree, \
             {c1} undefined in Microsoft's files are C1 controls, {listed} listed differences; \
             no second body's file for {}",
            NO_MAPPING.join(", ")
        ))
    } else {
        Err(problems.join("; "))
    }
}

const LABELS_HEADER: &str = "\
//! The Encoding Standard's table of encodings and labels (§4.2).
//!
// @generated by `cargo xtask tables` (xtask/src/encoding_indexes.rs) from
// crates/clazel-encoding/data/encoding-dd794344/ (the whatwg/encoding commit
// and SHA-256 of encodings.json are in SOURCE.md there). Do not edit: `cargo
// xtask check` fails if this differs from what the generator produces.
//
// What the generator derives (the proofs are relative to these tables):
// - Encodings are numbered 0 to 39 in the order encodings.json lists them,
//   which is the order of the standard's table and of spec::Encoding.
// - One label row per label in encodings.json, sorted by the label's bytes:
//   228 rows. Row i's label is LABEL_CHARS[LABEL_START[i] .. LABEL_START[i]
//   + LABEL_LEN[i]], and LABEL_ENCODING[i] is the number of the encoding it
//   is listed under.
// - Encoding n's name is LABEL_CHARS[NAME_START[n] .. NAME_START[n] +
//   NAME_LEN[n]], as encodings.json gives it (with its capitals).
// - Checked when generating, and not trusted (labels/lemmas.rs proves what
//   it uses): every label is non-empty, at most 255 long, lowercase ASCII
//   letters, digits and -_.:, and unique; every encoding's ASCII-lowercased
//   name is one of its labels.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

";

const INDEXES_HEADER: &str = "\
//! The Encoding Standard's single-byte indexes (§5, as §9 uses them).
//!
// @generated by `cargo xtask tables` (xtask/src/encoding_indexes.rs) from
// crates/clazel-encoding/data/encoding-dd794344/ (the whatwg/encoding commit
// and SHA-256 of indexes.json are in SOURCE.md there). Do not edit: `cargo
// xtask check` fails if this differs from what the generator produces.
//
// What the generator derives (the proofs are relative to these tables):
// - One table per 128-entry array of indexes.json: INDEX_<KEY> for the key
//   with `-` as `_` (27 tables; ISO-8859-8-I reads INDEX_ISO_8859_8).
// - Entry p is the code point for pointer p (\"index code point\"), or
//   0xFFFFFFFF where the array has null (the pointer is not in the index).
// - Checked when generating, and not trusted (single_byte/lemmas.rs proves
//   what it uses): no entry is below 0x80, a surrogate or above U+10FFFF,
//   and no code point appears twice in one index.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

";
