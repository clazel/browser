//! WPT's form encoding tests, as tables: `url/urlencoded-parser.any.js` (a
//! literal array of (input, parsed pairs)) and, from
//! `html/semantics/forms/form-submission-0/`, `urlencoded2.window.js`,
//! `text-plain.window.js` and `multipart-formdata.window.js` (each a list of
//! `formTest({ name, value, expected, formEncoding, description })` calls).
//!
//! The form tests build a form with one hidden control (or add the entry in
//! a `formdata` event) and submit it into a frame; a call whose `value` is a
//! `new File(...)` needs a file input and is skipped and counted. Every other
//! call is converted: its `name` and `value` are strings (a lone surrogate
//! stays a lone surrogate, as in JavaScript), `formEncoding` defaults to
//! `utf-8`, and `expected` is the isomorphic-decoded body (for
//! `multipart/form-data`, the page builds the body from `{ name, value }`
//! and the first line of the actual body, the boundary; both are kept).
//! The converter fails on anything it does not recognise, so an upstream
//! change cannot be half-read.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Lit, Node, Parser, find_all};

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "urlencoded-parser.any.js",
    "urlencoded2.window.js",
    "text-plain.window.js",
    "multipart-formdata.window.js",
];

/// Text each form test page must contain once, so that what the converter
/// assumes about its helper is still true.
const REQUIRED: &[(&str, &str)] = &[
    (
        "urlencoded2.window.js",
        "formSubmissionTemplate(\"application/x-www-form-urlencoded\")",
    ),
    (
        "text-plain.window.js",
        "formSubmissionTemplate(\"text/plain\")",
    ),
    (
        "multipart-formdata.window.js",
        "formSubmissionTemplate(\n  \"multipart/form-data\",",
    ),
];

/// A code point string, lone surrogates kept as themselves.
fn code_points(units: &[u16]) -> Vec<u32> {
    char::decode_utf16(units.iter().copied())
        .map(|r| r.map_or_else(|e| u32::from(e.unpaired_surrogate()), u32::from))
        .collect()
}

fn lit(units: &[u16]) -> String {
    let v: Vec<String> = code_points(units)
        .iter()
        .map(|c| format!("0x{c:04X}"))
        .collect();
    format!("&[{}]", v.join(", "))
}

struct FormCase {
    line: usize,
    name: Vec<u16>,
    value: Vec<u16>,
    encoding: String,
    /// The expected body; for multipart, the expected field name.
    a: Vec<u16>,
    /// For multipart, the expected field value.
    b: Vec<u16>,
    description: Vec<u16>,
}

struct ParserCase {
    input: Vec<u16>,
    pairs: Vec<(Vec<u16>, Vec<u16>)>,
}

fn form_cases(file: &str, source: &str, multipart: bool) -> Result<(Vec<FormCase>, usize), String> {
    let starts = find_all(source, "formTest({");
    let mut cases = Vec::new();
    let mut skipped = 0usize;
    for (k, &after) in starts.iter().enumerate() {
        let mut p = Parser::at(source, after.saturating_sub(1));
        match p.literal() {
            Ok(node) => {
                let at = |e: String| format!("{file}: {e}");
                let name = node.field("name").and_then(Node::str_units).map_err(at)?;
                let value = node.field("value").and_then(Node::str_units);
                let value = value.map_err(|e| format!("{file}: {e}"))?;
                let encoding = match node.field("formEncoding") {
                    Ok(n) => n.string()?,
                    Err(_) => "utf-8".to_owned(),
                };
                let description = node.field("description")?.str_units()?;
                let expected = node.field("expected")?;
                let (a, b) = if multipart {
                    if node.field("expected")?.field("filename").is_ok() {
                        return Err(format!(
                            "{file}:{}: a filename expected, but the value is a string",
                            node.line
                        ));
                    }
                    (
                        expected.field("name")?.str_units()?.to_vec(),
                        expected.field("value")?.str_units()?.to_vec(),
                    )
                } else {
                    (expected.str_units()?.to_vec(), Vec::new())
                };
                cases.push(FormCase {
                    line: node.line,
                    name: name.to_vec(),
                    value: value.to_vec(),
                    encoding,
                    a,
                    b,
                    description: description.to_vec(),
                });
            }
            Err(e) => {
                let from = after;
                let to = starts
                    .get(k.saturating_add(1))
                    .copied()
                    .unwrap_or(usize::MAX);
                let region: String = source
                    .chars()
                    .skip(from)
                    .take(to.saturating_sub(from))
                    .collect();
                if region.contains("new File(") {
                    skipped = skipped.saturating_add(1);
                } else {
                    return Err(format!("{file}: {e}"));
                }
            }
        }
    }
    if cases.is_empty() {
        return Err(format!("{file}: no formTest calls"));
    }
    Ok((cases, skipped))
}

fn parser_cases(source: &str) -> Result<Vec<ParserCase>, String> {
    let end = source
        .find("].forEach")
        .ok_or("urlencoded-parser.any.js: no `].forEach`")?;
    let text: String = source
        .chars()
        .take(
            source
                .get(..end)
                .map_or(0, |s| s.chars().count())
                .saturating_add(1),
        )
        .collect();
    let root = Parser::new(&text).literal()?;
    let mut out = Vec::new();
    for row in root.array()? {
        let input = row.field("input")?.str_units()?.to_vec();
        let mut pairs = Vec::new();
        for pair in row.field("output")?.array()? {
            let [n, v] = pair.array()? else {
                return Err(format!("line {}: expected a pair", pair.line));
            };
            pairs.push((n.str_units()?.to_vec(), v.str_units()?.to_vec()));
        }
        out.push(ParserCase { input, pairs });
    }
    if matches!(root.lit, Lit::Arr(ref a) if a.is_empty()) {
        return Err("urlencoded-parser.any.js: no rows".into());
    }
    Ok(out)
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let read = |f: &str| std::fs::read_to_string(dir.join(f)).map_err(|e| format!("{f}: {e}"));
    for (file, needle) in REQUIRED {
        if read(file)?.matches(needle).count() != 1 {
            return Err(format!(
                "{file}: expected {needle:?} exactly once; the test changed upstream"
            ));
        }
    }
    let parser = parser_cases(&read("urlencoded-parser.any.js")?)?;
    let (urlencoded, u_skip) = form_cases(
        "urlencoded2.window.js",
        &read("urlencoded2.window.js")?,
        false,
    )?;
    let (plain, p_skip) = form_cases(
        "text-plain.window.js",
        &read("text-plain.window.js")?,
        false,
    )?;
    let (multi, m_skip) = form_cases(
        "multipart-formdata.window.js",
        &read("multipart-formdata.window.js")?,
        true,
    )?;

    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-form-encodings/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_form_encodings.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-form-encodings/SOURCE.md.\n\
         // Every string is code points (a lone surrogate stays one).\n",
    );
    out.push_str("const PARSER: &[ParserCase] = &[\n");
    for c in &parser {
        let pairs: Vec<String> = c
            .pairs
            .iter()
            .map(|(n, v)| format!("({}, {})", lit(n), lit(v)))
            .collect();
        writeln!(
            out,
            "    ParserCase {{ input: {}, pairs: &[{}] }},",
            lit(&c.input),
            pairs.join(", ")
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    for (name, cases, skip) in [
        ("URLENCODED", &urlencoded, u_skip),
        ("TEXT_PLAIN", &plain, p_skip),
        ("MULTIPART", &multi, m_skip),
    ] {
        writeln!(out, "const {name}_FILE_CASES_SKIPPED: usize = {skip};")
            .map_err(|e| e.to_string())?;
        writeln!(out, "const {name}: &[FormCase] = &[").map_err(|e| e.to_string())?;
        for c in cases {
            writeln!(
                out,
                "    FormCase {{ line: {}, name: {}, value: {}, encoding: {:?}, a: {}, b: {}, description: {} }},",
                c.line,
                lit(&c.name),
                lit(&c.value),
                c.encoding,
                lit(&c.a),
                lit(&c.b),
                lit(&c.description)
            )
            .map_err(|e| e.to_string())?;
        }
        out.push_str("];\n");
    }
    Ok(out)
}
