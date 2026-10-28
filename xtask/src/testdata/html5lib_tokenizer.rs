//! html5lib-tests `tokenizer/*.test`: the HTML tokenizer cases, as a table
//! of (input, initial states, last start tag, expected tokens).
//!
//! Each file is a JSON object with one member, `tests` (or
//! `xmlViolationTests` in `xmlViolation.test`, whose cases expect the
//! "coercing an HTML DOM into an infoset" tweaks on top of tokenization),
//! an array of objects with `description`, `input` and `output`, and
//! optionally `initialStates`, `lastStartTag`, `doubleEscaped` and
//! `errors`. The format is the vendored `README.md`'s, and the converter
//! fails on anything else:
//! - `doubleEscaped` cases are unescaped here, in `input` and in every
//!   string of `output`: each `\uHHHH` becomes the code point HHHH (the
//!   README's only rule; a surrogate stays a surrogate);
//! - an omitted `initialStates` is `["Data state"]`; each state is one of
//!   the README's six names;
//! - `output` tokens are `["DOCTYPE", name, public, system, correctness]`,
//!   `["StartTag", name, {attributes}]` with an optional fourth `true`,
//!   `["EndTag", name]`, `["Comment", data]`,
//!   `["ProcessingInstruction", target, data]` (three entries, as the
//!   cases have them; the README still shows two) and `["Character", data]`;
//!   attributes are converted sorted by name (a JSON object has no order,
//!   and the test compares them as a map);
//! - `errors` is read and ignored: parse errors are not modelled (Phase 4
//!   item 4.6), which the generated file says.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "README.md",
    "contentModelFlags.test",
    "domjs.test",
    "entities.test",
    "escapeFlag.test",
    "namedEntities.test",
    "numericEntities.test",
    "pendingSpecChanges.test",
    "test1.test",
    "test2.test",
    "test3.test",
    "test4.test",
    "unicodeChars.test",
    "unicodeCharsProblematic.test",
    "xmlViolation.test",
];

/// Keys a case may have.
const KEYS: &[&str] = &[
    "description",
    "input",
    "output",
    "initialStates",
    "lastStartTag",
    "doubleEscaped",
    "errors",
];

/// The README's initial state names, and the generated table's names.
const STATES: &[(&str, &str)] = &[
    ("Data state", "Data"),
    ("PLAINTEXT state", "Plaintext"),
    ("RCDATA state", "Rcdata"),
    ("RAWTEXT state", "Rawtext"),
    ("Script data state", "ScriptData"),
    ("CDATA section state", "CdataSection"),
];

/// Lines of the vendored README that say what a case means; the
/// conversion fails if one of them is no longer there.
const README_LINES: &[&str] = &[
    "All adjacent character tokens are coalesced into a single",
    "into the corresponding Unicode code point. (Note that this option also",
    "`public_id` and `system_id` are either strings or `null`. `correctness`",
];

/// `s` as code points, with each `\uHHHH` replaced by U+HHHH if `double`.
fn code_points(s: &str, double: bool) -> Result<Vec<u32>, String> {
    let chars: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(&c) = chars.get(i) {
        if double && c == '\\' && chars.get(i.saturating_add(1)) == Some(&'u') {
            let hex: String = chars
                .get(i.saturating_add(2)..i.saturating_add(6))
                .ok_or_else(|| format!("{s:?}: truncated \\u escape"))?
                .iter()
                .collect();
            let v = u32::from_str_radix(&hex, 16)
                .map_err(|_| format!("{s:?}: bad \\u escape {hex:?}"))?;
            out.push(v);
            i = i.saturating_add(6);
        } else {
            out.push(u32::from(c));
            i = i.saturating_add(1);
        }
    }
    Ok(out)
}

fn cps(s: &str, double: bool) -> Result<String, String> {
    let items: Vec<String> = code_points(s, double)?
        .iter()
        .map(|c| format!("0x{c:X}"))
        .collect();
    Ok(format!("&[{}]", items.join(", ")))
}

fn opt_cps(v: &Value, double: bool, what: &str) -> Result<String, String> {
    match v {
        Value::Null => Ok("None".into()),
        Value::String(s) => Ok(format!("Some({})", cps(s, double)?)),
        _ => Err(format!("{what}: not a string or null")),
    }
}

fn string<'a>(v: Option<&'a Value>, what: &str) -> Result<&'a str, String> {
    v.and_then(Value::as_str)
        .ok_or_else(|| format!("{what}: not a string"))
}

/// One expected token as a Rust expression of the test's `T` type.
fn token(v: &Value, double: bool) -> Result<String, String> {
    let a = v.as_array().ok_or("a token is not an array")?;
    let kind = string(a.first(), "token kind")?;
    let s =
        |k: usize, what: &str| -> Result<String, String> { cps(string(a.get(k), what)?, double) };
    let n = a.len();
    match (kind, n) {
        ("DOCTYPE", 5) => {
            let correct = a
                .get(4)
                .and_then(Value::as_bool)
                .ok_or("DOCTYPE correctness is not a boolean")?;
            Ok(format!(
                "T::Doctype({}, {}, {}, {correct})",
                opt_cps(a.get(1).unwrap_or(&Value::Null), double, "DOCTYPE name")?,
                opt_cps(a.get(2).unwrap_or(&Value::Null), double, "DOCTYPE public")?,
                opt_cps(a.get(3).unwrap_or(&Value::Null), double, "DOCTYPE system")?,
            ))
        }
        ("StartTag", 3 | 4) => {
            let self_closing = match a.get(3) {
                None => false,
                Some(Value::Bool(true)) => true,
                Some(_) => return Err("StartTag's fourth entry is not true".into()),
            };
            let attrs = a
                .get(2)
                .and_then(Value::as_object)
                .ok_or("StartTag attributes are not an object")?;
            // serde_json's map is sorted by key.
            let mut items = Vec::new();
            for (k, v) in attrs {
                let value = v.as_str().ok_or("an attribute value is not a string")?;
                items.push(format!("({}, {})", cps(k, double)?, cps(value, double)?));
            }
            Ok(format!(
                "T::Start({}, &[{}], {self_closing})",
                s(1, "StartTag name")?,
                items.join(", ")
            ))
        }
        ("EndTag", 2) => Ok(format!("T::End({})", s(1, "EndTag name")?)),
        ("Comment", 2) => Ok(format!("T::Comment({})", s(1, "Comment data")?)),
        ("ProcessingInstruction", 3) => Ok(format!(
            "T::Pi({}, {})",
            s(1, "ProcessingInstruction target")?,
            s(2, "ProcessingInstruction data")?
        )),
        ("Character", 2) => Ok(format!("T::Chars({})", s(1, "Character data")?)),
        _ => Err(format!("unexpected token {kind:?} with {n} entries")),
    }
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let readme =
        std::fs::read_to_string(dir.join("README.md")).map_err(|e| format!("README.md: {e}"))?;
    for line in README_LINES {
        if !readme.lines().any(|l| l == *line) {
            return Err(format!(
                "README.md: the line {line:?} changed; check what a case means"
            ));
        }
    }
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/html5lib-tokenizer/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/html5lib_tokenizer.rs) produces.\n\
         // Source, commit and license: tests/data/html5lib-tokenizer/SOURCE.md.\n\
         //\n\
         // `doubleEscaped` cases are unescaped (each \\uHHHH is U+HHHH); an\n\
         // omitted `initialStates` is [Data]; attributes are sorted by name.\n\
         // Each case's `errors` were read and ignored: parse errors are not\n\
         // modelled (Phase 4 item 4.6). `xml_violation` marks the cases of\n\
         // xmlViolation.test, which expect the infoset coercion tweaks.\n\
         const HTML5LIB: &[Case] = &[\n",
    );
    for file in FILES.iter().filter(|f| f.ends_with(".test")) {
        let path = dir.join(file);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let json: Value =
            serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
        let obj = json
            .as_object()
            .ok_or_else(|| format!("{file}: expected a JSON object"))?;
        let (member, xml) = match obj
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>()
            .as_slice()
        {
            ["tests"] => ("tests", false),
            ["xmlViolationTests"] => ("xmlViolationTests", true),
            other => return Err(format!("{file}: unexpected members {other:?}")),
        };
        let cases = obj
            .get(member)
            .and_then(Value::as_array)
            .ok_or_else(|| format!("{file}: {member} is not an array"))?;
        for (index, case) in cases.iter().enumerate() {
            let c = case
                .as_object()
                .ok_or_else(|| format!("{file}[{index}]: not an object"))?;
            if let Some(k) = c.keys().find(|k| !KEYS.contains(&k.as_str())) {
                return Err(format!("{file}[{index}]: unexpected key {k:?}"));
            }
            let double = match c.get("doubleEscaped") {
                None => false,
                Some(Value::Bool(b)) => *b,
                Some(_) => return Err(format!("{file}[{index}]: doubleEscaped not a boolean")),
            };
            if let Some(e) = c.get("errors") {
                e.as_array()
                    .ok_or_else(|| format!("{file}[{index}]: errors is not an array"))?;
            }
            let description = string(c.get("description"), "description")
                .map_err(|e| format!("{file}[{index}]: {e}"))?;
            let input = cps(
                string(c.get("input"), "input").map_err(|e| format!("{file}[{index}]: {e}"))?,
                double,
            )?;
            let states = match c.get("initialStates") {
                None => vec!["Data"],
                Some(Value::Array(a)) => a
                    .iter()
                    .map(|s| {
                        let s = s.as_str().unwrap_or_default();
                        STATES
                            .iter()
                            .find(|(name, _)| *name == s)
                            .map(|(_, ours)| *ours)
                            .ok_or_else(|| format!("{file}[{index}]: unknown state {s:?}"))
                    })
                    .collect::<Result<_, _>>()?,
                Some(_) => return Err(format!("{file}[{index}]: initialStates not an array")),
            };
            let last = match c.get("lastStartTag") {
                None => "None".to_owned(),
                Some(Value::String(s)) => format!("Some({})", cps(s, double)?),
                Some(_) => return Err(format!("{file}[{index}]: lastStartTag not a string")),
            };
            let output: Vec<String> = c
                .get("output")
                .and_then(Value::as_array)
                .ok_or_else(|| format!("{file}[{index}]: output is not an array"))?
                .iter()
                .map(|t| token(t, double).map_err(|e| format!("{file}[{index}]: {e}")))
                .collect::<Result<_, _>>()?;
            let states: Vec<String> = states.iter().map(|s| format!("S::{s}")).collect();
            writeln!(
                out,
                "    Case {{ file: {file:?}, index: {index}, description: {description:?}, input: {input}, \
                 states: &[{}], last_start_tag: {last}, output: &[{}], xml_violation: {xml} }},",
                states.join(", "),
                output.join(", ")
            )
            .map_err(|e| e.to_string())?;
        }
    }
    out.push_str("];\n");
    Ok(out)
}
