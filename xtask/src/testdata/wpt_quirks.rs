//! WPT `quirks/unitless-length/` and `quirks/hashless-hex-color/`: the Quirks Mode
//! Standard's two CSS value quirks (§3.6 and §3.7 at the pinned text; the plan's §3.1† and
//! §3.2†).
//!
//! Both are testharness.js pages that load `support/common.js`, which holds the cases as
//! three literal arrays: `tests` (an input and what it must equal in quirks mode, `q`, and
//! in other modes, `s`; a missing one means the input must be dropped), `props` (the
//! properties each input is tried on) and `other_tests` (declarations that must be dropped
//! in quirks mode, because the quirk does not apply to those properties). The pages differ
//! only in the mode of the frame the script writes, named by the `iframe`'s class.
//!
//! The vendored copies keep their directory as a prefix: `unitless-length.common.js` is
//! `quirks/unitless-length/support/common.js` and `unitless-length.quirks.html` is
//! `quirks/unitless-length/quirks.html`.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Node, Parser, find_all};

/// The two tests.
const SUITES: &[&str] = &["hashless-hex-color", "unitless-length"];

/// The three modes, as the pages' `iframe` classes.
const MODES: &[&str] = &["limited-quirks", "no-quirks", "quirks"];

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "hashless-hex-color.common.js",
    "hashless-hex-color.limited-quirks.html",
    "hashless-hex-color.no-quirks.html",
    "hashless-hex-color.quirks.html",
    "unitless-length.common.js",
    "unitless-length.limited-quirks.html",
    "unitless-length.no-quirks.html",
    "unitless-length.quirks.html",
];

/// The literal array assigned by `var name = [` in `text`.
fn array(text: &str, name: &str) -> Result<Vec<Node>, String> {
    let needle = format!("var {name} = [");
    let found = find_all(text, &needle);
    let [after] = found.as_slice() else {
        return Err(format!("{} assignments of {name}, not one", found.len()));
    };
    let mut p = Parser::at(text, after.saturating_sub(1));
    Ok(p.literal()?.array()?.to_vec())
}

/// Optional string field `key` of object `n`.
fn optional(n: &Node, key: &str) -> Result<Option<String>, String> {
    match n.field(key) {
        Ok(v) => v.string().map(Some),
        Err(_) => Ok(None),
    }
}

/// Check that each object in `nodes` has only the fields in `keys`.
fn only_fields(nodes: &[Node], keys: &[&str]) -> Result<(), String> {
    for n in nodes {
        let super::js::Lit::Obj(fields) = &n.lit else {
            return Err(format!("line {}: expected an object", n.line));
        };
        for (k, _) in fields {
            if !keys.contains(&k.as_str()) {
                return Err(format!("line {}: unknown field {k:?}", n.line));
            }
        }
    }
    Ok(())
}

fn opt(s: Option<&String>) -> String {
    s.map_or_else(|| "None".to_owned(), |s| format!("Some({s:?})"))
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let mut cases = String::new();
    let mut props = String::new();
    let mut excluded = String::new();
    for suite in SUITES {
        let file = format!("{suite}.common.js");
        let text = std::fs::read_to_string(dir.join(&file)).map_err(|e| format!("{file}: {e}"))?;
        let here = |e: String| format!("{file}: {e}");
        let tests = array(&text, "tests").map_err(here)?;
        only_fields(&tests, &["input", "q", "s", "shorthand", "desc", "svg"]).map_err(here)?;
        for t in &tests {
            let input = t.field("input").and_then(Node::string).map_err(here)?;
            let q = optional(t, "q").map_err(here)?;
            let s = optional(t, "s").map_err(here)?;
            let shorthand = match t.field("shorthand") {
                Ok(v) => v.boolean().map_err(here)?,
                Err(_) => false,
            };
            writeln!(
                cases,
                "    Case {{ suite: {suite:?}, line: {}, input: {input:?}, q: {}, s: {}, shorthand: {shorthand} }},",
                t.line,
                opt(q.as_ref()),
                opt(s.as_ref())
            )
            .map_err(|e| e.to_string())?;
        }
        let list = array(&text, "props").map_err(here)?;
        only_fields(&list, &["prop", "check", "check_also"]).map_err(here)?;
        for p in &list {
            let prop = p.field("prop").and_then(Node::string).map_err(here)?;
            let check = p.field("check").and_then(Node::string).map_err(here)?;
            let also: Vec<String> = match p.field("check_also") {
                Ok(v) => v
                    .array()
                    .map_err(here)?
                    .iter()
                    .map(|n| n.string().map(|s| format!("{s:?}")))
                    .collect::<Result<_, _>>()
                    .map_err(here)?,
                Err(_) => Vec::new(),
            };
            let has_also = p.field("check_also").is_ok();
            writeln!(
                props,
                "    QuirkProp {{ suite: {suite:?}, prop: {prop:?}, check: {check:?}, shorthand: {has_also}, also: &[{}] }},",
                also.join(", ")
            )
            .map_err(|e| e.to_string())?;
        }
        let others = array(&text, "other_tests").map_err(here)?;
        only_fields(&others, &["input", "prop"]).map_err(here)?;
        for o in &others {
            let input = o.field("input").and_then(Node::string).map_err(here)?;
            let prop = o.field("prop").and_then(Node::string).map_err(here)?;
            writeln!(
                excluded,
                "    ({suite:?}, {}, {input:?}, {prop:?}),",
                o.line
            )
            .map_err(|e| e.to_string())?;
        }
        // Each page must load the script and name its mode.
        for mode in MODES {
            let page = format!("{suite}.{mode}.html");
            let text =
                std::fs::read_to_string(dir.join(&page)).map_err(|e| format!("{page}: {e}"))?;
            if find_all(&text, &format!("<iframe class={mode}>")).len() != 1
                || find_all(&text, "<script src=support/common.js>").len() != 1
            {
                return Err(format!(
                    "{page}: expected one <iframe class={mode}> and one support/common.js"
                ));
            }
        }
    }
    Ok(format!(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-quirks/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_quirks.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-quirks/SOURCE.md.\n\
         //\n\
         // Each page runs every case on every property of its suite, in its mode: quirks,\n\
         // limited-quirks or no-quirks (the last two behave alike here).\n\
         const QUIRKS: &[Case] = &[\n{cases}];\n\n\
         const QUIRK_PROPS: &[QuirkProp] = &[\n{props}];\n\n\
         // Declarations that must be dropped in quirks mode: (suite, line, declaration,\n\
         // the property checked).\n\
         const EXCLUDED: &[(&str, usize, &str, &str)] = &[\n{excluded}];\n"
    ))
}

#[cfg(test)]
mod tests {
    use super::array;

    #[test]
    fn reads_the_literal_arrays() -> Result<(), String> {
        let text = "onload = function() {\n    var tests = [\n    {input:\"1\", q:\"1px\"},\n    {input:'a'},\n    ];\n";
        let tests = array(text, "tests")?;
        assert_eq!(tests.len(), 2);
        assert!(array(text, "props").is_err());
        assert!(array("var tests = [x];", "tests").is_err());
        Ok(())
    }
}
