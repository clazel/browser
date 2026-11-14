//! WPT `css/css-syntax/`: what can be read without a browser, as a table of (file,
//! line, helper, input, expected result), and a list of everything that cannot.
//!
//! These are testharness.js pages. Four of them call a helper of their own with
//! literal arguments, and those calls are the table: [`TABLES`] names each page's
//! helpers. The script of such a page is read as a run of statements, so a call in a
//! comment is not read, and anything but a helper's definition, a helper's call or
//! a direct `test()` fails the conversion instead of being half-read. The other
//! pages compute their checks through the DOM, and [`NOT_RUN`] lists them, each with
//! its reason. Nothing there counts as a pass.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Node, Parser, find_all};

/// A page whose checks are helper calls with literal arguments.
struct Table {
    file: &'static str,
    /// The page's helpers, with how many arguments each takes.
    helpers: &'static [(&'static str, usize)],
    /// `test()` calls written out in the page, which are not read.
    direct: usize,
}

const TABLES: &[Table] = &[
    Table {
        file: "anb-parsing.html",
        helpers: &[("testANB", 2)],
        direct: 0,
    },
    Table {
        file: "anb-serialization.html",
        helpers: &[("testANB", 2)],
        direct: 0,
    },
    Table {
        file: "input-preprocessing.html",
        helpers: &[("testParsing", 2)],
        direct: 0,
    },
    Table {
        file: "urange-parsing.html",
        helpers: &[("testUrange", 2), ("testInvalidUrange", 1)],
        direct: 1,
    },
];

const THROUGH_THE_DOM: &str = "computes its checks through the DOM or the CSS object model";

/// Every other page vendored, and why none of its checks can be read here.
const NOT_RUN: &[(&str, &str)] = &[
    ("at-rule-in-declaration-list.html", THROUGH_THE_DOM),
    ("cdc-vs-ident-tokens.html", THROUGH_THE_DOM),
    ("charset-is-not-a-rule.html", THROUGH_THE_DOM),
    ("custom-property-rule-ambiguity.html", THROUGH_THE_DOM),
    ("decimal-points-in-numbers.html", THROUGH_THE_DOM),
    ("declarations-trim-whitespace.html", THROUGH_THE_DOM),
    ("escaped-eof.html", THROUGH_THE_DOM),
    ("ident-three-code-points.html", THROUGH_THE_DOM),
    (
        "inclusive-ranges.html",
        "calls its helpers in loops, with computed strings",
    ),
    ("invalid-margin-trim-block-balancing.html", THROUGH_THE_DOM),
    ("invalid-nested-rules.html", THROUGH_THE_DOM),
    ("invalid-shape-block-balancing.html", THROUGH_THE_DOM),
    ("non-ascii-codepoints.html", THROUGH_THE_DOM),
    ("parse-invalid-input.html", THROUGH_THE_DOM),
    ("serialize-consecutive-tokens.html", THROUGH_THE_DOM),
    ("serialize-escape-identifiers.html", THROUGH_THE_DOM),
    ("trailing-braces.html", THROUGH_THE_DOM),
    ("unclosed-constructs.html", THROUGH_THE_DOM),
    ("unclosed-url-at-eof.html", THROUGH_THE_DOM),
    ("unicode-range-selector.html", THROUGH_THE_DOM),
    ("url-whitespace-consumption.html", THROUGH_THE_DOM),
    ("var-with-blocks.html", THROUGH_THE_DOM),
    ("whitespace.html", THROUGH_THE_DOM),
];

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "anb-parsing.html",
    "anb-serialization.html",
    "at-rule-in-declaration-list.html",
    "cdc-vs-ident-tokens.html",
    "charset-is-not-a-rule.html",
    "custom-property-rule-ambiguity.html",
    "decimal-points-in-numbers.html",
    "declarations-trim-whitespace.html",
    "escaped-eof.html",
    "ident-three-code-points.html",
    "inclusive-ranges.html",
    "input-preprocessing.html",
    "invalid-margin-trim-block-balancing.html",
    "invalid-nested-rules.html",
    "invalid-shape-block-balancing.html",
    "non-ascii-codepoints.html",
    "parse-invalid-input.html",
    "serialize-consecutive-tokens.html",
    "serialize-escape-identifiers.html",
    "trailing-braces.html",
    "unclosed-constructs.html",
    "unclosed-url-at-eof.html",
    "unicode-range-selector.html",
    "urange-parsing.html",
    "url-whitespace-consumption.html",
    "var-with-blocks.html",
    "whitespace.html",
];

/// One helper call. `expected` is `None` for "this does not parse".
struct Call {
    line: usize,
    helper: String,
    input: Vec<u16>,
    expected: Option<Vec<u16>>,
}

/// Move `p` past the next `marker`.
fn skip_past(p: &mut Parser, marker: &str) -> Result<(), String> {
    while !p.rest_starts_with(marker) {
        if p.bump().is_none() {
            return p.err(&format!("no {marker:?} before the end"));
        }
    }
    for _ in marker.chars() {
        p.bump();
    }
    Ok(())
}

/// A call's arguments as (input, expected). The pages write a parse error as the
/// string "parse error", which no real result is.
fn arguments(values: &[Node]) -> Result<(Vec<u16>, Option<Vec<u16>>), String> {
    let error: Vec<u16> = "parse error".encode_utf16().collect();
    match values {
        [input] => Ok((input.str_units()?.to_vec(), None)),
        [input, expected] => {
            let expected = expected.str_units()?;
            let expected = (expected != error.as_slice()).then(|| expected.to_vec());
            Ok((input.str_units()?.to_vec(), expected))
        }
        _ => Err(format!("{} arguments", values.len())),
    }
}

/// Read the page's one inline script as a run of statements.
fn read_calls(table: &Table, text: &str) -> Result<Vec<Call>, String> {
    let starts = find_all(text, "<script>");
    let [start] = starts.as_slice() else {
        return Err(format!("{} inline scripts, not one", starts.len()));
    };
    let mut p = Parser::at(text, *start);
    let mut calls = Vec::new();
    let mut direct = 0usize;
    loop {
        p.skip_trivia();
        if p.rest_starts_with("</script>") {
            break;
        }
        let line = p.line();
        let name = p.ident()?;
        if name == "function" {
            skip_past(&mut p, "\n}")?;
        } else if name == "test" {
            skip_past(&mut p, "\n}, ")?;
            skip_past(&mut p, "\n")?;
            direct = direct.saturating_add(1);
        } else {
            let Some((_, count)) = table.helpers.iter().find(|(h, _)| *h == name) else {
                return p.err(&format!("{name} is not one of the page's helpers"));
            };
            p.expect("(")?;
            let values = p.list(')', |p| p.literal())?;
            if values.len() != *count {
                return p.err(&format!("{name} takes {count} arguments"));
            }
            p.eat(";");
            let (input, expected) = arguments(&values).map_err(|e| format!("line {line}: {e}"))?;
            calls.push(Call {
                line,
                helper: name,
                input,
                expected,
            });
        }
    }
    if direct != table.direct {
        return Err(format!(
            "{direct} direct test() calls, expected {}",
            table.direct
        ));
    }
    if calls.is_empty() {
        return Err("no helper calls".to_owned());
    }
    Ok(calls)
}

fn units(v: &[u16]) -> String {
    let hex: Vec<String> = v.iter().map(|u| format!("0x{u:04X}")).collect();
    format!("&[{}]", hex.join(", "))
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let mut out = String::from(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-css-syntax/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_css_syntax.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-css-syntax/SOURCE.md.\n\
         const WPT: &[Case] = &[\n",
    );
    for table in TABLES {
        let file = table.file;
        let text = std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))?;
        for c in read_calls(table, &text).map_err(|e| format!("{file}: {e}"))? {
            let expected = match &c.expected {
                None => "None".to_owned(),
                Some(v) => format!("Some({})", units(v)),
            };
            writeln!(
                out,
                "    Case {{ file: {file:?}, line: {}, helper: {:?}, input: {}, expected: {expected} }},",
                c.line,
                c.helper,
                units(&c.input)
            )
            .map_err(|e| e.to_string())?;
        }
    }
    out.push_str("];\n\n// What this table does not cover: (file, why).\nconst NOT_RUN: &[(&str, &str)] = &[\n");
    for table in TABLES.iter().filter(|t| t.direct > 0) {
        writeln!(
            out,
            "    ({:?}, \"{} direct test() through the DOM\"),",
            table.file, table.direct
        )
        .map_err(|e| e.to_string())?;
    }
    for (file, why) in NOT_RUN {
        if !dir.join(file).is_file() {
            return Err(format!("{file}: listed as not run, but not vendored"));
        }
        writeln!(out, "    ({file:?}, {why:?}),").map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{FILES, NOT_RUN, TABLES, Table, read_calls};

    const TABLE: Table = Table {
        file: "x.html",
        helpers: &[("two", 2), ("one", 1)],
        direct: 0,
    };

    fn page(script: &str) -> String {
        format!("<script src=a></script>\n<script>\n{script}\n</script>\n")
    }

    #[test]
    fn reads_literal_calls_and_skips_definitions_and_comments() -> Result<(), String> {
        let text = page(
            "function two(a, b) {\n    test(()=>{ x; }, `y`);\n}\n\
             /* two(\"comment\", \"no\"); */\n// two(\"comment\", \"no\");\n\
             two(\"a\\ud800\", \"b\");\none(\"c\")\ntwo(\"d\", \"parse error\");",
        );
        let calls = read_calls(&TABLE, &text)?;
        assert_eq!(calls.len(), 3);
        let first = calls.first().ok_or("no call")?;
        assert_eq!(first.input, vec![0x61, 0xD800]);
        assert_eq!(first.expected, Some(vec![0x62]));
        assert_eq!(first.helper, "two");
        assert_eq!(first.line, 8);
        assert_eq!(calls.get(1).and_then(|c| c.expected.as_ref()), None);
        assert_eq!(calls.get(2).and_then(|c| c.expected.as_ref()), None);
        Ok(())
    }

    #[test]
    fn anything_else_fails_the_conversion() {
        let refused = [
            "two(i+\"\", \"a\");",
            "two(\"a\");",
            "one(\"a\", \"b\");",
            "for(var i = 0; i < 2; i++) { one(\"a\"); }",
            "three(\"a\");",
            "",
            "one(\"a\");\ntest(()=>{\n    x;\n}, \"a direct test\");",
        ];
        for script in refused {
            assert!(read_calls(&TABLE, &page(script)).is_err(), "{script}");
        }
        assert!(read_calls(&TABLE, "no script").is_err());
    }

    #[test]
    fn a_declared_direct_test_is_counted_and_not_read() -> Result<(), String> {
        let table = Table { direct: 1, ..TABLE };
        let text = page("one(\"a\");\ntest(()=>{\n    one(\"no\");\n}, \"direct\");");
        assert_eq!(read_calls(&table, &text)?.len(), 1);
        assert!(read_calls(&table, &page("one(\"a\");")).is_err());
        Ok(())
    }

    #[test]
    fn every_vendored_page_is_a_table_or_listed_as_not_run() {
        for file in FILES {
            let table = TABLES.iter().filter(|t| t.file == *file).count();
            let not_run = NOT_RUN.iter().filter(|(f, _)| f == file).count();
            assert_eq!(table.saturating_add(not_run), 1, "{file}");
        }
        assert_eq!(TABLES.len().saturating_add(NOT_RUN.len()), FILES.len());
    }
}
