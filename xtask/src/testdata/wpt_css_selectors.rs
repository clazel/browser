//! WPT `css/selectors/parsing/`: a table of (file, line, helper, selector, whether it
//! is valid, what it may serialize to).
//!
//! These are testharness.js pages. Most call the helpers of
//! `css/support/parsing-testcommon.js` with literal arguments. Two write their cases as
//! small templates, which are expanded here as the page's script would:
//!
//! - `parse-is-where.html`'s `assert_valid(valid, pattern, expected, description)` runs
//!   for `is` and `where`, with `String.prototype.replace`, which replaces the first
//!   `{}` only.
//! - `parse-anplusb.html`'s `run_tests_on_anplusb_selector(source)` runs a list of
//!   checks written as `source + '…'` for each pseudo-class it is called with.
//!
//! A page's script is read as a run of statements, so a call in a comment is not read,
//! and anything else fails the conversion instead of being half-read.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Lit, Node, Parser, find_all};

/// A page, and how many `test()` calls written out in it are not read.
struct Page {
    file: &'static str,
    direct: usize,
}

const fn page(file: &'static str) -> Page {
    Page { file, direct: 0 }
}

const PAGES: &[Page] = &[
    page("invalid-pseudos.html"),
    page("parse-anplusb.html"),
    page("parse-attribute.html"),
    page("parse-child.html"),
    page("parse-class-prefix.tentative.html"),
    page("parse-class.html"),
    page("parse-descendant.html"),
    page("parse-focus-visible.html"),
    page("parse-has-class-prefix.tentative.html"),
    Page {
        file: "parse-has-disallow-nesting-has-inside-has.html",
        direct: 1,
    },
    page("parse-has-forgiving-selector.html"),
    page("parse-has-slotted.tentative.html"),
    page("parse-has.html"),
    page("parse-heading.html"),
    page("parse-id.html"),
    page("parse-is-where.html"),
    page("parse-is.html"),
    page("parse-not.html"),
    page("parse-part.html"),
    page("parse-sibling.html"),
    page("parse-slotted.html"),
    page("parse-state.html"),
    page("parse-universal.html"),
    page("parse-where.html"),
];

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "invalid-pseudos.html",
    "parse-anplusb.html",
    "parse-attribute.html",
    "parse-child.html",
    "parse-class-prefix.tentative.html",
    "parse-class.html",
    "parse-descendant.html",
    "parse-focus-visible.html",
    "parse-has-class-prefix.tentative.html",
    "parse-has-disallow-nesting-has-inside-has.html",
    "parse-has-forgiving-selector.html",
    "parse-has-slotted.tentative.html",
    "parse-has.html",
    "parse-heading.html",
    "parse-id.html",
    "parse-is-where.html",
    "parse-is.html",
    "parse-not.html",
    "parse-part.html",
    "parse-sibling.html",
    "parse-slotted.html",
    "parse-state.html",
    "parse-universal.html",
    "parse-where.html",
    "parsing-testcommon.js",
];

/// One check. `serialized` is what a valid selector may serialize to.
#[derive(Debug, PartialEq)]
struct Call {
    line: usize,
    helper: String,
    selector: Vec<u16>,
    valid: bool,
    serialized: Vec<Vec<u16>>,
}

fn utf16(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

/// `text.replace("{}", with)`: the first only, as in JavaScript.
fn replace_first(text: &[u16], with: &[u16]) -> Vec<u16> {
    let pattern = utf16("{}");
    match text.windows(2).position(|w| w == pattern.as_slice()) {
        None => text.to_vec(),
        Some(at) => {
            let (head, tail) = text.split_at(at);
            let rest = tail.get(2..).unwrap_or_default();
            [head, with, rest].concat()
        }
    }
}

/// Move `p`, at an opening bracket, past the one that closes it, stepping over strings
/// and comments.
fn skip_balanced(p: &mut Parser) -> Result<(), String> {
    let mut depth = 0usize;
    loop {
        p.skip_trivia();
        match p.bump() {
            None => return p.err("no closing bracket before the end"),
            Some('(' | '[' | '{') => depth = depth.saturating_add(1),
            Some(')' | ']' | '}') => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Ok(());
                }
            }
            Some(q @ ('\'' | '"' | '`')) => loop {
                match p.bump() {
                    None => return p.err("no closing quote before the end"),
                    Some('\\') => {
                        p.bump();
                    }
                    Some(c) if c == q => break,
                    Some(_) => {}
                }
            },
            Some(_) => {}
        }
    }
}

/// Move `p`, after the word `function`, past the function.
fn skip_function(p: &mut Parser) -> Result<(), String> {
    p.ident()?;
    p.skip_trivia();
    skip_balanced(p)?;
    p.skip_trivia();
    skip_balanced(p)
}

/// The arguments of `test_valid_selector` and `test_valid_forgiving_selector`.
fn valid_selector(helper: &str, line: usize, values: &[Node]) -> Result<Call, String> {
    let (selector, serialized) = match values {
        [selector] => (selector, vec![selector.str_units()?.to_vec()]),
        [selector, one] if matches!(one.lit, Lit::Arr(_)) => {
            let all: Result<Vec<Vec<u16>>, String> = one
                .array()?
                .iter()
                .map(|s| s.str_units().map(<[u16]>::to_vec))
                .collect();
            (selector, all?)
        }
        [selector, one] => (selector, vec![one.str_units()?.to_vec()]),
        _ => return Err(format!("{helper}: {} arguments", values.len())),
    };
    Ok(Call {
        line,
        helper: helper.to_owned(),
        selector: selector.str_units()?.to_vec(),
        valid: true,
        serialized,
    })
}

fn invalid(helper: &str, line: usize, selector: Vec<u16>) -> Call {
    Call {
        line,
        helper: helper.to_owned(),
        selector,
        valid: false,
        serialized: Vec::new(),
    }
}

/// `assert_valid(valid, pattern, expected, description)`, for `is` and `where`.
fn assert_valid(calls: &mut Vec<Call>, line: usize, values: &[Node]) -> Result<(), String> {
    let [valid, pattern, expected, description] = values else {
        return Err(format!("assert_valid: {} arguments", values.len()));
    };
    description.str_units()?;
    let helper = if valid.boolean()? {
        "test_valid_selector"
    } else {
        "test_valid_forgiving_selector"
    };
    for pseudo in [":is", ":where"] {
        let pseudo = utf16(pseudo);
        let selector = replace_first(pattern.str_units()?, &pseudo);
        let serialized = if expected.is_null() {
            selector.clone()
        } else {
            replace_first(expected.str_units()?, &pseudo)
        };
        calls.push(Call {
            line,
            helper: helper.to_owned(),
            selector,
            valid: true,
            serialized: vec![serialized],
        });
    }
    Ok(())
}

/// One argument written `source + '…'`, as the text after `source`.
fn source_plus(p: &mut Parser) -> Result<Vec<u16>, String> {
    p.skip_trivia();
    if p.ident()? != "source" {
        return p.err("expected source");
    }
    p.skip_trivia();
    p.expect("+")?;
    Ok(p.literal()?.str_units()?.to_vec())
}

/// A check of `run_tests_on_anplusb_selector`: its helper, and what follows `source`.
struct Template {
    helper: String,
    selector: Vec<u16>,
    serialized: Option<Vec<u16>>,
}

/// The body of `run_tests_on_anplusb_selector`, with `p` after the word `function`.
fn read_template(p: &mut Parser) -> Result<Vec<Template>, String> {
    p.ident()?;
    p.expect("(source)")?;
    p.skip_trivia();
    p.expect("{")?;
    let mut checks = Vec::new();
    loop {
        p.skip_trivia();
        if p.eat("}") {
            return Ok(checks);
        }
        let helper = p.ident()?;
        p.expect("(")?;
        let values = p.list(')', source_plus)?;
        p.eat(";");
        let (selector, serialized) = match (helper.as_str(), values.as_slice()) {
            ("assert_selector_serializes_to", [selector, serialized]) => {
                (selector.clone(), Some(serialized.clone()))
            }
            ("assert_invalid_selector", [selector]) => (selector.clone(), None),
            _ => return p.err(&format!("{helper} is not a check of the template")),
        };
        checks.push(Template {
            helper,
            selector,
            serialized,
        });
    }
}

/// Read the page's one inline script as a run of statements.
fn read_calls(page: &Page, text: &str) -> Result<Vec<Call>, String> {
    let starts = find_all(text, "<script>");
    let [start] = starts.as_slice() else {
        return Err(format!("{} inline scripts, not one", starts.len()));
    };
    let mut p = Parser::at(text, *start);
    let mut calls = Vec::new();
    let mut template: Vec<Template> = Vec::new();
    let mut direct = 0usize;
    loop {
        p.skip_trivia();
        if p.rest_starts_with("</script>") {
            break;
        }
        let line = p.line();
        let name = p.ident()?;
        if name == "function" {
            p.skip_trivia();
            if p.rest_starts_with("run_tests_on_anplusb_selector") {
                template = read_template(&mut p)?;
            } else {
                skip_function(&mut p)?;
            }
            continue;
        }
        if name == "test" {
            p.skip_trivia();
            skip_balanced(&mut p)?;
            p.eat(";");
            direct = direct.saturating_add(1);
            continue;
        }
        p.expect("(")?;
        let values = p.list(')', |p| p.literal())?;
        p.eat(";");
        let here = |e: String| format!("line {line}: {e}");
        match name.as_str() {
            "test_valid_selector" | "test_valid_forgiving_selector" => {
                calls.push(valid_selector(&name, line, &values).map_err(here)?);
            }
            "test_invalid_selector" => {
                let [selector] = values.as_slice() else {
                    return p.err("test_invalid_selector takes one argument");
                };
                calls.push(invalid(
                    &name,
                    line,
                    selector.str_units().map_err(here)?.to_vec(),
                ));
            }
            "assert_valid" => assert_valid(&mut calls, line, &values).map_err(here)?,
            "run_tests_on_anplusb_selector" => {
                let [source] = values.as_slice() else {
                    return p.err("run_tests_on_anplusb_selector takes one argument");
                };
                let source = source.str_units().map_err(here)?;
                for check in &template {
                    let selector = [source, check.selector.as_slice()].concat();
                    calls.push(match &check.serialized {
                        None => invalid(&check.helper, line, selector),
                        Some(serialized) => Call {
                            line,
                            helper: check.helper.clone(),
                            selector,
                            valid: true,
                            serialized: vec![[source, serialized.as_slice()].concat()],
                        },
                    });
                }
            }
            _ => return p.err(&format!("{name} is not a helper this reads")),
        }
    }
    if direct != page.direct {
        return Err(format!(
            "{direct} direct test() calls, expected {}",
            page.direct
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
        "// @generated by `cargo xtask testdata` from tests/data/wpt-css-selectors/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_css_selectors.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-css-selectors/SOURCE.md.\n\
         const WPT: &[Case] = &[\n",
    );
    for page in PAGES {
        let file = page.file;
        let text = std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))?;
        for c in read_calls(page, &text).map_err(|e| format!("{file}: {e}"))? {
            let serialized: Vec<String> = c.serialized.iter().map(|s| units(s)).collect();
            writeln!(
                out,
                "    Case {{ file: {file:?}, line: {}, helper: {:?}, selector: {}, valid: {}, serialized: &[{}] }},",
                c.line,
                c.helper,
                units(&c.selector),
                c.valid,
                serialized.join(", ")
            )
            .map_err(|e| e.to_string())?;
        }
    }
    out.push_str("];\n\n// What this table does not cover: (file, why).\nconst NOT_RUN: &[(&str, &str)] = &[\n");
    for page in PAGES.iter().filter(|p| p.direct > 0) {
        writeln!(
            out,
            "    ({:?}, \"{} direct test() through the DOM\"),",
            page.file, page.direct
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{FILES, PAGES, Page, read_calls, replace_first, utf16};

    const PAGE: Page = Page {
        file: "x.html",
        direct: 0,
    };

    fn script(body: &str) -> String {
        format!("<script src=a></script>\n<script>\n{body}\n</script>\n")
    }

    #[test]
    fn reads_literal_calls_and_skips_definitions_and_comments() -> Result<(), String> {
        let text = script(
            "function other(a) {\n  test(() => { x(\"}\"); }, `y`);\n}\n\
             // test_invalid_selector('comment');\n\
             test_valid_selector('a');\n\
             test_valid_selector('b', 'c');\n\
             test_valid_selector('d', ['e', 'f']);\n\
             test_invalid_selector(`g`);\n\
             test_valid_forgiving_selector('h');",
        );
        let calls = read_calls(&PAGE, &text)?;
        assert_eq!(calls.len(), 5);
        let serialized: Vec<_> = calls.iter().map(|c| c.serialized.clone()).collect();
        assert_eq!(
            serialized,
            vec![
                vec![utf16("a")],
                vec![utf16("c")],
                vec![utf16("e"), utf16("f")],
                vec![],
                vec![utf16("h")],
            ]
        );
        assert_eq!(calls.get(3).map(|c| c.valid), Some(false));
        Ok(())
    }

    #[test]
    fn replace_is_the_first_only() {
        assert_eq!(
            replace_first(&utf16("{}a{}"), &utf16(":is")),
            utf16(":isa{}")
        );
        assert_eq!(replace_first(&utf16("a"), &utf16(":is")), utf16("a"));
    }

    #[test]
    fn assert_valid_expands_for_is_and_where() -> Result<(), String> {
        let text = script(
            "function assert_valid(valid, pattern, expected_pattern, description) {\n\
             for (let p of [\"is\"]) { test_valid_selector(p, p); }\n}\n\
             assert_valid(true, \"{}(div )\", \"{}(div)\", \"d\");\n\
             assert_valid(false, \"{}(,)\", null, \"e\");",
        );
        let calls = read_calls(&PAGE, &text)?;
        let got: Vec<_> = calls
            .iter()
            .map(|c| (c.helper.as_str(), c.selector.clone(), c.serialized.clone()))
            .collect();
        assert_eq!(
            got,
            vec![
                (
                    "test_valid_selector",
                    utf16(":is(div )"),
                    vec![utf16(":is(div)")]
                ),
                (
                    "test_valid_selector",
                    utf16(":where(div )"),
                    vec![utf16(":where(div)")]
                ),
                (
                    "test_valid_forgiving_selector",
                    utf16(":is(,)"),
                    vec![utf16(":is(,)")]
                ),
                (
                    "test_valid_forgiving_selector",
                    utf16(":where(,)"),
                    vec![utf16(":where(,)")]
                ),
            ]
        );
        Ok(())
    }

    #[test]
    fn the_anplusb_template_runs_for_each_source() -> Result<(), String> {
        let text = script(
            "function run_tests_on_anplusb_selector(source) {\n\
             assert_selector_serializes_to(source + '(1n+0)', source + '(n)');\n\
             assert_invalid_selector(source + '(n- 1 2)');\n}\n\
             run_tests_on_anplusb_selector(':a');\n\
             run_tests_on_anplusb_selector(':b');",
        );
        let calls = read_calls(&PAGE, &text)?;
        assert_eq!(calls.len(), 4);
        let last = calls.last().ok_or("no call")?;
        assert_eq!(last.selector, utf16(":b(n- 1 2)"));
        assert!(!last.valid);
        let second = calls.get(2).ok_or("no call")?;
        assert_eq!(second.serialized, vec![utf16(":b(n)")]);
        assert_eq!(second.helper, "assert_selector_serializes_to");
        Ok(())
    }

    #[test]
    fn anything_else_fails_the_conversion() {
        let refused = [
            "test_valid_selector(i + \"\");",
            "test_invalid_selector('a', 'b');",
            "test_valid_selector('a', 'b', 'c');",
            "test_valid_selector('a', 1);",
            "for (var i = 0; i < 2; i++) { test_invalid_selector('a'); }",
            "other('a');",
            "",
            "test_invalid_selector('a');\ntest(() => { x; });",
            "assert_valid(true, \"a\", null);",
            "function run_tests_on_anplusb_selector(source) {\nother(source + 'a');\n}",
        ];
        for body in refused {
            assert!(read_calls(&PAGE, &script(body)).is_err(), "{body}");
        }
        assert!(read_calls(&PAGE, "no script").is_err());
    }

    #[test]
    fn a_declared_direct_test_is_counted_and_not_read() -> Result<(), String> {
        let page = Page { direct: 1, ..PAGE };
        let text =
            script("test_invalid_selector('a');\ntest(() => {\n  // It's a\n  x(\")\");\n})");
        assert_eq!(read_calls(&page, &text)?.len(), 1);
        assert!(read_calls(&page, &script("test_invalid_selector('a');")).is_err());
        Ok(())
    }

    #[test]
    fn every_vendored_page_is_read() {
        let pages = FILES.iter().filter(|f| f.ends_with(".html")).count();
        assert_eq!(pages, PAGES.len());
        for page in PAGES {
            assert!(FILES.contains(&page.file), "{}", page.file);
        }
    }
}
