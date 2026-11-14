//! WPT property value parsing pages (`css/*/parsing/*-valid.html` and `*-invalid.html`, and
//! a few of `css/css-values/`): a table of (file, line, property, value, whether it is
//! valid, what it may serialize to).
//!
//! Each page is a testharness.js page calling `test_valid_value(property, value,
//! serialized?)` and `test_invalid_value(property, value)` from
//! `css/support/parsing-testcommon.js`. A page is read only if every use of those two
//! helpers in its inline script is a call written at the top level of the script, after a
//! `;` or `}` (or at its start), with literal arguments. A page that uses either helper any
//! other way (inside a function or a loop, or with an argument that is computed) is not run
//! as a whole and is listed in `NOT_RUN` with the reason, so a half-read page is never
//! counted. Calls of other helpers at the top level (`test_shorthand_value`,
//! `test_computed_value`, a page's own wrappers) are counted in `OTHER` and never run.
//!
//! The vendored copies keep their WPT directory as a prefix: `css-box.margin-valid.html` is
//! `css/css-box/parsing/margin-valid.html`, and `css-values.x.html` is
//! `css/css-values/x.html`.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Lit, Node, Parser, find_all};

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "css-backgrounds.background-color-invalid.html",
    "css-backgrounds.background-color-valid.html",
    "css-backgrounds.background-image-invalid.html",
    "css-backgrounds.background-image-valid.html",
    "css-backgrounds.background-invalid.html",
    "css-backgrounds.background-valid.html",
    "css-backgrounds.border-color-invalid.html",
    "css-backgrounds.border-color-valid.html",
    "css-backgrounds.border-invalid.html",
    "css-backgrounds.border-style-invalid.html",
    "css-backgrounds.border-style-valid.html",
    "css-backgrounds.border-valid.html",
    "css-backgrounds.border-width-invalid.html",
    "css-backgrounds.border-width-valid.html",
    "css-box.margin-invalid.html",
    "css-box.margin-valid.html",
    "css-box.padding-invalid.html",
    "css-box.padding-valid.html",
    "css-box.visibility-invalid.html",
    "css-box.visibility-valid.html",
    "css-color.color-invalid-hex-color.html",
    "css-color.color-invalid-hsl.html",
    "css-color.color-invalid-named-color.html",
    "css-color.color-invalid-rgb.html",
    "css-color.color-invalid.html",
    "css-color.color-valid-hsl.html",
    "css-color.color-valid-rgb.html",
    "css-color.color-valid.html",
    "css-display.display-invalid.html",
    "css-display.display-valid.html",
    "css-fonts.font-family-invalid.html",
    "css-fonts.font-family-valid.html",
    "css-fonts.font-invalid.html",
    "css-fonts.font-size-invalid.html",
    "css-fonts.font-size-valid.html",
    "css-fonts.font-style-invalid.html",
    "css-fonts.font-style-valid.html",
    "css-fonts.font-valid.html",
    "css-fonts.font-weight-invalid.html",
    "css-fonts.font-weight-valid.html",
    "css-inline.line-height-invalid.html",
    "css-inline.line-height-valid.html",
    "css-inline.vertical-align-invalid.html",
    "css-inline.vertical-align-valid.html",
    "css-lists.list-style-type-invalid.html",
    "css-lists.list-style-type-valid.html",
    "css-overflow.overflow-invalid.html",
    "css-overflow.overflow-valid.html",
    "css-overflow.text-overflow-invalid.html",
    "css-overflow.text-overflow-valid.html",
    "css-sizing.height-invalid.html",
    "css-sizing.height-valid.html",
    "css-sizing.max-height-invalid.html",
    "css-sizing.max-height-valid.html",
    "css-sizing.max-width-invalid.html",
    "css-sizing.max-width-valid.html",
    "css-sizing.min-height-invalid.html",
    "css-sizing.min-height-valid.html",
    "css-sizing.min-width-invalid.html",
    "css-sizing.min-width-valid.html",
    "css-sizing.width-invalid.html",
    "css-sizing.width-valid.html",
    "css-tables.border-collapse-invalid.html",
    "css-tables.border-collapse-valid.html",
    "css-tables.border-spacing-invalid.html",
    "css-tables.border-spacing-valid.html",
    "css-tables.table-layout-invalid.html",
    "css-tables.table-layout-valid.html",
    "css-text-decor.text-decoration-color-invalid.html",
    "css-text-decor.text-decoration-color-valid.html",
    "css-text-decor.text-decoration-invalid.html",
    "css-text-decor.text-decoration-line-invalid.html",
    "css-text-decor.text-decoration-line-valid.html",
    "css-text-decor.text-decoration-style-invalid.html",
    "css-text-decor.text-decoration-style-valid.html",
    "css-text-decor.text-decoration-valid.html",
    "css-text.overflow-wrap-invalid.html",
    "css-text.overflow-wrap-valid.html",
    "css-text.text-align-invalid.html",
    "css-text.text-align-valid.html",
    "css-text.text-indent-invalid.html",
    "css-text.text-indent-valid.html",
    "css-text.white-space-invalid.html",
    "css-text.white-space-valid.html",
    "css-text.word-break-invalid.html",
    "css-text.word-break-valid.html",
    "css-ui.cursor-invalid.html",
    "css-ui.cursor-valid.html",
    "css-ui.resize-invalid.html",
    "css-ui.resize-valid.html",
    "css-values.calc-invalid-parsing.html",
    "css-values.minmax-length-invalid.html",
    "css-values.viewport-units-parsing.html",
    "parsing-testcommon.js",
];

/// The two helpers this reads.
const HELPERS: &[&str] = &["test_valid_value", "test_invalid_value"];

/// One check.
#[derive(Debug, PartialEq)]
struct Call {
    line: usize,
    property: String,
    value: String,
    valid: bool,
    serialized: Vec<String>,
}

/// What a page gave: its checks, or why it is not run; and how many other checks at
/// the top level were not read.
#[derive(Debug, PartialEq)]
struct PageResult {
    calls: Result<Vec<Call>, String>,
    other: usize,
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '$'
}

/// The arguments of one helper call.
fn call(helper: &str, line: usize, values: &[Node]) -> Result<Call, String> {
    let text = |n: &Node| n.string();
    match (helper, values) {
        ("test_invalid_value", [property, value]) => Ok(Call {
            line,
            property: text(property)?,
            value: text(value)?,
            valid: false,
            serialized: Vec::new(),
        }),
        ("test_valid_value", [property, value]) => Ok(Call {
            line,
            property: text(property)?,
            value: text(value)?,
            valid: true,
            serialized: vec![text(value)?],
        }),
        ("test_valid_value", [property, value, serialized]) => {
            let serialized = match &serialized.lit {
                Lit::Arr(all) => all.iter().map(text).collect::<Result<Vec<_>, _>>()?,
                _ => vec![text(serialized)?],
            };
            Ok(Call {
                line,
                property: text(property)?,
                value: text(value)?,
                valid: true,
                serialized,
            })
        }
        _ => Err(format!("{helper} with {} arguments", values.len())),
    }
}

/// Read one page.
fn read_page(text: &str) -> Result<PageResult, String> {
    let starts = find_all(text, "<script>");
    let [start] = starts.as_slice() else {
        return Err(format!("{} inline scripts, not one", starts.len()));
    };
    let chars: Vec<char> = text.chars().collect();
    let mut calls = Vec::new();
    let mut other = 0usize;
    let mut not_run: Option<String> = None;
    let mut depth = 0usize;
    // The last character that is not trivia, at any depth.
    let mut last: Option<char> = None;
    let mut i = *start;
    loop {
        let Some(&c) = chars.get(i) else {
            return Err("no </script>".to_owned());
        };
        let next = chars.get(i.saturating_add(1)).copied();
        if chars
            .get(i..i.saturating_add(9))
            .is_some_and(|w| w.iter().collect::<String>() == "</script>")
        {
            break;
        }
        match c {
            '/' if next == Some('/') => {
                while chars.get(i).is_some_and(|&c| c != '\n') {
                    i = i.saturating_add(1);
                }
                continue;
            }
            '/' if next == Some('*') => {
                i = i.saturating_add(2);
                while chars.get(i).is_some()
                    && !(chars.get(i) == Some(&'*') && chars.get(i.saturating_add(1)) == Some(&'/'))
                {
                    i = i.saturating_add(1);
                }
                i = i.saturating_add(2);
                continue;
            }
            q @ ('\'' | '"' | '`') => {
                i = i.saturating_add(1);
                loop {
                    match chars.get(i) {
                        None => return Err("unterminated string".to_owned()),
                        Some('\\') => i = i.saturating_add(2),
                        Some(&d) if d == q => break,
                        Some(_) => i = i.saturating_add(1),
                    }
                }
                last = Some(q);
                i = i.saturating_add(1);
                continue;
            }
            '(' | '[' | '{' => depth = depth.saturating_add(1),
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            c if c.is_whitespace() => {
                i = i.saturating_add(1);
                continue;
            }
            c if is_ident_char(c) => {
                let mut end = i;
                while chars.get(end).is_some_and(|&c| is_ident_char(c)) {
                    end = end.saturating_add(1);
                }
                let word: String = chars.get(i..end).unwrap_or_default().iter().collect();
                let before = last;
                let mut after = end;
                while chars.get(after).is_some_and(|c| c.is_whitespace()) {
                    after = after.saturating_add(1);
                }
                let is_call = chars.get(after) == Some(&'(');
                if HELPERS.contains(&word.as_str()) {
                    let statement_start = matches!(before, None | Some(';' | '}'));
                    if depth != 0 || !statement_start || !is_call {
                        not_run.get_or_insert_with(|| {
                            format!("{word} used inside a function, a loop or an expression")
                        });
                    } else {
                        let mut p = Parser::at(text, after.saturating_add(1));
                        let line = p.line();
                        match p
                            .list(')', |p| p.literal())
                            .and_then(|v| call(&word, line, &v))
                        {
                            Ok(c) => calls.push(c),
                            Err(e) => {
                                not_run.get_or_insert_with(|| {
                                    format!("{word} with arguments that are not literals ({e})")
                                });
                            }
                        }
                    }
                } else if depth == 0 && is_call && word.starts_with("test_") {
                    other = other.saturating_add(1);
                }
                last = chars.get(end.saturating_sub(1)).copied();
                i = end;
                continue;
            }
            _ => {}
        }
        last = Some(c);
        i = i.saturating_add(1);
    }
    let calls = match not_run {
        Some(why) => Err(why),
        None if calls.is_empty() => Err("no literal helper calls".to_owned()),
        None => Ok(calls),
    };
    Ok(PageResult { calls, other })
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let mut out = String::from(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-css-values/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_css_values.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-css-values/SOURCE.md.\n\
         const WPT: &[Case] = &[\n",
    );
    let mut not_run = String::new();
    let mut others = String::new();
    for file in FILES.iter().filter(|f| f.ends_with(".html")) {
        let text = std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))?;
        let page = read_page(&text).map_err(|e| format!("{file}: {e}"))?;
        match page.calls {
            Ok(calls) => {
                for c in calls {
                    let serialized: Vec<String> =
                        c.serialized.iter().map(|s| format!("{s:?}")).collect();
                    writeln!(
                        out,
                        "    Case {{ file: {file:?}, line: {}, property: {:?}, value: {:?}, valid: {}, serialized: &[{}] }},",
                        c.line,
                        c.property,
                        c.value,
                        c.valid,
                        serialized.join(", ")
                    )
                    .map_err(|e| e.to_string())?;
                }
            }
            Err(why) => writeln!(not_run, "    ({file:?}, {why:?}),").map_err(|e| e.to_string())?,
        }
        if page.other > 0 {
            writeln!(others, "    ({file:?}, {}),", page.other).map_err(|e| e.to_string())?;
        }
    }
    out.push_str(
        "];\n\n// Pages not run as a whole: (file, why).\nconst NOT_RUN: &[(&str, &str)] = &[\n",
    );
    out.push_str(&not_run);
    out.push_str(
        "];\n\n// Calls of other helpers at the top level of a page, never run: (file, how many).\n\
         const OTHER: &[(&str, usize)] = &[\n",
    );
    out.push_str(&others);
    out.push_str("];\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{FILES, read_page};

    fn script(body: &str) -> String {
        format!("<script src=a></script>\n<script>\n{body}\n</script>\n")
    }

    #[test]
    fn reads_top_level_literal_calls() -> Result<(), String> {
        let page = read_page(&script(
            "// test_invalid_value('a', 'comment');\n\
             test_valid_value('margin', '1px');\n\
             test_valid_value(\"margin\", \"1px 1px\", \"1px\");\n\
             test_valid_value('border', 'thin', ['thin', 'thin none']);\n\
             test_invalid_value('color', `#f`);\n\
             test_shorthand_value('background', 'none', {a: 'b'});",
        ))?;
        let calls = page.calls?;
        assert_eq!(calls.len(), 4);
        let serialized: Vec<_> = calls.iter().map(|c| c.serialized.clone()).collect();
        assert_eq!(
            serialized,
            vec![
                vec!["1px".to_owned()],
                vec!["1px".to_owned()],
                vec!["thin".to_owned(), "thin none".to_owned()],
                vec![],
            ]
        );
        assert_eq!(calls.get(3).map(|c| c.line), Some(7));
        assert_eq!(page.other, 1);
        Ok(())
    }

    #[test]
    fn any_other_use_makes_the_page_not_run() -> Result<(), String> {
        let refused = [
            "for (const t of tests) {\n test_invalid_value('color', t);\n}",
            "function f(v) { test_invalid_value('width', v); }\nf('a');",
            "test_valid_value('width', '1' + unit);",
            "for (const u of us) test_valid_value('width', 'a');",
            "test_valid_value('width', 'a', 'b', {});",
            "test_invalid_value('width');",
            "x = test_valid_value;",
            // Without a semicolon the call might be a loop's body, so it is not read.
            "test_valid_value('a', 'b')\ntest_valid_value('a', 'c');",
            "",
        ];
        for body in refused {
            assert!(read_page(&script(body))?.calls.is_err(), "{body}");
        }
        assert!(read_page("no script").is_err());
        Ok(())
    }

    #[test]
    fn strings_and_comments_do_not_count() -> Result<(), String> {
        let page = read_page(&script(
            "const s = 'test_invalid_value(x)'; /* test_valid_value(y) */\n\
             test_valid_value('a', 'b');",
        ))?;
        assert_eq!(page.calls?.len(), 1);
        Ok(())
    }

    #[test]
    fn every_page_is_html_or_the_helpers() {
        for f in FILES {
            assert!(f.ends_with(".html") || *f == "parsing-testcommon.js", "{f}");
        }
    }
}
