//! html5lib tree-construction tests (`*.dat`, maintained in WPT's
//! `html/syntax/parsing/resources/`), as a table of (input, fragment
//! context, scripting flag, expected tree).
//!
//! The format (WPT `html/syntax/parsing/resources/README.md`): tests
//! separated by one empty line, the file ending in a single LF. Each test is
//! an optional `#description` section, `#data` (every line up to `#errors`,
//! the final LF dropped), `#errors`, an optional `#new-errors`, an optional
//! `#document-fragment` (one line: the context element), an optional
//! `#script-on` or `#script-off`, and `#document` (the `| ` tree, up to the
//! empty line before the next test). Sections must come in that order; any
//! other `#` line where a section is expected, a missing section or a
//! malformed tree fails the conversion. `#errors`, `#new-errors` and
//! `#description` are read and dropped. The `scripted_*.dat` files need a
//! script engine: they are parsed with the same checks and only counted.

use std::fmt::Write as _;
use std::path::Path;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "adoption01.dat",
    "adoption02.dat",
    "blocks.dat",
    "comments01.dat",
    "doctype01.dat",
    "domjs-unsafe.dat",
    "entities01.dat",
    "entities02.dat",
    "foreign-fragment.dat",
    "html5test-com.dat",
    "inbody01.dat",
    "isindex.dat",
    "main-element.dat",
    "math.dat",
    "menuitem-element.dat",
    "namespace-sensitivity.dat",
    "noscript01.dat",
    "pending-spec-changes-plain-text-unsafe.dat",
    "pending-spec-changes.dat",
    "plain-text-unsafe.dat",
    "processing-instructions.dat",
    "quirks01.dat",
    "ruby.dat",
    "scriptdata01.dat",
    "scripted_adoption01.dat",
    "scripted_ark.dat",
    "scripted_foster01.dat",
    "scripted_webkit01.dat",
    "search-element.dat",
    "svg.dat",
    "tables01.dat",
    "template.dat",
    "tests1.dat",
    "tests10.dat",
    "tests11.dat",
    "tests12.dat",
    "tests14.dat",
    "tests15.dat",
    "tests16.dat",
    "tests17.dat",
    "tests18.dat",
    "tests19.dat",
    "tests2.dat",
    "tests20.dat",
    "tests21.dat",
    "tests22.dat",
    "tests23.dat",
    "tests24.dat",
    "tests25.dat",
    "tests26.dat",
    "tests3.dat",
    "tests4.dat",
    "tests5.dat",
    "tests6.dat",
    "tests7.dat",
    "tests8.dat",
    "tests9.dat",
    "tests_innerHTML_1.dat",
    "tricky01.dat",
    "void-in-phrasing.dat",
    "webkit01.dat",
    "webkit02.dat",
];

/// Files that end in an extra empty line, against the format (the file
/// ends in a single LF). The empty line is dropped; a listed file that no
/// longer has one fails, so the list stays exact.
const ENDS_IN_EMPTY_LINE: &[&str] = &["processing-instructions.dat"];

/// Prefix of the files whose cases need a script engine.
const SCRIPTED: &str = "scripted_";

/// Section headers that may end an `#errors` or `#new-errors` section.
const AFTER_ERRORS: &[&str] = &[
    "#new-errors",
    "#document-fragment",
    "#script-on",
    "#script-off",
    "#document",
];

/// Every section header of the format.
const SECTIONS: &[&str] = &[
    "#description",
    "#data",
    "#errors",
    "#new-errors",
    "#document-fragment",
    "#script-on",
    "#script-off",
    "#document",
];

/// One test, as read from a `.dat` file.
#[derive(Debug, PartialEq, Eq)]
pub struct Test {
    /// `#data`, the final line feed dropped.
    pub data: String,
    /// `#document-fragment`'s context element.
    pub fragment: Option<String>,
    /// `#script-on` (true) or `#script-off` (false).
    pub scripting: Option<bool>,
    /// `#document`, lines joined with LF.
    pub document: String,
}

/// Whether line `i` starts a test (`#data` or `#description`).
fn starts_test(lines: &[&str], i: usize) -> bool {
    matches!(lines.get(i), Some(&"#data" | &"#description"))
}

/// Parse a whole `.dat` file; `extra_empty_line`: it must end in one
/// empty line, which is dropped. Errors name the 1-based line.
pub fn parse(text: &str, extra_empty_line: bool) -> Result<Vec<Test>, String> {
    let mut body = text
        .strip_suffix('\n')
        .ok_or("the file does not end in a line feed")?;
    if extra_empty_line {
        body = body
            .strip_suffix('\n')
            .ok_or("listed in ENDS_IN_EMPTY_LINE, but does not end in an empty line")?;
    }
    if body.ends_with('\n') {
        return Err("the file ends in an empty line".to_owned());
    }
    let lines: Vec<&str> = body.split('\n').collect();
    let at = |i: usize| -> &str { lines.get(i).copied().unwrap_or("<end of file>") };
    let err =
        |i: usize, what: &str| format!("line {}: {what}, found {:?}", i.saturating_add(1), at(i));
    let mut tests = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        if at(i) == "#description" {
            i = i.saturating_add(1);
            while i < lines.len() && at(i) != "#data" {
                i = i.saturating_add(1);
            }
        }
        if at(i) != "#data" {
            return Err(err(i, "expected #data or #description"));
        }
        i = i.saturating_add(1);
        let start = i;
        while i < lines.len() && at(i) != "#errors" {
            i = i.saturating_add(1);
        }
        let data = lines.get(start..i).unwrap_or_default().join("\n");
        for header in ["#errors", "#new-errors"] {
            if at(i) != header {
                if header == "#errors" {
                    return Err(err(i, "expected #errors"));
                }
                continue;
            }
            i = i.saturating_add(1);
            while i < lines.len() && !AFTER_ERRORS.contains(&at(i)) {
                if at(i).is_empty() || at(i).starts_with('#') {
                    return Err(err(i, "expected an error line or a section"));
                }
                i = i.saturating_add(1);
            }
        }
        let mut fragment = None;
        if at(i) == "#document-fragment" {
            i = i.saturating_add(1);
            if at(i).is_empty() || at(i).starts_with('#') || i >= lines.len() {
                return Err(err(i, "expected a context element"));
            }
            fragment = Some(at(i).to_owned());
            i = i.saturating_add(1);
        }
        let mut scripting = None;
        if at(i) == "#script-on" || at(i) == "#script-off" {
            scripting = Some(at(i) == "#script-on");
            i = i.saturating_add(1);
        }
        if at(i) != "#document" {
            return Err(err(i, "expected #document"));
        }
        i = i.saturating_add(1);
        let start = i;
        if !at(i).starts_with("| ") {
            return Err(err(i, "expected a tree line starting with \"| \""));
        }
        while i < lines.len() && !(at(i).is_empty() && starts_test(&lines, i.saturating_add(1))) {
            if SECTIONS.contains(&at(i)) {
                return Err(err(
                    i,
                    "expected a tree line, or an empty line and the next test",
                ));
            }
            i = i.saturating_add(1);
        }
        let document = lines.get(start..i).unwrap_or_default().join("\n");
        if i < lines.len() {
            // Skip the empty line separating this test from the next.
            i = i.saturating_add(1);
        }
        tests.push(Test {
            data,
            fragment,
            scripting,
            document,
        });
    }
    if tests.is_empty() {
        return Err("no tests".to_owned());
    }
    Ok(tests)
}

fn quote(s: &str) -> String {
    format!("{s:?}")
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let mut cases = String::new();
    let mut scripted = 0usize;
    for file in FILES {
        let path = dir.join(file);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let tests =
            parse(&text, ENDS_IN_EMPTY_LINE.contains(file)).map_err(|e| format!("{file}: {e}"))?;
        if file.starts_with(SCRIPTED) {
            scripted = scripted.saturating_add(tests.len());
            continue;
        }
        for (index, t) in tests.iter().enumerate() {
            let fragment = t
                .fragment
                .as_deref()
                .map_or_else(|| "None".to_owned(), |f| format!("Some({})", quote(f)));
            let scripting = match t.scripting {
                None => "None",
                Some(true) => "Some(true)",
                Some(false) => "Some(false)",
            };
            writeln!(
                cases,
                "    Case {{ file: {}, index: {index}, data: {}, fragment: {fragment}, \
                 scripting: {scripting}, document: {} }},",
                quote(file),
                quote(&t.data),
                quote(&t.document)
            )
            .map_err(|e| e.to_string())?;
        }
    }
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/html5lib-tree-construction/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/html5lib_tree.rs) produces.\n\
         // Source, commit and license: tests/data/html5lib-tree-construction/SOURCE.md\n\
         // (html5lib tree-construction tests from WPT html/syntax/parsing/resources/ at\n\
         // 4ad507b28db0a636f528def9161d109fe11b93a3).\n\
         //\n\
         // Parse errors are not modelled: each case's #errors and #new-errors are read\n\
         // and dropped, so a case passes on its tree alone. #description is dropped too.\n\
         // The scripted_*.dat cases need a script engine and are only counted.\n\
         \n\
         /// One tree-construction case.\n\
         pub struct Case {\n\
         \x20   /// The `.dat` file.\n\
         \x20   pub file: &'static str,\n\
         \x20   /// The case's 0-based position in its file.\n\
         \x20   pub index: usize,\n\
         \x20   /// The input, exactly as in the file (the final line feed removed).\n\
         \x20   pub data: &'static str,\n\
         \x20   /// The #document-fragment context, e.g. \"td\" or \"svg path\";\n\
         \x20   /// `None`: parse as a document.\n\
         \x20   pub fragment: Option<&'static str>,\n\
         \x20   /// #script-on: `Some(true)`; #script-off: `Some(false)`; neither:\n\
         \x20   /// `None` (run with scripting both on and off).\n\
         \x20   pub scripting: Option<bool>,\n\
         \x20   /// The expected tree, exactly as in the file, lines joined with \\n.\n\
         \x20   pub document: &'static str,\n\
         }\n\
         \n",
    );
    writeln!(
        out,
        "/// Cases in scripted_*.dat: counted, never run.\n\
         pub const SCRIPTED_NOT_RUN: usize = {scripted};\n\
         \n\
         /// Every case of the other files, in file order.\n\
         pub const CASES: &[Case] = &["
    )
    .map_err(|e| e.to_string())?;
    out.push_str(&cases);
    out.push_str("];\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{Test, parse};

    #[test]
    fn parses_sections() {
        let text = "#data\n<p>a\n\nb\n#errors\n(1,3): expected-doctype\n#new-errors\n\
                    (1:1) x\n#document\n| <html>\n|   <body>\n|     \"a\n\nb\"\n\n\
                    #description\nfragment\n#data\n<td>\n#errors\n#document-fragment\n\
                    svg path\n#script-off\n#document\n| <td>\n";
        assert_eq!(
            parse(text, false),
            Ok(vec![
                Test {
                    data: "<p>a\n\nb".to_owned(),
                    fragment: None,
                    scripting: None,
                    document: "| <html>\n|   <body>\n|     \"a\n\nb\"".to_owned(),
                },
                Test {
                    data: "<td>".to_owned(),
                    fragment: Some("svg path".to_owned()),
                    scripting: Some(false),
                    document: "| <td>".to_owned(),
                },
            ])
        );
    }

    #[test]
    fn rejects_deviations() {
        let ok = "#data\nx\n#errors\n#document\n| \"x\"\n";
        assert!(parse(ok, false).is_ok());
        // An unknown section.
        assert!(parse("#data\nx\n#errors\n#weird\n#document\n| \"x\"\n", false).is_err());
        // No #document.
        assert!(parse("#data\nx\n#errors\n", false).is_err());
        // Sections out of order.
        assert!(
            parse(
                "#data\nx\n#errors\n#script-on\n#document-fragment\ntd\n#document\n| x\n",
                false
            )
            .is_err()
        );
        // No final line feed, or an extra one.
        assert!(parse(ok.trim_end(), false).is_err());
        assert!(parse(&format!("{ok}\n"), false).is_err());
        assert!(parse(&format!("{ok}\n"), true).is_ok());
        assert!(parse(ok, true).is_err());
        // Something other than a test after the separator.
        assert!(parse(&format!("{ok}\n#errors\n"), false).is_err());
    }
}
