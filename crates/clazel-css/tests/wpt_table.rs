//! The converted WPT `css/css-syntax/` table (phase-5.md item 5.1).
//!
//! There is no parser to run the cases through yet, so this checks only the table:
//! that each page's cases are there, that a sample came through unchanged, and that
//! what could not be read is still listed. Item 5.4's conformance test takes over
//! from this one, so no conformance is claimed here, and this file prints no
//! `clazel-conformance:` line.

/// One helper call of a WPT page. A string is UTF-16 code units, as JavaScript has it,
/// because some inputs are lone surrogates. `expected` is `None` for a parse error.
struct Case {
    file: &'static str,
    line: usize,
    helper: &'static str,
    input: &'static [u16],
    expected: Option<&'static [u16]>,
}

include!("generated/wpt_css_syntax.rs");

/// Each page read, with its number of helper calls, counted from the vendored pages.
const PAGES: &[(&str, usize)] = &[
    ("anb-parsing.html", 67),
    ("anb-serialization.html", 20),
    ("input-preprocessing.html", 10),
    ("urange-parsing.html", 94),
];

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn case(file: &str, input: &[u16]) -> Option<&'static Case> {
    WPT.iter().find(|c| c.file == file && c.input == input)
}

#[test]
fn every_page_has_all_its_calls_in_order() {
    for (file, count) in PAGES {
        let lines: Vec<usize> = WPT
            .iter()
            .filter(|c| c.file == *file)
            .map(|c| c.line)
            .collect();
        assert_eq!(lines.len(), *count, "{file}");
        assert!(lines.is_sorted(), "{file}");
    }
    let total = PAGES.iter().map(|(_, count)| *count).sum::<usize>();
    assert_eq!(WPT.len(), total);
}

#[test]
fn a_sample_survives_the_conversion() {
    let odd = case("anb-parsing.html", &units("odd"));
    assert_eq!(odd.map(|c| c.helper), Some("testANB"));
    assert_eq!(odd.and_then(|c| c.expected), Some(units("2n+1").as_slice()));

    let error = case("anb-parsing.html", &units("+ n"));
    assert_eq!(error.map(|c| c.expected), Some(None));

    let invalid = case("urange-parsing.html", &units("u+efg"));
    assert_eq!(invalid.map(|c| c.helper), Some("testInvalidUrange"));
    assert_eq!(invalid.map(|c| c.expected), Some(None));

    // A lone surrogate is kept as the page wrote it.
    let surrogate = case("input-preprocessing.html", &[0xD800]);
    assert_eq!(
        surrogate.and_then(|c| c.expected),
        Some([0xFFFD].as_slice())
    );
}

#[test]
fn what_could_not_be_read_stays_listed() {
    // 23 pages, and one direct test in a page that is otherwise read.
    assert_eq!(NOT_RUN.len(), 24);
    assert!(
        NOT_RUN
            .iter()
            .all(|(file, why)| !file.is_empty() && !why.is_empty())
    );
    assert!(
        NOT_RUN
            .iter()
            .any(|(file, _)| *file == "urange-parsing.html")
    );
    assert!(
        NOT_RUN
            .iter()
            .any(|(file, _)| *file == "inclusive-ranges.html")
    );
}
