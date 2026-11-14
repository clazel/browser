//! The converted WPT `css/selectors/parsing/` table (phase-5.md item 5.1).
//!
//! There is no parser to run the cases through yet, so this checks only the table:
//! that each page's cases are there, that a sample came through unchanged, and that
//! what could not be read is still listed. Item 5.5's conformance test takes over from
//! this one, so no conformance is claimed here, and this file prints no
//! `clazel-conformance:` line.

/// One check of a WPT page. A string is UTF-16 code units, as JavaScript has it.
/// `serialized` is what a valid selector may serialize to.
struct Case {
    file: &'static str,
    line: usize,
    helper: &'static str,
    selector: &'static [u16],
    valid: bool,
    serialized: &'static [&'static [u16]],
}

include!("generated/wpt_css_selectors.rs");

/// Each page, with its number of checks, counted from the vendored pages with `grep`
/// and not by the converter. `parse-is-where.html` is 22 `assert_valid` calls for two
/// pseudo-classes and one more call, and `parse-anplusb.html` is 28 checks for four.
const PAGES: &[(&str, usize)] = &[
    ("invalid-pseudos.html", 12),
    ("parse-anplusb.html", 112),
    ("parse-attribute.html", 16),
    ("parse-child.html", 2),
    ("parse-class-prefix.tentative.html", 16),
    ("parse-class.html", 4),
    ("parse-descendant.html", 3),
    ("parse-focus-visible.html", 3),
    ("parse-has-class-prefix.tentative.html", 15),
    ("parse-has-disallow-nesting-has-inside-has.html", 1),
    ("parse-has-forgiving-selector.html", 3),
    ("parse-has-slotted.tentative.html", 23),
    ("parse-has.html", 29),
    ("parse-heading.html", 28),
    ("parse-id.html", 3),
    ("parse-is-where.html", 45),
    ("parse-is.html", 6),
    ("parse-not.html", 26),
    ("parse-part.html", 32),
    ("parse-sibling.html", 3),
    ("parse-slotted.html", 19),
    ("parse-state.html", 24),
    ("parse-universal.html", 3),
    ("parse-where.html", 6),
];

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn find(file: &str, selector: &str) -> Option<&'static Case> {
    let selector = units(selector);
    WPT.iter()
        .find(|c| c.file == file && c.selector == selector.as_slice())
}

#[test]
fn every_page_has_its_cases() {
    for (file, count) in PAGES {
        let found = WPT.iter().filter(|c| c.file == *file).count();
        assert_eq!(found, *count, "{file}");
    }
    let total = PAGES.iter().fold(0usize, |n, (_, c)| n.saturating_add(*c));
    assert_eq!(WPT.len(), total);
    assert!(WPT.iter().all(|c| c.line > 0));
}

#[test]
fn a_valid_case_has_a_serialization_and_an_invalid_one_none() {
    for case in WPT {
        assert_eq!(
            case.valid,
            !case.serialized.is_empty(),
            "{} line {}",
            case.file,
            case.line
        );
    }
}

#[test]
fn samples_came_through_unchanged() {
    let attribute = find("parse-attribute.html", "[att=val]");
    let expected = units("[att=\"val\"]");
    assert_eq!(attribute.map(|c| c.valid), Some(true));
    assert_eq!(
        attribute.map(|c| c.serialized),
        Some([expected.as_slice()].as_slice())
    );

    let either = find("parse-has.html", "*:has(.a)").map(|c| c.serialized.len());
    assert_eq!(either, Some(2));

    let same = find("parse-attribute.html", "[att]");
    assert_eq!(
        same.and_then(|c| c.serialized.first().copied()),
        Some(units("[att]").as_slice())
    );
}

#[test]
fn the_templates_were_expanded() {
    for pseudo in [":is", ":where"] {
        let selector = format!("{pseudo}(div )");
        let case = find("parse-is-where.html", &selector);
        assert_eq!(case.map(|c| c.helper), Some("test_valid_selector"));
        let expected = units(&format!("{pseudo}(div)"));
        assert_eq!(
            case.and_then(|c| c.serialized.first().copied()),
            Some(expected.as_slice())
        );
    }
    let forgiving = find("parse-is-where.html", ":is(,,,)");
    assert_eq!(
        forgiving.map(|c| c.helper),
        Some("test_valid_forgiving_selector")
    );

    for pseudo in [
        ":nth-child",
        ":nth-last-child",
        ":nth-of-type",
        ":nth-last-of-type",
    ] {
        let selector = format!("{pseudo}(+n+3)");
        let case = find("parse-anplusb.html", &selector);
        let expected = units(&format!("{pseudo}(n+3)"));
        assert_eq!(
            case.and_then(|c| c.serialized.first().copied()),
            Some(expected.as_slice())
        );
        let selector = format!("{pseudo}(n-b1)");
        let bad = find("parse-anplusb.html", &selector);
        assert_eq!(bad.map(|c| c.valid), Some(false));
    }
    let bad = WPT
        .iter()
        .find(|c| c.file == "parse-is-where.html" && !c.valid);
    assert_eq!(bad.map(|c| c.helper), Some("test_invalid_selector"));
}

#[test]
fn what_could_not_be_read_is_listed() {
    assert_eq!(
        NOT_RUN,
        [(
            "parse-has-disallow-nesting-has-inside-has.html",
            "1 direct test() through the DOM"
        )]
    );
}
