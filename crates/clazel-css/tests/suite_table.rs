//! The converted `css-parsing-tests` table (phase-5.md item 5.1).
//!
//! There is no parser to run the cases through yet, so this checks only the table:
//! that every file's cases are there, and that a sample of each kind of value came
//! through the conversion unchanged. Item 5.4's conformance test takes over from
//! this one, mapping the table to `clazel-css`'s types. No conformance is claimed
//! here, so this file prints no `clazel-conformance:` line.

use Json::{Bool, List, Null, Num, Obj, Str};

/// A value of the suite's JSON, as the converter wrote it.
#[derive(Debug, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    /// The number as JSON wrote it, since a test decides how to read it.
    Num(&'static str),
    Str(&'static str),
    List(&'static [Json]),
    /// Fields in key order.
    Obj(&'static [(&'static str, Json)]),
}

/// One case: the file it came from, its place there, what goes in and what comes out.
struct Case {
    file: &'static str,
    index: usize,
    input: Json,
    expected: Json,
}

include!("generated/css_parsing_tests.rs");

/// Every file, with its number of cases, counted from the vendored files.
const FILES: &[(&str, usize)] = &[
    ("An+B.json", 128),
    ("component_value_list.json", 44),
    ("declaration_list.json", 9),
    ("one_component_value.json", 10),
    ("one_declaration.json", 22),
    ("one_rule.json", 14),
    ("rule_list.json", 16),
    ("stylesheet.json", 18),
    ("stylesheet_bytes.json", 28),
    ("urange.json", 12),
];

fn case(file: &str, index: usize) -> Option<&'static Case> {
    CASES.iter().find(|c| c.file == file && c.index == index)
}

#[test]
fn every_file_has_all_its_cases_in_order() {
    for (file, count) in FILES {
        let indices: Vec<usize> = CASES
            .iter()
            .filter(|c| c.file == *file)
            .map(|c| c.index)
            .collect();
        let expected: Vec<usize> = (0..*count).collect();
        assert_eq!(indices, expected, "{file}");
    }
    let total = FILES.iter().map(|(_, count)| *count).sum::<usize>();
    assert_eq!(CASES.len(), total);
}

#[test]
fn each_kind_of_value_survives_the_conversion() {
    let red = case("component_value_list.json", 2);
    assert_eq!(red.map(|c| &c.input), Some(&Str("red")));
    assert_eq!(
        red.map(|c| &c.expected),
        Some(&List(&[List(&[Str("ident"), Str("red")])]))
    );

    let odd = case("An+B.json", 2);
    assert_eq!(odd.map(|c| &c.input), Some(&Str("odd")));
    assert_eq!(odd.map(|c| &c.expected), Some(&List(&[Num("2"), Num("1")])));

    let bytes = case("stylesheet_bytes.json", 1);
    assert_eq!(
        bytes.map(|c| &c.input),
        Some(&Obj(&[
            ("css_bytes", Str("@\u{c3}\u{a9}")),
            ("environment_encoding", Null),
            ("protocol_encoding", Null),
        ]))
    );
    assert_eq!(
        bytes.map(|c| &c.expected),
        Some(&List(&[
            List(&[List(&[Str("at-rule"), Str("é"), List(&[]), Null])]),
            Str("utf-8"),
        ]))
    );

    let declarations = CASES
        .iter()
        .filter(|c| c.file == "one_declaration.json")
        .filter(|c| matches!(c.expected, List([Str("declaration"), _, _, Bool(_)])));
    assert!(declarations.count() > 0);
}
