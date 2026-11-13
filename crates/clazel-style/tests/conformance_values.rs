//! The property value parsers and their serialization against WPT (phase-5.md item 5.6):
//! the `-valid` and `-invalid` parsing pages of the subset's properties, and the Quirks Mode
//! tests `quirks/unitless-length/` and `quirks/hashless-hex-color/`.
//!
//! **Parsing pages.** Each case is one unit, run as `parsing-testcommon.js` runs it: set
//! `element.style[property] = value` on an empty declaration block and read
//! `getPropertyValue(property)`. A valid case passes if the result is one of the strings the
//! page accepts and setting that result again gives it back; an invalid case passes if the
//! result is the empty string. Cases of properties outside the subset are not counted (the
//! table has none: the pages were chosen by property).
//!
//! **Quirks tests.** Each unit is one case of `common.js` on one property, in one of the
//! three modes the pages run (quirks, limited-quirks and no-quirks). The page compares the
//! computed value of the test declaration with that of the reference; item 5.6 has no
//! computed values, so the unit compares the serialized specified values of the property it
//! checks (and of `check_also`'s), which agree wherever the reference is written as the
//! value the quirk gives. A missing reference means the test declaration must be dropped.
//! Properties outside the subset (`bottom`, `clip`, `left`, `letter-spacing`, `right`,
//! `top`, `word-spacing`, `outline-*`) are not run, and not counted.
//!
//! A unit that fails is an expected failure only if this file gives it a reason; any other
//! failure, and any expected failure that passes, fails the test.

use clazel_style::values::{get_property_value, parse, property};

/// One check of a WPT parsing page.
struct Case {
    file: &'static str,
    line: usize,
    property: &'static str,
    value: &'static str,
    valid: bool,
    serialized: &'static [&'static str],
}

include!("generated/wpt_css_values.rs");

mod quirks_table {
    /// One case of a quirks test's `tests` array.
    pub struct Case {
        pub suite: &'static str,
        pub line: usize,
        pub input: &'static str,
        pub q: Option<&'static str>,
        pub s: Option<&'static str>,
        pub shorthand: bool,
    }

    /// One entry of its `props` array.
    pub struct QuirkProp {
        pub suite: &'static str,
        pub prop: &'static str,
        pub check: &'static str,
        pub shorthand: bool,
        pub also: &'static [&'static str],
    }

    include!("generated/wpt_quirks.rs");

    /// The `tests` arrays.
    pub fn cases() -> &'static [Case] {
        QUIRKS
    }

    /// The `props` arrays.
    pub fn props() -> &'static [QuirkProp] {
        QUIRK_PROPS
    }

    /// The `other_tests` arrays.
    pub fn excluded() -> &'static [(&'static str, usize, &'static str, &'static str)] {
        EXCLUDED
    }
}

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// `e.style[property] = value; e.style.getPropertyValue(property)`.
fn set_and_get(property: &str, value: &str, quirks: bool) -> String {
    let block = parse(&cps(property), &cps(value), quirks).unwrap_or_default();
    get_property_value(&block, &cps(property))
}

/// Value syntax outside the subset (phase-5.md 5.0(b) and item 5.6), by what the value
/// contains. Only cases WPT calls valid can fail for this, since the parser calls what it
/// does not support invalid.
const OUT_OF_SUBSET_SYNTAX: &[(&str, &str)] = &[
    (
        "calc(",
        "calc() and the math functions are not in the subset",
    ),
    (
        "min(",
        "calc() and the math functions are not in the subset",
    ),
    (
        "max(",
        "calc() and the math functions are not in the subset",
    ),
    (
        "clamp(",
        "calc() and the math functions are not in the subset",
    ),
    (
        "sign(",
        "calc() and the math functions are not in the subset",
    ),
    (
        "fit-content",
        "the intrinsic sizing keywords are not in the subset",
    ),
    (
        "min-content",
        "the intrinsic sizing keywords are not in the subset",
    ),
    (
        "max-content",
        "the intrinsic sizing keywords are not in the subset",
    ),
    ("light-dark(", "light-dark() is not in the subset"),
    ("image-set(", "image-set() is not in the subset"),
    ("cross-fade(", "cross-fade() is not in the subset"),
    ("image(", "image() is not in the subset"),
    (
        "symbols(",
        "symbols() (CSS Counter Styles 3 §6†) is not in the subset",
    ),
    (
        "color(",
        "CSS Color 4's color() and other colour spaces are not in the subset",
    ),
    (
        "lab(",
        "colour spaces other than sRGB are not in the subset",
    ),
    (
        "lch(",
        "colour spaces other than sRGB are not in the subset",
    ),
    (
        "hwb(",
        "colour spaces other than sRGB are not in the subset",
    ),
    (
        "color-mix(",
        "colour spaces other than sRGB are not in the subset",
    ),
    (
        "border-area",
        "background-clip: border-area (Backgrounds 4) is not in the subset",
    ),
];

/// Properties whose pages WPT includes but which are not in the subset.
const OUT_OF_SUBSET_PROPERTIES: &[(&str, &str)] = &[
    (
        "overflow-block",
        "the flow-relative overflow longhands are not in the subset",
    ),
    (
        "overflow-inline",
        "the flow-relative overflow longhands are not in the subset",
    ),
];

/// Single cases expected to fail, by (file, value), with the reason.
const CASES: &[(&str, &str, &str)] = &[(
    "css-backgrounds.background-valid.html",
    "url(\"https://example.com/\") 1px 2px / 3px 4px space round local padding-box content-box, rgb(5, 6, 7) url(\"https://example.com/\") 1px 2px / 3px 4px space round local padding-box content-box",
    "several background layers are not in the subset (one layer is)",
)];

/// Valid values of a property that are outside the subset: (property, the values the
/// subset has, why the others are not in it). A valid case whose value is not one of the
/// listed ones is an expected failure.
const SUBSET_VALUES: &[(&str, &[&str], &str)] = &[
    (
        "display",
        &[
            "none",
            "block",
            "inline",
            "inline-block",
            "list-item",
            "table",
            "inline-table",
            "table-row-group",
            "table-header-group",
            "table-footer-group",
            "table-row",
            "table-cell",
            "table-column-group",
            "table-column",
            "table-caption",
        ],
        "phase-5.md item 5.6 fixes display's subset to none, block, inline, inline-block, \
         list-item and the table values; flex, grid, ruby, run-in, contents, flow-root and the \
         multi-keyword syntax are Phase 8's",
    ),
    (
        "vertical-align",
        &[
            "baseline",
            "sub",
            "super",
            "top",
            "text-top",
            "middle",
            "bottom",
            "text-bottom",
            "-10px",
            "0.5em",
            "20%",
        ],
        "the subset has CSS 2.1 §10.8.1's vertical-align; CSS Inline 3's shorthand \
         (alignment-baseline, baseline-shift, baseline-source), which also serializes 0 as \
         baseline, is not in it",
    ),
    (
        "text-decoration-line",
        &[
            "none",
            "underline",
            "overline",
            "line-through",
            "blink",
            "underline overline",
            "overline underline",
            "underline line-through",
            "line-through underline",
            "underline blink",
            "blink underline",
            "overline line-through",
            "line-through overline",
            "overline blink",
            "blink overline",
            "line-through blink",
            "blink line-through",
        ],
        "spelling-error and grammar-error are CSS Text Decoration 4's, not in the subset",
    ),
    (
        "word-break",
        &["normal", "break-all", "keep-all", "break-word"],
        "manual and auto-phrase are CSS Text 4's, not in the subset",
    ),
];

/// Why a parsing case is expected to fail, or `None`.
fn expected_failure(case: &Case) -> Option<&'static str> {
    if let Some((_, _, why)) = CASES
        .iter()
        .find(|(f, v, _)| *f == case.file && *v == case.value)
    {
        return Some(why);
    }
    if !case.valid {
        return None;
    }
    if let Some((_, why)) = OUT_OF_SUBSET_PROPERTIES
        .iter()
        .find(|(p, _)| *p == case.property)
    {
        return Some(why);
    }
    if let Some((_, values, why)) = SUBSET_VALUES.iter().find(|(p, _, _)| *p == case.property) {
        // Text Decoration's combinations of three or four lines are in the subset too.
        let lines = case.property == "text-decoration-line"
            && case
                .value
                .split(' ')
                .all(|w| ["underline", "overline", "line-through", "blink"].contains(&w));
        if !values.contains(&case.value) && !lines {
            return Some(why);
        }
    }
    let lower = case.value.to_ascii_lowercase();
    OUT_OF_SUBSET_SYNTAX
        .iter()
        .find(|(s, _)| lower.contains(s))
        .map(|(_, why)| *why)
}

/// One parsing case: `Ok` if it passes.
fn run(case: &Case) -> Result<(), String> {
    let got = set_and_get(case.property, case.value, false);
    if !case.valid {
        return if got.is_empty() {
            Ok(())
        } else {
            Err(format!("set, reads {got:?}"))
        };
    }
    if got.is_empty() {
        return Err("not set".to_owned());
    }
    if !case.serialized.contains(&got.as_str()) {
        return Err(format!("reads {got:?}"));
    }
    let again = set_and_get(case.property, &got, false);
    if again != got {
        return Err(format!("{got:?} set again reads {again:?}"));
    }
    Ok(())
}

/// Tallies of one suite.
#[derive(Default)]
struct Tally {
    pass: usize,
    xfail: usize,
    ran: usize,
    failures: Vec<String>,
}

impl Tally {
    fn add(&mut self, what: String, result: Result<(), String>, expected: Option<&str>) {
        self.ran = self.ran.saturating_add(1);
        match (result, expected) {
            (Ok(()), None) => self.pass = self.pass.saturating_add(1),
            (Err(_), Some(_)) => self.xfail = self.xfail.saturating_add(1),
            (Ok(()), Some(reason)) => self
                .failures
                .push(format!("{what} passes but is listed: {reason}")),
            (Err(why), None) => self.failures.push(format!("{what}: {why}")),
        }
    }

    fn report(&self, suite: &str) {
        println!(
            "clazel-conformance: suite=\"{suite}\" pass={} xfail={} fail={} total={}",
            self.pass,
            self.xfail,
            self.failures.len(),
            self.ran
        );
    }
}

#[test]
fn wpt_property_value_parsing() {
    // Under Miri a stride of the cases, to finish in about a minute (docs/VERIFICATION.md):
    // 7 runs 131 of them in 42 s of Miri's time.
    let stride = if cfg!(miri) { 7 } else { 1 };
    let mut t = Tally::default();
    for (k, case) in WPT.iter().enumerate() {
        if !k.is_multiple_of(stride) {
            continue;
        }
        // Every property a valid case sets is known, in or out of the subset (an invalid
        // case may name one that does not exist, such as `margin-bottom-left`).
        let known = property(&cps(case.property)).is_some()
            || OUT_OF_SUBSET_PROPERTIES
                .iter()
                .any(|(p, _)| *p == case.property);
        assert!(
            known || !case.valid,
            "{}: {} is not a property of the subset",
            case.file,
            case.property
        );
        t.add(
            format!(
                "{}:{} {}: {:?} ({})",
                case.file,
                case.line,
                case.property,
                case.value,
                if case.valid { "valid" } else { "invalid" }
            ),
            run(case),
            expected_failure(case),
        );
    }
    t.report("WPT css/*/parsing (property values of the subset)");
    // Pages the converter could not read as literals are listed there, never counted, and
    // so are the other helpers' calls (test_shorthand_value and wrappers).
    let others: usize = OTHER.iter().map(|(_, n)| *n).sum();
    println!(
        "not run: {} pages that call the helpers from loops or wrappers, and {others} calls \
         of other helpers",
        NOT_RUN.len()
    );
    assert_eq!(NOT_RUN.len(), 9);
    assert_eq!(others, 64);
    assert!(t.failures.is_empty(), "{}", t.failures.join("\n"));
}

/// Quirks cases expected to fail: (suite, input, reason).
const QUIRK_CASES: &[(&str, &str, &str)] = &[];

#[test]
fn wpt_quirks() {
    // Under Miri a stride of the (mode, case, property) checks, to finish in about a
    // minute (docs/VERIFICATION.md): 103 runs 118 of them in 32 s of Miri's time, leaving
    // margin. 103 is prime, so the sample spreads over the three modes, both suites and
    // every property rather than repeating one column of the loop.
    let stride = if cfg!(miri) { 103 } else { 1 };
    let mut t = Tally::default();
    let mut k = 0usize;
    // The properties of the subset, found once: looking each up inside the loop below
    // cost most of the test's time under Miri.
    let props: Vec<_> = quirks_table::props()
        .iter()
        .filter(|p| property(&cps(p.prop)).is_some())
        .collect();
    for (mode, quirks) in [
        ("quirks", true),
        ("limited-quirks", false),
        ("no-quirks", false),
    ] {
        for case in quirks_table::cases() {
            for p in props.iter().filter(|p| p.suite == case.suite) {
                if case.shorthand && !p.shorthand {
                    continue;
                }
                k = k.saturating_add(1);
                if !k.is_multiple_of(stride) {
                    continue;
                }
                let reference = if quirks { case.q } else { case.s };
                let checks: Vec<&str> = std::iter::once(p.check)
                    .chain(p.also.iter().copied())
                    .collect();
                let test = parse(&cps(p.prop), &cps(case.input), quirks).unwrap_or_default();
                // A reference the property drops is a declaration dropped: the element keeps
                // the initial value, so the test declaration must be dropped too.
                let given = reference.is_some();
                let reference = reference
                    .map(|r| parse(&cps(p.prop), &cps(r), quirks).unwrap_or_default())
                    .unwrap_or_default();
                let result = if reference.is_empty() {
                    if test.is_empty() {
                        Ok(())
                    } else {
                        Err("set, but the reference is not".to_owned())
                    }
                } else if test.is_empty() {
                    Err("not set".to_owned())
                } else {
                    let differ: Vec<String> = checks
                        .iter()
                        .filter_map(|c| {
                            let a = get_property_value(&test, &cps(c));
                            let b = get_property_value(&reference, &cps(c));
                            (a != b).then(|| format!("{c} {a:?} != {b:?}"))
                        })
                        .collect();
                    if differ.is_empty() {
                        Ok(())
                    } else {
                        Err(differ.join(", "))
                    }
                };
                let expected = QUIRK_CASES
                    .iter()
                    .find(|(s, i, _)| *s == case.suite && *i == case.input)
                    .map(|(_, _, why)| *why)
                    .or_else(|| {
                        (given && case.input.contains("calc("))
                            .then_some("calc() is not in the subset")
                    });
                t.add(
                    format!(
                        "{}:{} ({mode}) {}: {:?}",
                        case.suite, case.line, p.prop, case.input
                    ),
                    result,
                    expected,
                );
            }
        }
    }
    // The declarations the quirk must not apply to, in quirks mode.
    for (suite, line, declaration, _) in quirks_table::excluded() {
        let Some((name, value)) = declaration.split_once(':') else {
            t.failures
                .push(format!("{suite}:{line} {declaration:?} has no colon"));
            continue;
        };
        if property(&cps(name)).is_none() {
            continue;
        }
        let set = parse(&cps(name), &cps(value), true).is_some();
        t.add(
            format!("{suite}:{line} (quirks) excluded {declaration:?}"),
            if set { Err("set".to_owned()) } else { Ok(()) },
            None,
        );
    }
    t.report("WPT quirks/unitless-length and quirks/hashless-hex-color");
    assert!(t.failures.is_empty(), "{}", t.failures.join("\n"));
}
