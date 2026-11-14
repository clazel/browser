//! The selector parser and serializer against WPT `css/selectors/parsing/` (phase-5.md item
//! 5.5), and matching against small documents built with `clazel-dom`'s arena.
//!
//! Each case of the converted table is one unit. It passes if the parser says it is valid
//! exactly when the page does and, if valid, the serialization is one of those the page
//! accepts. A case that fails is an expected failure only if [`expected_failure`] gives it a
//! class, a reason and the exact way it fails ([`Failure`]: parsed as invalid, parsed as valid
//! with this serialization, or serialized as this); a different failure, any other failure,
//! and any expected failure that passes, fails the test, and each class has a pinned count.
//! The cases WPT calls invalid on pages of unsupported features are rejected only because the
//! whole feature is: they are counted as expected failures, not passes.

use std::collections::BTreeMap;

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_selectors::exec_match::matches;
use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_serialize::serialize;
use clazel_selectors::exec_specificity::list_specificity_of;

/// One check of a WPT page. A string is UTF-16 code units, as JavaScript has it.
struct Case {
    file: &'static str,
    line: usize,
    helper: &'static str,
    selector: &'static [u16],
    valid: bool,
    serialized: &'static [&'static [u16]],
}

include!("generated/wpt_css_selectors.rs");

/// UTF-16 as code points, a lone surrogate becoming U+FFFD as a browser's string would.
fn code_points(units: &[u16]) -> Vec<u32> {
    char::decode_utf16(units.iter().copied())
        .map(|r| r.map_or(0xFFFD, u32::from))
        .collect()
}

/// A string of code points.
fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Code points as text, for messages.
fn text(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// Pages of features outside item 5.5's subset (spec.rs's modelling choices). The parser
/// rejects every selector that names one of these features, so on these pages:
/// - what WPT calls valid fails, as "parsed as invalid" ([`Failure::Rejected`]);
/// - what WPT calls invalid is rejected too, but only because the whole feature is, not for
///   the reason the page tests. Those cases are not passes: [`wpt_css_selectors_parsing`]
///   tallies them apart, as expected failures.
const UNSUPPORTED_PAGES: &[(&str, &str)] = &[
    (
        "parse-has.html",
        ":has() is deferred to Phase 8; this UA treats it as unsupported, so invalid",
    ),
    (
        "parse-has-forgiving-selector.html",
        ":has() is deferred to Phase 8",
    ),
    (
        "parse-has-class-prefix.tentative.html",
        ":has() is deferred to Phase 8",
    ),
    (
        "parse-has-slotted.tentative.html",
        ":has() and ::slotted() are not in the subset",
    ),
    (
        "parse-has-disallow-nesting-has-inside-has.html",
        ":has() is deferred to Phase 8",
    ),
    (
        "parse-part.html",
        "::part() (shadow DOM) is not in the subset",
    ),
    (
        "parse-slotted.html",
        "::slotted() (shadow DOM) is not in the subset",
    ),
    (
        "parse-state.html",
        ":state() (custom elements) is not in the subset",
    ),
    ("parse-heading.html", ":heading is not in the subset"),
];

/// How a case that WPT and the parser disagree on disagrees.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Failure {
    /// WPT calls the selector valid; the parser calls it invalid.
    Rejected,
    /// WPT calls the selector invalid; the parser accepts it, with this serialization.
    Accepted(String),
    /// WPT calls the selector valid and the parser accepts it, but its serialization is none
    /// of those WPT accepts: this one.
    Serialized(String),
}

/// A kind of expected failure. Each has the count of cases it must hold, since the table
/// is fixed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    /// `.foo-*`, a tentative proposal in no standard pinned here.
    ClassPrefix,
    /// `:host`, `:host()`.
    ShadowHost,
    /// `:has()`.
    Has,
    /// `::part()`.
    ShadowPart,
    /// A forgiving list whose invalid item the parser drops where engines keep its text.
    ForgivingDropsItem,
    /// A valid case on a page of an unsupported feature, with no more specific class.
    UnsupportedPage,
    /// The one case WPT calls invalid and the parser accepts.
    BadTokenInIs,
}

impl Class {
    /// The number of cases of this class in the WPT table (when all of it is run).
    fn count(self) -> usize {
        match self {
            Class::ClassPrefix => 11,
            Class::ShadowHost => 15,
            Class::Has => 43,
            Class::ShadowPart => 34,
            Class::ForgivingDropsItem => 8,
            Class::UnsupportedPage => 42,
            Class::BadTokenInIs => 1,
        }
    }

    fn reason(self) -> &'static str {
        match self {
            Class::ClassPrefix => {
                "class-prefix selectors (.foo-*) are a tentative proposal, in no standard pinned here"
            }
            Class::ShadowHost => ":host() (shadow DOM) is not in the subset",
            Class::Has => ":has() is deferred to Phase 8",
            Class::ShadowPart => "::part() (shadow DOM) is not in the subset",
            Class::ForgivingDropsItem => {
                "the forgiving list drops the invalid item; engines keep its text for \
                 serialization, which CSSOM does not specify, and spec.rs serializes what was kept"
            }
            Class::UnsupportedPage => "the page's feature is not in the subset",
            Class::BadTokenInIs => {
                "WPT calls this invalid by <any-value>'s rule against bad tokens; its argument \
                 holds an unclosed [ block that swallows the ), which CSS Syntax closes at EOF, \
                 so spec.rs keeps :is() valid with the item dropped. Not resolved; see the PR"
            }
        }
    }
}

/// Selectors WPT calls valid whose argument has an item that is invalid here: the parser
/// accepts the selector and serializes what is left of it, as §18.1's "forgiving selector
/// list" says ("invalid or unsupported" items are dropped, the rest kept), where engines
/// keep the item's text. `(page, selector, serialization)`, worked out by hand:
/// - `.foo-*` is no selector here, so `:is(.foo-*)` is `:is()`; likewise `.b:has(.c) .d`
///   (`:has()` is unsupported), `::before` (not valid inside `:is()`, §4.2), and an empty
///   item (`,,,`) or an item with only a pseudo-element and `:HOVER` (`::before:HOVER`).
/// - `::before:HOVER, .a` keeps only `.a`.
const FORGIVING_DROPS: &[(&str, &str, &str)] = &[
    ("parse-class-prefix.tentative.html", ":is(.foo-*)", ":is()"),
    ("parse-has.html", ".a:is(.b:has(.c) .d)", ".a:is()"),
    ("parse-is-where.html", ":is(::before)", ":is()"),
    ("parse-is-where.html", ":where(::before)", ":where()"),
    ("parse-is-where.html", ":is(,,,)", ":is()"),
    ("parse-is-where.html", ":where(,,,)", ":where()"),
    ("parse-is-where.html", ":is(::before:HOVER, .a)", ":is(.a)"),
    (
        "parse-is-where.html",
        ":where(::before:HOVER, .a)",
        ":where(.a)",
    ),
    ("parse-is-where.html", ":is(::before:HOVER  )", ":is()"),
    (
        "parse-is-where.html",
        ":where(::before:HOVER  )",
        ":where()",
    ),
];

/// A case expected to fail, how, and why.
struct Expected {
    class: Class,
    failure: Failure,
}

/// The expected failure of `case`, or `None` if it must pass. Cases are picked into a class
/// by the text of the selector or its page, but the failure each must show is pinned
/// exactly, so that a feature that is half implemented, and starts accepting with the wrong
/// result, fails here rather than keeping its place in the list.
fn expected_failure(case: &Case) -> Option<Expected> {
    let selector = String::from_utf16_lossy(case.selector);
    if !case.valid {
        // WPT calls it invalid.
        if case.file == "parse-is-where.html" && selector.starts_with(":is(# C4") {
            return Some(Expected {
                class: Class::BadTokenInIs,
                failure: Failure::Accepted(":is()".to_owned()),
            });
        }
        return None;
    }
    let class = if case.file == "parse-class-prefix.tentative.html" && selector.contains("-*") {
        Class::ClassPrefix
    } else if selector.contains(":host") {
        Class::ShadowHost
    } else if selector.contains(":has(") {
        Class::Has
    } else if selector.contains("::part(") {
        Class::ShadowPart
    } else if case.file == "parse-is-where.html"
        && FORGIVING_DROPS
            .iter()
            .any(|(f, s, _)| *f == case.file && *s == selector)
    {
        Class::ForgivingDropsItem
    } else if UNSUPPORTED_PAGES.iter().any(|(f, _)| *f == case.file) {
        Class::UnsupportedPage
    } else {
        return None;
    };
    let failure = FORGIVING_DROPS
        .iter()
        .find(|(f, s, _)| *f == case.file && *s == selector)
        .map_or(Failure::Rejected, |(_, _, out)| {
            Failure::Serialized((*out).to_owned())
        });
    Some(Expected { class, failure })
}

/// True if `case` is one WPT calls invalid, on a page of an unsupported feature: whatever
/// the parser answers is not evidence about the case's own reason.
fn invalid_on_unsupported_page(case: &Case) -> bool {
    !case.valid && UNSUPPORTED_PAGES.iter().any(|(f, _)| *f == case.file)
}

/// How the parser and serializer disagree with one case, or `Ok` if they agree.
fn run(case: &Case) -> Result<(), Failure> {
    let input = code_points(case.selector);
    let parsed = parse_selector(&input);
    match (&parsed, case.valid) {
        (None, false) => Ok(()),
        (None, true) => Err(Failure::Rejected),
        (Some(s), false) => Err(Failure::Accepted(text(&serialize(s)))),
        (Some(s), true) => {
            let out = serialize(s);
            if case.serialized.iter().any(|e| code_points(e) == out) {
                Ok(())
            } else {
                Err(Failure::Serialized(text(&out)))
            }
        }
    }
}

#[test]
fn wpt_css_selectors_parsing() {
    // Under Miri a stride of the cases, to finish in about a minute (docs/VERIFICATION.md).
    let stride = if cfg!(miri) { 23 } else { 1 };
    let mut pass = 0usize;
    let mut xfail = 0usize;
    // Of `xfail`: the cases WPT calls invalid that the parser rejects, on pages of unsupported
    // features. They are not passes; the summary line has no field for them.
    let mut wrong_reason = 0usize;
    let mut classes: BTreeMap<Class, usize> = BTreeMap::new();
    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;
    for (k, case) in WPT.iter().enumerate() {
        if k % stride != 0 {
            continue;
        }
        ran = ran.saturating_add(1);
        let selector = String::from_utf16_lossy(case.selector);
        let at = format!(
            "{}:{} {:?} ({})",
            case.file, case.line, selector, case.helper
        );
        match (run(case), expected_failure(case)) {
            (Ok(()), None) => {
                if invalid_on_unsupported_page(case) {
                    wrong_reason = wrong_reason.saturating_add(1);
                    xfail = xfail.saturating_add(1);
                } else {
                    pass = pass.saturating_add(1);
                }
            }
            (Err(got), Some(expected)) => {
                if got == expected.failure {
                    xfail = xfail.saturating_add(1);
                    let n = classes.entry(expected.class).or_insert(0);
                    *n = n.saturating_add(1);
                } else {
                    failures.push(format!(
                        "{at}: expected to fail as {:?} ({}) but failed as {got:?}",
                        expected.failure,
                        expected.class.reason()
                    ));
                }
            }
            (Ok(()), Some(expected)) => {
                // An expected failure that passes is a list out of date.
                failures.push(format!(
                    "{at} passes but is listed: {}",
                    expected.class.reason()
                ));
            }
            (Err(got), None) => failures.push(format!("{at}: {got:?}")),
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT css/selectors/parsing\" pass={pass} xfail={xfail} fail={} total={}",
        failures.len(),
        ran
    );
    println!(
        "clazel-selectors: of the {xfail} xfail, {wrong_reason} are cases WPT calls invalid on pages \
         of unsupported features, rejected for the wrong reason (feature unsupported), not passes"
    );
    // The one check the converter could not read is a direct test() through the DOM's
    // matches(); it is not counted.
    assert_eq!(NOT_RUN.len(), 1);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    if stride == 1 {
        // The table is fixed, so each class holds exactly its cases.
        for class in [
            Class::ClassPrefix,
            Class::ShadowHost,
            Class::Has,
            Class::ShadowPart,
            Class::ForgivingDropsItem,
            Class::UnsupportedPage,
            Class::BadTokenInIs,
        ] {
            assert_eq!(
                classes.get(&class).copied().unwrap_or(0),
                class.count(),
                "{class:?}"
            );
        }
        assert_eq!(
            wrong_reason, 60,
            "invalid cases on pages of unsupported features"
        );
        assert_eq!(
            xfail,
            wrong_reason
                + [
                    Class::ClassPrefix,
                    Class::ShadowHost,
                    Class::Has,
                    Class::ShadowPart,
                    Class::ForgivingDropsItem,
                    Class::UnsupportedPage,
                    Class::BadTokenInIs,
                ]
                .iter()
                .map(|c| c.count())
                .sum::<usize>()
        );
        assert_eq!(pass + xfail, WPT.len());
    }
}

// ------------------------------------------------------------------------------------
// Matching and specificity on small documents
// ------------------------------------------------------------------------------------

/// An HTML element named `name` with no-namespace attributes `attrs`.
fn element(arena: &mut Arena, name: &str, attrs: &[(&str, &str)]) -> usize {
    let id = arena
        .create(ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: cps(name),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        })
        .unwrap_or(0);
    for (n, v) in attrs {
        arena.append_attribute(
            id,
            ExecAttr {
                namespace: None,
                prefix: None,
                local_name: cps(n),
                value: cps(v),
            },
        );
    }
    id
}

/// A text node.
fn text_node(arena: &mut Arena, data: &str) -> usize {
    arena
        .create(ExecKind::Text { data: cps(data) })
        .unwrap_or(0)
}

/// `<html><body><div id=main class="a B"><p lang=EN>…</p> <p></p><a href=/>x</a></div>
/// <ul><li><li class=x><li></ul></body></html>`; returns the arena and the nodes by name.
fn document(mode: DocumentMode) -> (Arena, Vec<(&'static str, usize)>) {
    let mut arena = Arena::new(Vec::new());
    arena.set_mode(mode);
    let html = element(&mut arena, "html", &[]);
    let body = element(&mut arena, "body", &[]);
    let div = element(&mut arena, "div", &[("id", "main"), ("class", "a B")]);
    let p1 = element(&mut arena, "p", &[("lang", "EN")]);
    let t1 = text_node(&mut arena, "words");
    let ws = text_node(&mut arena, "  ");
    let p2 = element(&mut arena, "p", &[]);
    let a = element(&mut arena, "a", &[("href", "/")]);
    let ul = element(&mut arena, "ul", &[]);
    let li1 = element(&mut arena, "li", &[]);
    let li2 = element(&mut arena, "li", &[("class", "x")]);
    let li3 = element(&mut arena, "li", &[]);
    arena.append(0, html);
    arena.append(html, body);
    arena.append(body, div);
    arena.append(div, p1);
    arena.append(p1, t1);
    arena.append(div, ws);
    arena.append(div, p2);
    arena.append(div, a);
    arena.append(body, ul);
    arena.append(ul, li1);
    arena.append(ul, li2);
    arena.append(ul, li3);
    let names = vec![
        ("html", html),
        ("body", body),
        ("div", div),
        ("p1", p1),
        ("p2", p2),
        ("a", a),
        ("ul", ul),
        ("li1", li1),
        ("li2", li2),
        ("li3", li3),
    ];
    (arena, names)
}

/// The names of the elements `selector` matches.
fn matched(mode: DocumentMode, selector: &str) -> Vec<&'static str> {
    let (arena, names) = document(mode);
    let Some(s) = parse_selector(&cps(selector)) else {
        return vec!["<invalid>"];
    };
    names
        .iter()
        .filter(|(_, id)| matches(&arena, &s, *id))
        .map(|(n, _)| *n)
        .collect()
}

#[test]
fn matching_follows_the_selectors() {
    use DocumentMode::{NoQuirks, Quirks};
    let cases: &[(&str, &[&str])] = &[
        ("p", &["p1", "p2"]),
        ("P", &["p1", "p2"]),
        ("*|li", &["li1", "li2", "li3"]),
        ("|li", &[]),
        ("div > p", &["p1", "p2"]),
        ("body p", &["p1", "p2"]),
        ("html > p", &[]),
        ("p + p", &["p2"]),
        ("p ~ a", &["a"]),
        ("li + li + li", &["li3"]),
        ("#main", &["div"]),
        ("#MAIN", &[]),
        (".a", &["div"]),
        (".b", &[]),
        ("[lang|=en]", &["p1"]),
        ("[lang=en s]", &[]),
        ("[class~=B]", &["div"]),
        ("[class~=b i]", &["div"]),
        ("[href^='/']", &["a"]),
        ("[href$='/']", &["a"]),
        ("[href*='']", &[]),
        (":link", &["a"]),
        (":visited", &[]),
        (":any-link", &["a"]),
        (":root", &["html"]),
        ("p:empty", &["p2"]),
        ("li:first-child", &["li1"]),
        ("li:last-child", &["li3"]),
        ("li:nth-child(2n+1)", &["li1", "li3"]),
        ("li:nth-last-child(1)", &["li3"]),
        ("p:first-of-type", &["p1"]),
        ("p:last-of-type", &["p2"]),
        ("a:only-of-type", &["a"]),
        ("ul:only-child", &[]),
        ("html:only-child", &["html"]),
        (":is(p, li.x)", &["p1", "p2", "li2"]),
        (":where(#main)", &["div"]),
        ("li:not(.x)", &["li1", "li3"]),
        (":is()", &[]),
        ("a:hover", &[]),
        ("p::before", &[]),
        ("body :is(ul > li) + li", &["li2", "li3"]),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (selector, expected) in cases {
        let got = matched(NoQuirks, selector);
        if got != *expected {
            wrong.push(format!("{selector:?}: {got:?}, expected {expected:?}"));
        }
    }
    // Quirks mode: class and ID selectors match ASCII case-insensitively.
    for (selector, expected) in [("#MAIN", &["div"][..]), (".b", &["div"][..])] {
        let got = matched(Quirks, selector);
        if got != expected {
            wrong.push(format!(
                "quirks {selector:?}: {got:?}, expected {expected:?}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn specificity_follows_section_17() {
    // §17's examples, and those of :is(), :not() and :where().
    let cases: &[(&str, (u32, u32, u32))] = &[
        ("*", (0, 0, 0)),
        ("LI", (0, 0, 1)),
        ("UL LI", (0, 0, 2)),
        ("UL OL+LI", (0, 0, 3)),
        ("H1 + *[REL=up]", (0, 1, 1)),
        ("UL OL LI.red", (0, 1, 3)),
        ("LI.red.level", (0, 2, 1)),
        ("#x34y", (1, 0, 0)),
        ("#s12:not(FOO)", (1, 0, 1)),
        (".foo :is(.bar, #baz)", (1, 1, 0)),
        (":is(em, #foo)", (1, 0, 0)),
        (".qux:where(em, #foo#bar#baz)", (0, 1, 0)),
        (":not(em, strong#foo)", (1, 0, 1)),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (selector, (a, b, c)) in cases {
        let Some(s) = parse_selector(&cps(selector)) else {
            wrong.push(format!("{selector:?} did not parse"));
            continue;
        };
        let got = list_specificity_of(&s, s.lists.len().saturating_sub(1));
        if (got.a, got.b, got.c) != (*a, *b, *c) {
            wrong.push(format!(
                "{selector:?}: ({}, {}, {}), expected ({a}, {b}, {c})",
                got.a, got.b, got.c
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn deep_nesting_is_refused_not_overflowed() {
    // Under Miri 40 levels, still past MAX_NESTING (32): tokenizing 10,000 levels there
    // takes hours, and what Miri checks is the code path, which 40 already takes.
    let depth = if cfg!(miri) { 40 } else { 10_000 };
    let mut s = String::new();
    for _ in 0..depth {
        s.push_str(":is(");
    }
    s.push('a');
    for _ in 0..depth {
        s.push(')');
    }
    assert!(parse_selector(&cps(&s)).is_none());
    let mut shallow = String::new();
    for _ in 0..8 {
        shallow.push_str(":is(");
    }
    shallow.push('a');
    for _ in 0..8 {
        shallow.push(')');
    }
    assert!(parse_selector(&cps(&shallow)).is_some());
}
