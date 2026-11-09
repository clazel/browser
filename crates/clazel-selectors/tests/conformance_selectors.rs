//! The selector parser and serializer against WPT `css/selectors/parsing/` (phase-5.md item
//! 5.5), and matching against small documents built with `clazel-dom`'s arena.
//!
//! Each case of the converted table is one unit. It passes if the parser says it is valid
//! exactly when the page does and, if valid, the serialization is one of those the page
//! accepts. A case that fails is an expected failure only if [`expected_failure`] gives it a
//! reason; any other failure, and any expected failure that passes, fails the test.

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

/// Pages, or parts of the grammar, outside item 5.5's subset (spec.rs's modelling choices).
const OUT_OF_SUBSET_PAGES: &[(&str, &str)] = &[
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

/// Single cases expected to fail, with the reason.
fn case_reason(file: &str, selector: &str) -> Option<&'static str> {
    if file == "parse-is-where.html" && selector.starts_with(":is(# C4") {
        return Some(
            "WPT calls this invalid by <any-value>'s rule against bad tokens; its argument holds \
             an unclosed [ block that swallows the ), which CSS Syntax closes at EOF, so \
             spec.rs keeps :is() valid with the item dropped. Not resolved; see the PR",
        );
    }
    if !valid_in_wpt(file, selector) {
        return None;
    }
    if file == "parse-class-prefix.tentative.html" && selector.contains("-*") {
        return Some(
            "class-prefix selectors (.foo-*) are a tentative proposal, in no standard pinned here",
        );
    }
    if selector.contains(":host") {
        return Some(":host() (shadow DOM) is not in the subset");
    }
    if selector.contains(":has(") {
        return Some(":has() is deferred to Phase 8");
    }
    if selector.contains("::part(") {
        return Some("::part() (shadow DOM) is not in the subset");
    }
    if file == "parse-is-where.html"
        && (selector.contains(",,,") || selector.contains("::before"))
        && !selector.starts_with(":is(div)")
        && !selector.starts_with(":where(div)")
    {
        return Some(
            "the forgiving list drops the invalid item; engines keep its text for \
             serialization, which CSSOM does not specify, and spec.rs serializes what was kept",
        );
    }
    None
}

/// True if the page calls `selector` valid.
fn valid_in_wpt(file: &str, selector: &str) -> bool {
    WPT.iter()
        .any(|c| c.file == file && c.valid && String::from_utf16_lossy(c.selector) == selector)
}

/// Why a case is expected to fail, or `None`. Only cases WPT calls valid can fail for being
/// outside the subset, since the parser calls what it does not support invalid.
fn expected_failure(case: &Case) -> Option<&'static str> {
    let selector = String::from_utf16_lossy(case.selector);
    if let Some(reason) = case_reason(case.file, &selector) {
        return Some(reason);
    }
    if !case.valid {
        return None;
    }
    OUT_OF_SUBSET_PAGES
        .iter()
        .find(|(file, _)| *file == case.file)
        .map(|(_, reason)| *reason)
}

/// What the parser and serializer do with one case: `Ok` if it passes.
fn run(case: &Case) -> Result<(), String> {
    let input = code_points(case.selector);
    let parsed = parse_selector(&input);
    match (&parsed, case.valid) {
        (None, false) => Ok(()),
        (None, true) => Err("parsed as invalid".to_owned()),
        (Some(s), false) => Err(format!("parsed as valid: {}", text(&serialize(s)))),
        (Some(s), true) => {
            let out = serialize(s);
            if case.serialized.iter().any(|e| code_points(e) == out) {
                Ok(())
            } else {
                Err(format!("serialized as {:?}", text(&out)))
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
    let mut failures: Vec<String> = Vec::new();
    let mut ran = 0usize;
    for (k, case) in WPT.iter().enumerate() {
        if k % stride != 0 {
            continue;
        }
        ran = ran.saturating_add(1);
        let selector = String::from_utf16_lossy(case.selector);
        match (run(case), expected_failure(case)) {
            (Ok(()), None) => pass = pass.saturating_add(1),
            (Err(_), Some(_)) => xfail = xfail.saturating_add(1),
            (Ok(()), Some(reason)) => {
                // An expected failure that passes is a list out of date.
                failures.push(format!(
                    "{}:{} {:?} ({}) passes but is listed: {reason}",
                    case.file, case.line, selector, case.helper
                ));
            }
            (Err(why), None) => failures.push(format!(
                "{}:{} {:?} ({}): {why}",
                case.file, case.line, selector, case.helper
            )),
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT css/selectors/parsing\" pass={pass} xfail={xfail} fail={} total={}",
        failures.len(),
        ran
    );
    // The one check the converter could not read is a direct test() through the DOM's
    // matches(); it is not counted.
    assert_eq!(NOT_RUN.len(), 1);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
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
    let mut s = String::new();
    for _ in 0..10_000 {
        s.push_str(":is(");
    }
    s.push('a');
    for _ in 0..10_000 {
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
