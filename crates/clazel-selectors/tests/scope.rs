//! `:scope` through the parser and the matcher: Selectors Level 4 §9.4 "The Reference Element
//! Pseudo-class: `:scope`", with `matches_scoped`'s scoping root and with `matches`' none.
//!
//! Every expected set was worked out by hand from the text, not from a run. The arena:
//!
//! ```text
//! html > body >
//!   div#a > p#b > span#s,  p#c
//!   div#e
//! ```

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_selectors::exec_match::{matches, matches_scoped};
use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_serialize::serialize;

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn element(arena: &mut Arena, name: &str, id: Option<&str>) -> usize {
    let node = arena
        .create(ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: cps(name),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        })
        .unwrap_or(0);
    if let Some(id) = id {
        arena.append_attribute(
            node,
            ExecAttr {
                namespace: None,
                prefix: None,
                local_name: cps("id"),
                value: cps(id),
            },
        );
    }
    node
}

/// The document, and its elements by id (`html` and `body` have none: they are labelled by
/// their names), in document order.
fn document() -> (Arena, Vec<(&'static str, usize)>) {
    let mut a = Arena::new(Vec::new());
    a.set_mode(DocumentMode::NoQuirks);
    let mut names: Vec<(&'static str, usize)> = Vec::new();
    let mut add = |a: &mut Arena, label: &'static str, parent: usize, node: usize| {
        a.append(parent, node);
        names.push((label, node));
        node
    };
    let n = element(&mut a, "html", None);
    let html = add(&mut a, "html", 0, n);
    let n = element(&mut a, "body", None);
    let body = add(&mut a, "body", html, n);
    let n = element(&mut a, "div", Some("a"));
    let da = add(&mut a, "a", body, n);
    let n = element(&mut a, "p", Some("b"));
    let pb = add(&mut a, "b", da, n);
    let n = element(&mut a, "span", Some("s"));
    add(&mut a, "s", pb, n);
    let n = element(&mut a, "p", Some("c"));
    add(&mut a, "c", da, n);
    let n = element(&mut a, "div", Some("e"));
    add(&mut a, "e", body, n);
    (a, names)
}

/// The labels of the elements `selector` matches, with the scoping root labelled `scope` (or
/// none), or `["<invalid>"]`.
fn matched(selector: &str, scope: Option<&str>) -> Vec<&'static str> {
    let (arena, names) = document();
    let Some(s) = parse_selector(&cps(selector)) else {
        return vec!["<invalid>"];
    };
    let root = scope.map(|label| {
        names
            .iter()
            .find(|(n, _)| *n == label)
            .map(|(_, id)| *id)
            .unwrap_or(usize::MAX)
    });
    names
        .iter()
        .filter(|(_, id)| match root {
            Some(r) => matches_scoped(&arena, &s, Some(r), *id),
            None => matches(&arena, &s, *id),
        })
        .map(|(n, _)| *n)
        .collect()
}

#[test]
fn with_a_scoping_root_scope_is_that_element() {
    // §9.4: ":scope represents this scoping root".
    assert_eq!(matched(":scope", Some("a")), ["a"]);
    assert_eq!(matched(":scope", Some("s")), ["s"]);
    assert_eq!(matched("div:scope", Some("a")), ["a"]);
    // ... and no other element, whatever its type.
    assert_eq!(matched("p:scope", Some("a")), Vec::<&str>::new());
    // §3.7: pseudo-class names are ASCII case-insensitive.
    assert_eq!(matched(":SCOPE", Some("e")), ["e"]);
    // The root element is not special when there is a scoping root.
    assert_eq!(matched(":scope", Some("body")), ["body"]);
}

#[test]
fn without_a_scoping_root_scope_is_root() {
    // §9.4: "If there is no scoping root then :scope represents the root of the tree the
    // element is in (equivalent to :host in a shadow tree, or :root otherwise)."
    assert_eq!(matched(":scope", None), ["html"]);
    assert_eq!(matched(":scope", None), matched(":root", None));
}

#[test]
fn scope_in_combinators_lists_and_functions() {
    // §16: the scoping root is the element `:scope` stands for wherever it is.
    assert_eq!(matched(":scope > p", Some("a")), ["b", "c"]);
    assert_eq!(matched(":scope p", Some("a")), ["b", "c"]);
    assert_eq!(matched(":scope span", Some("a")), ["s"]);
    assert_eq!(matched(":scope > span", Some("a")), Vec::<&str>::new());
    assert_eq!(matched(":scope + div", Some("a")), ["e"]);
    assert_eq!(matched(":scope ~ div", Some("a")), ["e"]);
    assert_eq!(matched(":scope > div", Some("body")), ["a", "e"]);
    // §4.2, §4.3: inside :is() and :not().
    assert_eq!(matched(":is(:scope, #e)", Some("a")), ["a", "e"]);
    assert_eq!(
        matched("div:not(:scope)", Some("a")),
        ["e"],
        "div:not(:scope)"
    );
    // The same selectors with no scoping root, where :scope is html.
    assert_eq!(matched(":scope > body", None), ["body"]);
    assert_eq!(matched(":scope > p", None), Vec::<&str>::new());
}

#[test]
fn a_scoping_root_that_is_not_an_element_matches_nothing() {
    // The modelling choice in `spec.rs`: only a true element is a scoping root. The document
    // node (0) is not an element, and no element is it.
    let (arena, names) = document();
    let parsed = parse_selector(&cps(":scope"));
    assert!(parsed.is_some(), ":scope parses");
    if let Some(s) = parsed {
        for (_, id) in &names {
            assert!(!matches_scoped(&arena, &s, Some(0), *id));
        }
    }
}

#[test]
fn scope_serializes_as_itself() {
    // CSSOM "serialize a simple selector": ":" and the name of the pseudo-class, in lower case.
    let parsed = parse_selector(&cps("a:SCOPE > b"));
    assert!(parsed.is_some(), "a:SCOPE > b parses");
    if let Some(s) = parsed {
        assert_eq!(serialize(&s), cps("a:scope > b"));
    }
}

#[test]
fn scope_is_not_a_user_action_pseudo_class() {
    // §18: only the user action pseudo-classes may follow a pseudo-element.
    assert!(parse_selector(&cps("p::before:scope")).is_none());
    assert!(parse_selector(&cps("p::before:hover")).is_some());
}
