//! WPT `dom/nodes/selectors.js` as data (Phase 7 item 7.13): the table of
//! selectors and the ids they must find, run through `clazel_web::selectors`
//! on the document of `ParentNode-querySelector-All-content.html`, parsed by
//! `clazel-treebuilder`. No JavaScript engine is involved: the harness
//! `ParentNode-querySelector-All.js` and `Element-matches.js` are
//! re-implemented here on the arena, step by step:
//!
//! - `setupSpecialElements` adds the `null` and `undefined` elements and the
//!   namespace test elements to `#root`, then the harness clones `#root` into
//!   the four contexts: the document, the in-document element (with a
//!   clone, marked `data-clone`, appended to the body that must never be
//!   found), a detached element and a document fragment.
//! - `validSelectors` entries with `TEST_QSA` run `querySelectorAll` and
//!   `querySelector` in each context their `exclude` allows (the document
//!   type is `html`); those with `TEST_MATCH` run `matches` on each expected
//!   id and each `unexpected` id, in the document.
//! - `invalidSelectors` must be `SyntaxError`s from `querySelector`,
//!   `querySelectorAll` and (on an element) `matches` and `closest`.
//! - The special selectors the script harness stringifies (`null`,
//!   `undefined`) and the tree order of `*`.
//!
//! Not run, because the test needs something this crate does not have:
//! `scopedSelectors` (the `find()` tests, whose `:scope` and reference-node
//! arguments `clazel-selectors` and the `matches` of this crate do not take),
//! the `.xht`/`.xhtml` variants (an XML parser), and the other `dom/nodes`
//! pages that are scripts about the DOM (mutation, shadow roots, `:has` in a
//! live tree and so on), which need the bindings.
//!
//! A unit is one selector in one context (or one `matches` entry); under
//! Miri every 40th selector runs, in the document and the element only. A
//! unit that fails must fall in a [`Class`] below, whose rule is a predicate
//! over the selector; a class that applies to nothing fails too.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::selectors::{SyntaxError, closest, matches, query_selector, query_selector_all};

/// `unwrap` for tests (the workspace denies `unwrap`/`expect`).
trait Must<T> {
    fn must(self) -> T;
}

impl<T> Must<T> for Option<T> {
    fn must(self) -> T {
        match self {
            Some(v) => v,
            None => unreachable!("expected a value"),
        }
    }
}

impl<T, E> Must<T> for Result<T, E> {
    fn must(self) -> T {
        match self {
            Ok(v) => v,
            Err(_) => unreachable!("expected Ok"),
        }
    }
}

const SELECTORS_JS: &str = include_str!("data/wpt-web/dom/nodes/selectors.js");
const CONTENT: &str =
    include_str!("data/wpt-web/dom/nodes/ParentNode-querySelector-All-content.html");

const TEST_QSA: u32 = 0x01;
const TEST_MATCH: u32 = 0x10;

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn u(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn text(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

// ---------------------------------------------------------------------
// Reading selectors.js: a scanner for the table's one-line entries.
// ---------------------------------------------------------------------

/// One entry of `validSelectors` or `invalidSelectors`.
struct Entry {
    name: String,
    selector: String,
    expect: Vec<String>,
    unexpected: Vec<String>,
    exclude: Vec<String>,
    test_type: u32,
}

/// A JavaScript string literal at the start of `s` (after spaces): its value
/// and what follows it. A backslash before a character with no escape of its
/// own gives the character (`\_` is `_`).
fn js_string(s: &str) -> Option<(String, &str)> {
    let s = s.trim_start();
    let mut chars = s.char_indices();
    let (_, quote) = chars.next()?;
    if quote != '"' && quote != '\'' {
        return None;
    }
    let mut out = String::new();
    while let Some((i, c)) = chars.next() {
        if c == quote {
            return Some((out, s.get(i.saturating_add(1)..)?));
        }
        if c != '\\' {
            out.push(c);
            continue;
        }
        let (_, e) = chars.next()?;
        match e {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            'f' => out.push('\u{c}'),
            'u' => {
                let mut v = 0u32;
                for _ in 0..4 {
                    v = v
                        .saturating_mul(16)
                        .saturating_add(chars.next()?.1.to_digit(16)?);
                }
                out.push(char::from_u32(v)?);
            }
            other => out.push(other),
        }
    }
    None
}

/// The strings of the array literal that follows `key:` in `line`.
fn js_list(line: &str, key: &str) -> Vec<String> {
    let Some(at) = line.find(&format!("{key}: [")) else {
        return Vec::new();
    };
    let mut rest = line
        .get(at.saturating_add(key.len()).saturating_add(3)..)
        .unwrap_or("");
    let mut out = Vec::new();
    while let Some((s, after)) = js_string(rest) {
        out.push(s);
        rest = after.trim_start().trim_start_matches(',');
    }
    out
}

fn entries(var: &str) -> Vec<Entry> {
    let start = SELECTORS_JS.find(&format!("var {var} = [")).must();
    let body = &SELECTORS_JS[start..];
    let end = body.find("\n];").must();
    let mut out = Vec::new();
    for line in body[..end].lines() {
        let line = line.trim();
        let Some(rest) = line.strip_prefix("{name:") else {
            continue;
        };
        let (name, rest) = js_string(rest).must();
        let at = rest.find("selector:").must();
        let (selector, after) =
            js_string(rest.get(at.saturating_add("selector:".len())..).must()).must();
        // The lists and the type are read from what follows the selector, so
        // that a selector containing "expect: [" is not mistaken.
        let tail = after;
        let test_type = tail.find("testType:").map_or(0, |t| {
            let flags = tail[t..].split('}').next().unwrap_or("");
            let mut v = 0;
            if flags.contains("TEST_QSA") {
                v |= TEST_QSA;
            }
            if flags.contains("TEST_MATCH") {
                v |= TEST_MATCH;
            }
            v
        });
        out.push(Entry {
            name,
            selector,
            expect: js_list(tail, "expect"),
            unexpected: js_list(tail, "unexpected"),
            exclude: js_list(tail, "exclude"),
            test_type,
        });
    }
    out
}

// ---------------------------------------------------------------------
// The document and the harness.
// ---------------------------------------------------------------------

fn copy_ns(ns: &Namespace) -> Namespace {
    match ns {
        Namespace::Html => Namespace::Html,
        Namespace::MathMl => Namespace::MathMl,
        Namespace::Svg => Namespace::Svg,
        Namespace::XLink => Namespace::XLink,
        Namespace::Xml => Namespace::Xml,
        Namespace::Xmlns => Namespace::Xmlns,
    }
}

fn new_kind(k: &ExecKind) -> ExecKind {
    match k {
        ExecKind::Element {
            namespace,
            prefix,
            local_name,
            attributes,
            ..
        } => ExecKind::Element {
            namespace: namespace.as_ref().map(copy_ns),
            prefix: prefix.clone(),
            local_name: local_name.clone(),
            attributes: attributes
                .iter()
                .map(|a| ExecAttr {
                    namespace: a.namespace.as_ref().map(copy_ns),
                    prefix: a.prefix.clone(),
                    local_name: a.local_name.clone(),
                    value: a.value.clone(),
                })
                .collect(),
            template_contents: None,
            form_owner: None,
        },
        ExecKind::Text { data } => ExecKind::Text { data: data.clone() },
        ExecKind::Comment { data } => ExecKind::Comment { data: data.clone() },
        _ => ExecKind::DocumentFragment { host: None },
    }
}

fn create(arena: &mut Arena, kind: ExecKind) -> usize {
    arena.create(kind).must()
}

fn attribute(arena: &Arena, e: usize, name: &str) -> Option<String> {
    match arena.kind(e) {
        ExecKind::Element { attributes, .. } => attributes
            .iter()
            .find(|a| a.namespace.is_none() && a.local_name == u(name))
            .map(|a| text(&a.value)),
        _ => None,
    }
}

fn id_of(arena: &Arena, e: usize) -> Option<String> {
    attribute(arena, e, "id")
}

/// Every element of the subtree of `root` (inclusive), in tree order.
fn elements_of(arena: &Arena, root: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut stack = vec![root];
    while let Some(n) = stack.pop() {
        if matches!(arena.kind(n), ExecKind::Element { .. }) {
            out.push(n);
        }
        stack.extend(arena.children(n).iter().rev().copied());
    }
    out
}

fn find_id(arena: &Arena, root: usize, id: &str) -> Option<usize> {
    elements_of(arena, root)
        .into_iter()
        .find(|&e| id_of(arena, e).as_deref() == Some(id))
}

fn set_attribute(arena: &mut Arena, e: usize, name: &str, value: &str) {
    arena.append_attribute(
        e,
        ExecAttr {
            namespace: None,
            prefix: None,
            local_name: u(name),
            value: u(value),
        },
    );
}

/// `cloneNode(true)`, detached: copies of the subtree of `src`.
fn deep_clone(arena: &mut Arena, src: usize) -> usize {
    let top = create(arena, new_kind(arena.kind(src)));
    let mut work = vec![(src, top)];
    while let Some((s, d)) = work.pop() {
        let kids: Vec<usize> = arena.children(s).to_vec();
        for k in kids {
            let c = create(arena, new_kind(arena.kind(k)));
            arena.append(d, c);
            work.push((k, c));
        }
    }
    top
}

fn element(arena: &mut Arena, ns: Option<Namespace>, name: &str, id: &str) -> usize {
    let e = create(
        arena,
        ExecKind::Element {
            namespace: ns,
            prefix: None,
            local_name: u(name),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        },
    );
    set_attribute(arena, e, "id", id);
    e
}

/// `setupSpecialElements` of `ParentNode-querySelector-All.js`. The
/// namespace `http://www.example.org/ns` is not one of `clazel-dom`'s six
/// (`Namespace`), so the fourth `div` of each group and the attribute in it
/// are not made: the entries that expect them are in the class
/// "unrepresentable namespace".
fn setup_special_elements(arena: &mut Arena, parent: usize) {
    for name in ["null", "undefined"] {
        let e = create(
            arena,
            ExecKind::Element {
                namespace: Some(Namespace::Html),
                prefix: None,
                local_name: u(name),
                attributes: Vec::new(),
                template_contents: None,
                form_owner: None,
            },
        );
        arena.append(parent, e);
    }
    for (group, prefix) in [
        ("any-namespace", "any-namespace"),
        ("no-namespace", "no-namespace"),
    ] {
        let g = element(arena, Some(Namespace::Html), "div", group);
        for (i, ns) in [Some(Namespace::Html), Some(Namespace::Html), None]
            .into_iter()
            .enumerate()
        {
            let d = element(
                arena,
                ns,
                "div",
                &format!("{prefix}-div{}", i.saturating_add(1)),
            );
            arena.append(g, d);
        }
        arena.append(parent, g);
    }
}

/// The contexts of `ParentNode-querySelector-All.html`.
struct World {
    arena: Arena,
    document: usize,
    /// `#root`, in the document.
    element: usize,
    detached: usize,
    fragment: usize,
}

fn world(with_clone: bool) -> World {
    let (p, _) = parse_real(&NoEnc, &u(CONTENT), Vec::new(), false, false);
    let mut arena = p.arena;
    let document = 0;
    let element = find_id(&arena, document, "root").must();
    setup_special_elements(&mut arena, element);
    let detached = deep_clone(&mut arena, element);
    let fragment = create(&mut arena, ExecKind::DocumentFragment { host: None });
    let in_fragment = deep_clone(&mut arena, element);
    arena.append(fragment, in_fragment);
    // The clone appended to the body before the in-document tests: none of
    // its elements may ever be found.
    if with_clone {
        let out_of_scope = deep_clone(&mut arena, element);
        for e in elements_of(&arena, out_of_scope) {
            set_attribute(&mut arena, e, "data-clone", "");
        }
        let body = find_id(&arena, document, "body").must();
        arena.append(body, out_of_scope);
    }
    World {
        arena,
        document,
        element,
        detached,
        fragment,
    }
}

// ---------------------------------------------------------------------
// Expected failures.
// ---------------------------------------------------------------------

/// A reason why a selector is not expected to pass, as a rule on its entry.
struct Class {
    name: &'static str,
    why: &'static str,
    applies: fn(&Entry) -> bool,
}

const CLASSES: &[Class] = &[
    Class {
        name: "unrepresentable namespace",
        why: "`clazel-dom`'s `Namespace` has six variants: the element and the attribute in http://www.example.org/ns of the WPT harness cannot be built",
        applies: |e| {
            e.expect.iter().any(|id| id.ends_with("-div4"))
                || e.expect.iter().any(|id| id == "attr-presence-i1")
        },
    },
    Class {
        name: "pseudo-class outside clazel-selectors' subset",
        why: "`:target`, `:lang()`, `:enabled`, `:disabled`, `:checked` and `::slotted()` are not parsed by `clazel-selectors` (phase-5.md item 5.5's subset), so the selector is a SyntaxError",
        applies: |e| {
            [
                ":target",
                ":lang(",
                ":enabled",
                ":disabled",
                ":checked",
                "::slotted",
            ]
            .iter()
            .any(|p| e.selector.contains(p))
        },
    },
    Class {
        name: ":empty and white space",
        why: "Selectors 4 §15.2† lets `:empty` match an element holding only white space, which `clazel-selectors` follows; the WPT table expects the Selectors 3 reading (a white space text node makes it not empty)",
        applies: |e| e.selector.contains(":empty"),
    },
];

// ---------------------------------------------------------------------

fn ids(arena: &Arena, nodes: &[usize]) -> Vec<String> {
    nodes
        .iter()
        .map(|&n| id_of(arena, n).unwrap_or_default())
        .collect()
}

/// Run one `validSelectors` entry as `runValidSelectorTest` does, in the
/// context `root` of kind `kind`; `Err` says what differed.
fn run_valid(w: &World, root: usize, e: &Entry) -> Result<(), String> {
    let sel = u(&e.selector);
    let all = query_selector_all(&w.arena, root, &sel).map_err(|_| "SyntaxError".to_string())?;
    let found = ids(&w.arena, &all);
    if found != e.expect {
        return Err(format!("expected {:?}, found {:?}", e.expect, found));
    }
    for &n in &all {
        if attribute(&w.arena, n, "data-clone").is_some() {
            return Err("found a cloned element".into());
        }
    }
    let one = query_selector(&w.arena, root, &sel).map_err(|_| "SyntaxError".to_string())?;
    if one != all.first().copied() {
        return Err(format!(
            "querySelector found {:?}, not the first of {:?}",
            one.map(|n| id_of(&w.arena, n)),
            found
        ));
    }
    Ok(())
}

fn run_matches(w: &World, e: &Entry) -> Result<(), String> {
    let sel = u(&e.selector);
    for (list, want) in [(&e.expect, true), (&e.unexpected, false)] {
        for id in list {
            let Some(el) = find_id(&w.arena, w.document, id) else {
                return Err(format!("no element #{id} in the document"));
            };
            let got = matches(&w.arena, el, &sel).map_err(|_| "SyntaxError".to_string())?;
            if got != want {
                return Err(format!("#{id}: matches is {got}, want {want}"));
            }
        }
    }
    Ok(())
}

#[test]
fn wpt_selectors() {
    // The document, detached and fragment tests run before the clone is
    // appended to the body; the in-document element's after.
    let w = world(false);
    let wc = world(true);
    let valid = entries("validSelectors");
    let invalid = entries("invalidSelectors");
    assert!(valid.len() > 150, "read {} valid entries", valid.len());
    assert!(invalid.len() > 25, "read {} invalid entries", invalid.len());
    let step = if cfg!(miri) { 40 } else { 1 };

    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut total = 0usize;
    let mut failed = Vec::new();
    let mut by_class = vec![0usize; CLASSES.len()];
    let mut settle = |entry: &Entry, what: String, r: Result<(), String>| {
        total += 1;
        match r {
            Ok(()) => pass += 1,
            Err(why) => {
                let hit: Vec<usize> = CLASSES
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| (c.applies)(entry))
                    .map(|(i, _)| i)
                    .collect();
                if hit.is_empty() {
                    failed.push(format!("{what}: {:?}: {why}", entry.selector));
                } else {
                    xfail += 1;
                    for i in hit {
                        if let Some(n) = by_class.get_mut(i) {
                            *n = n.saturating_add(1);
                        }
                    }
                }
            }
        }
    };

    // Invalid selectors: SyntaxError from all four, in every context.
    for e in invalid.iter().step_by(step) {
        let sel = u(&e.selector);
        let mut r = Ok(());
        for root in [w.document, w.element, w.detached, w.fragment] {
            if query_selector(&w.arena, root, &sel) != Err(SyntaxError)
                || query_selector_all(&w.arena, root, &sel) != Err(SyntaxError)
            {
                r = Err(format!("not a SyntaxError (root {root})"));
            }
        }
        if matches(&w.arena, w.element, &sel) != Err(SyntaxError)
            || closest(&w.arena, w.element, &sel) != Err(SyntaxError)
        {
            r = Err("matches or closest: not a SyntaxError".into());
        }
        settle(e, format!("invalid [{}]", e.name), r);
    }

    // Valid selectors, as querySelector[All] in the four contexts.
    let contexts: [(&str, &World, usize); 4] = [
        ("document", &w, w.document),
        ("element", &wc, wc.element),
        ("detached", &w, w.detached),
        ("fragment", &w, w.fragment),
    ];
    for e in valid.iter().step_by(step) {
        if e.test_type & TEST_QSA != 0 {
            for (kind, cw, root) in contexts {
                if cfg!(miri) && (kind == "detached" || kind == "fragment") {
                    continue;
                }
                if e.exclude.iter().any(|x| x == kind || x == "html") {
                    continue;
                }
                settle(e, format!("{kind} [{}]", e.name), run_valid(cw, root, e));
            }
        }
        if e.test_type & TEST_MATCH != 0
            && !e.exclude.iter().any(|x| x == "document" || x == "html")
        {
            settle(e, format!("matches [{}]", e.name), run_matches(&w, e));
        }
    }

    // The special selectors of runSpecialSelectorTests (the script harness
    // stringifies null and undefined to these) and the tree order of "*".
    for (sel, tag) in [("null", "null"), ("undefined", "undefined")] {
        for (_, cw, root) in contexts {
            let all = query_selector_all(&cw.arena, root, &u(sel)).must();
            assert_eq!(all.len(), 1, "{sel}");
            let one = query_selector(&cw.arena, root, &u(sel)).must();
            assert_eq!(one, all.first().copied(), "{sel}");
            match cw.arena.kind(all.first().copied().must()) {
                ExecKind::Element { local_name, .. } => assert_eq!(text(local_name), tag),
                _ => unreachable!("an element"),
            }
        }
    }
    for (_, cw, root) in contexts {
        let all = query_selector_all(&cw.arena, root, &u("*")).must();
        let mut want = elements_of(&cw.arena, root);
        want.retain(|&n| n != root);
        assert_eq!(all, want, "`*` is every descendant element in tree order");
    }

    for f in &failed {
        println!("MISMATCH {f}\n");
    }
    assert!(
        failed.is_empty(),
        "{} unexplained differences",
        failed.len()
    );
    assert_eq!(pass.saturating_add(xfail), total);
    if cfg!(miri) {
        return;
    }
    println!("selectors: expected failures by class:");
    for (c, n) in CLASSES.iter().zip(by_class.iter()) {
        println!("  {}: {}: {n}", c.name, c.why);
        assert!(*n > 0, "class {:?} applies to nothing: remove it", c.name);
    }
    println!(
        "clazel-conformance: suite=\"WPT dom/nodes selectors.js (querySelector[All], matches)\" pass={pass} xfail={xfail} fail=0 total={total}"
    );
}
