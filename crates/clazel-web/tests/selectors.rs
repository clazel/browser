//! `querySelector`, `querySelectorAll`, `matches` and `closest` (DOM
//! §4.2.6†, §4.9†) on trees built by hand: each test names the rule it
//! covers.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
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

fn u(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// A tree under construction.
struct Tree {
    arena: Arena,
}

impl Tree {
    fn new() -> Tree {
        Tree {
            arena: Arena::new(Vec::new()),
        }
    }

    fn make(&mut self, kind: ExecKind) -> usize {
        match self.arena.create(kind) {
            Some(n) => n,
            None => unreachable!("node limit"),
        }
    }

    /// An HTML element with `attrs` (name, value pairs), appended to `parent`.
    fn el(&mut self, parent: usize, name: &str, attrs: &[(&str, &str)]) -> usize {
        let attributes = attrs
            .iter()
            .map(|(n, v)| ExecAttr {
                namespace: None,
                prefix: None,
                local_name: u(n),
                value: u(v),
            })
            .collect();
        let e = self.make(ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: u(name),
            attributes,
            template_contents: None,
            form_owner: None,
        });
        self.arena.append(parent, e);
        e
    }

    /// A detached element (no parent).
    fn loose(&mut self, name: &str, attrs: &[(&str, &str)]) -> usize {
        let doc = self.make(ExecKind::DocumentFragment { host: None });
        let e = self.el(doc, name, attrs);
        self.arena.remove(e);
        e
    }

    fn text(&mut self, parent: usize, data: &str) -> usize {
        let t = self.make(ExecKind::Text { data: u(data) });
        self.arena.append(parent, t);
        t
    }
}

/// The document of the tests:
///
/// ```text
/// #0 document
///   html#html
///     body#body
///       div#a.x
///         p#p1.x
///           span#s1
///         "text"
///         p#p2
///       div#b
///         p#p3.x
/// ```
struct Doc {
    t: Tree,
    document: usize,
    html: usize,
    body: usize,
    a: usize,
    p1: usize,
    s1: usize,
    p2: usize,
    b: usize,
    p3: usize,
}

fn doc() -> Doc {
    let mut t = Tree::new();
    let document = 0;
    let html = t.el(document, "html", &[("id", "html")]);
    let body = t.el(html, "body", &[("id", "body")]);
    let a = t.el(body, "div", &[("id", "a"), ("class", "x")]);
    let p1 = t.el(a, "p", &[("id", "p1"), ("class", "x")]);
    let s1 = t.el(p1, "span", &[("id", "s1")]);
    t.text(a, "text");
    let p2 = t.el(a, "p", &[("id", "p2")]);
    let b = t.el(body, "div", &[("id", "b")]);
    let p3 = t.el(b, "p", &[("id", "p3"), ("class", "x")]);
    Doc {
        t,
        document,
        html,
        body,
        a,
        p1,
        s1,
        p2,
        b,
        p3,
    }
}

fn all(d: &Doc, root: usize, sel: &str) -> Vec<usize> {
    query_selector_all(&d.t.arena, root, &u(sel)).must()
}

fn first(d: &Doc, root: usize, sel: &str) -> Option<usize> {
    query_selector(&d.t.arena, root, &u(sel)).must()
}

// DOM §4.2.6† querySelectorAll: "all the elements ... in tree order".
#[test]
fn query_selector_all_is_in_tree_order() {
    let d = doc();
    assert_eq!(all(&d, d.document, "p"), [d.p1, d.p2, d.p3]);
    assert_eq!(
        all(&d, d.document, "*"),
        [d.html, d.body, d.a, d.p1, d.s1, d.p2, d.b, d.p3]
    );
    assert_eq!(all(&d, d.document, ".x"), [d.a, d.p1, d.p3]);
}

// A selector list returns each element once, in tree order, not in the
// order of the list.
#[test]
fn selector_list_is_in_tree_order_without_duplicates() {
    let d = doc();
    assert_eq!(all(&d, d.document, "#p3, p, #p1"), [d.p1, d.p2, d.p3]);
}

// DOM §4.2.6†: "the descendants of this": never the context node itself.
#[test]
fn root_is_not_a_result() {
    let d = doc();
    assert_eq!(all(&d, d.a, "div"), []);
    assert_eq!(all(&d, d.a, "*"), [d.p1, d.s1, d.p2]);
    assert_eq!(first(&d, d.a, "#a"), None);
    assert_eq!(first(&d, d.p3, "*"), None);
}

// The first result of querySelectorAll is querySelector's.
#[test]
fn query_selector_is_the_first_result() {
    let d = doc();
    assert_eq!(first(&d, d.document, "p"), Some(d.p1));
    assert_eq!(first(&d, d.b, "p"), Some(d.p3));
    assert_eq!(first(&d, d.document, "table"), None);
}

// "match a selector against a tree": the whole tree is matched against, so a
// compound or a combinator may use nodes outside the context node.
#[test]
fn selectors_see_outside_the_context_node() {
    let d = doc();
    assert_eq!(all(&d, d.a, "#a p"), [d.p1, d.p2]);
    assert_eq!(all(&d, d.a, "body > div > p"), [d.p1, d.p2]);
    assert_eq!(all(&d, d.a, "#b p"), []);
    assert_eq!(all(&d, d.p1, "p + p"), []);
    assert_eq!(all(&d, d.a, "p + p"), [d.p2]);
    assert_eq!(all(&d, d.a, "p ~ p"), [d.p2]);
}

// A fragment, and a detached element, are trees of their own.
#[test]
fn detached_trees() {
    let mut t = Tree::new();
    let frag = t.make(ExecKind::DocumentFragment { host: None });
    let div = t.el(frag, "div", &[("id", "d")]);
    let p = t.el(div, "p", &[]);
    assert_eq!(query_selector_all(&t.arena, frag, &u("div p")).must(), [p]);
    assert_eq!(query_selector(&t.arena, frag, &u("div")).must(), Some(div));
    let loose = t.loose("section", &[]);
    let inner = t.el(loose, "b", &[]);
    assert_eq!(
        query_selector_all(&t.arena, loose, &u("section b")).must(),
        [inner]
    );
    assert_eq!(
        query_selector_all(&t.arena, loose, &u("section")).must(),
        []
    );
    // `:root` is the document element, so it matches nothing in a
    // detached tree (Selectors 4 §15.1†).
    assert_eq!(query_selector_all(&t.arena, loose, &u(":root")).must(), []);
}

// DOM §4.2.6† step 2: an invalid selector is a SyntaxError, from every method,
// also when nothing could match.
#[test]
fn invalid_selectors_are_syntax_errors() {
    let d = doc();
    for bad in ["", "[", "div,", ">*", "div:example", "..x", "#", "ns|div"] {
        let s = u(bad);
        assert_eq!(
            query_selector(&d.t.arena, d.document, &s),
            Err(SyntaxError),
            "{bad:?}"
        );
        assert_eq!(
            query_selector_all(&d.t.arena, d.document, &s),
            Err(SyntaxError),
            "{bad:?}"
        );
        assert_eq!(matches(&d.t.arena, d.p1, &s), Err(SyntaxError), "{bad:?}");
        assert_eq!(closest(&d.t.arena, d.p1, &s), Err(SyntaxError), "{bad:?}");
    }
    // Also on a node that is not in the arena, and on an empty tree.
    assert_eq!(query_selector(&d.t.arena, 9999, &u("[")), Err(SyntaxError));
}

// The parser's input limit (`MAX_PARSER_INPUT`, 2^29 code points) is a
// SyntaxError and not a panic; it is too large to build here, so a long
// selector below it is only checked to parse.
#[test]
fn long_selectors_parse() {
    let d = doc();
    let n = if cfg!(miri) { 1_000 } else { 100_000 };
    let long = vec![u32::from('a'); n];
    assert_eq!(
        query_selector_all(&d.t.arena, d.document, &long),
        Ok(vec![])
    );
}

// DOM §4.9† matches: "match a selector against an element ... this".
#[test]
fn matches_the_element() {
    let d = doc();
    let a = &d.t.arena;
    assert_eq!(matches(a, d.p1, &u("p")), Ok(true));
    assert_eq!(matches(a, d.p1, &u("div p")), Ok(true));
    assert_eq!(matches(a, d.p1, &u("div > span")), Ok(false));
    assert_eq!(matches(a, d.p2, &u("p:not(.x)")), Ok(true));
    assert_eq!(matches(a, d.p1, &u("p:not(.x)")), Ok(false));
    assert_eq!(matches(a, d.p2, &u("p:nth-child(2)")), Ok(true));
    assert_eq!(matches(a, d.p3, &u(":first-child")), Ok(true));
    assert_eq!(matches(a, d.html, &u(":root")), Ok(true));
    assert_eq!(matches(a, d.body, &u(":root")), Ok(false));
    assert_eq!(matches(a, d.p1, &u("#nope, .x")), Ok(true));
}

// `matches` on a node that is no element, or not in the arena, is false.
#[test]
fn matches_is_false_for_non_elements() {
    let d = doc();
    assert_eq!(matches(&d.t.arena, d.document, &u("*")), Ok(false));
    assert_eq!(matches(&d.t.arena, 9999, &u("*")), Ok(false));
    let text = d.t.arena.children(d.a).get(1).copied().must();
    assert_eq!(matches(&d.t.arena, text, &u("*")), Ok(false));
    assert_eq!(closest(&d.t.arena, 9999, &u("*")), Ok(None));
}

// DOM §4.9† closest: "inclusive ancestors that are elements, in reverse
// tree order": the nearest first, and the element itself counts.
#[test]
fn closest_is_the_nearest_inclusive_ancestor() {
    let d = doc();
    let a = &d.t.arena;
    assert_eq!(closest(a, d.s1, &u("span")), Ok(Some(d.s1)));
    assert_eq!(closest(a, d.s1, &u(".x")), Ok(Some(d.p1)));
    assert_eq!(closest(a, d.s1, &u("div")), Ok(Some(d.a)));
    assert_eq!(closest(a, d.p2, &u(".x")), Ok(Some(d.a)));
    assert_eq!(closest(a, d.s1, &u("div, p")), Ok(Some(d.p1)));
    assert_eq!(closest(a, d.p3, &u("#a")), Ok(None));
    assert_eq!(closest(a, d.s1, &u("body")), Ok(Some(d.body)));
    // The document is no element: it is never returned.
    assert_eq!(
        closest(
            a,
            d.s1,
            &u("*:not(html):not(body):not(div):not(p):not(span)")
        ),
        Ok(None)
    );
    assert_eq!(closest(a, d.b, &u("html > body > div")), Ok(Some(d.b)));
}

// Case: type selectors on an HTML element in an HTML document are ASCII
// case-insensitive (Selectors 4 §6.1†, HTML §4.16.2†), ids and classes are
// case-sensitive in a no-quirks document.
#[test]
fn case_rules() {
    let d = doc();
    assert_eq!(all(&d, d.document, "P").len(), 3);
    assert_eq!(all(&d, d.document, "#P1").len(), 0);
    assert_eq!(all(&d, d.document, ".X").len(), 0);
}

// Template contents are not descendants (DOM §4.4†: they are a separate
// fragment), so a query does not enter them.
#[test]
fn template_contents_are_not_entered() {
    let mut t = Tree::new();
    let tpl = t.el(0, "template", &[]);
    let contents = match t.arena.create_template_contents(tpl) {
        Some(c) => c,
        None => unreachable!("node limit"),
    };
    let inside = t.el(contents, "p", &[]);
    let outside = t.el(0, "p", &[]);
    assert_eq!(query_selector_all(&t.arena, 0, &u("p")).must(), [outside]);
    // Queried on the contents fragment, the `p` inside is found.
    assert_eq!(
        query_selector_all(&t.arena, contents, &u("p")).must(),
        [inside]
    );
}

// Iterative walk: a tree far deeper than the stack could recurse over.
#[test]
fn deep_trees_do_not_overflow() {
    let depth: usize = if cfg!(miri) { 100 } else { 3_000 };
    let mut t = Tree::new();
    let mut cur = 0;
    for _ in 0..depth {
        cur = t.el(cur, "div", &[]);
    }
    let leaf = t.el(cur, "p", &[("id", "leaf")]);
    assert_eq!(query_selector(&t.arena, 0, &u("p")).must(), Some(leaf));
    // A child combinator needs only the parent; a descendant combinator
    // walks the whole chain, which `clazel-selectors` does iteratively.
    assert_eq!(
        query_selector(&t.arena, 0, &u("div > p")).must(),
        Some(leaf)
    );
    assert_eq!(query_selector_all(&t.arena, 0, &u("#leaf")).must(), [leaf]);
    // The outermost div is the document element.
    assert_eq!(closest(&t.arena, leaf, &u(":root")), Ok(Some(1)));
}

// The context node's own attributes: a node outside the arena is no
// context: an empty result, not a panic.
#[test]
fn unknown_context_node_is_empty() {
    let d = doc();
    assert_eq!(query_selector(&d.t.arena, 9999, &u("*")), Ok(None));
    assert_eq!(query_selector_all(&d.t.arena, 9999, &u("*")), Ok(vec![]));
}

// Known gap, recorded so that a change in `clazel-selectors` shows here:
// `:scope` is not parsed, so it is a SyntaxError.
#[test]
fn scope_is_a_known_gap() {
    let d = doc();
    let r = query_selector_all(&d.t.arena, d.a, &u(":scope > p"));
    assert_eq!(r, Err(SyntaxError));
}
