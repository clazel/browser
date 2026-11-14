//! Unit tests of the executable arena: a small tree built with every
//! operation, and checked through the readers.
//!
//! The proofs already show each operation equals its spec function; these
//! tests check the compiled code runs as the proofs describe (and that the
//! API is usable without Verus).

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};

fn s(text: &str) -> Vec<u32> {
    text.chars().map(u32::from).collect()
}

fn element(name: &str) -> ExecKind {
    ExecKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: s(name),
        attributes: Vec::new(),
        template_contents: None,
        form_owner: None,
    }
}

fn text(data: &str) -> ExecKind {
    ExecKind::Text { data: s(data) }
}

fn create(a: &mut Arena, kind: ExecKind) -> usize {
    let id = a.create(kind);
    assert!(id.is_some(), "the node limit is far away");
    id.unwrap_or_default()
}

fn local_name(a: &Arena, n: usize) -> Vec<u32> {
    match a.kind(n) {
        ExecKind::Element { local_name, .. } => local_name.clone(),
        _ => Vec::new(),
    }
}

/// `<html><head></head><body><p>a</p><b>c</b></body></html>`, built the
/// way the tree builder would, then edited.
#[test]
fn builds_and_edits_a_small_tree() {
    let mut a = Arena::new(s("about:blank"));
    assert_eq!(a.len(), 1);
    assert!(matches!(
        a.kind(0),
        ExecKind::Document {
            mode: DocumentMode::NoQuirks,
            ..
        }
    ));

    let html = create(&mut a, element("html"));
    let head = create(&mut a, element("head"));
    let body = create(&mut a, element("body"));
    let p = create(&mut a, element("p"));
    let t = create(&mut a, text("a"));
    a.append(0, html);
    a.append(html, head);
    a.append(html, body);
    a.append(body, p);
    a.append(p, t);
    a.append_data(t, &s("bc"));
    assert_eq!(a.len(), 6);
    assert_eq!(a.children(0), &[html]);
    assert_eq!(a.children(html), &[head, body]);
    assert_eq!(a.parent(body), Some(html));
    assert_eq!(a.parent(0), None);
    assert_eq!(a.last_child(html), Some(body));
    assert_eq!(a.previous_sibling(body), Some(head));
    assert_eq!(a.previous_sibling(head), None);
    assert!(a.has_child(p));
    assert!(!a.has_child(head));
    assert!(matches!(a.kind(t), ExecKind::Text { data } if *data == s("abc")));
    assert!(a.is_inclusive_ancestor(0, t));
    assert!(a.is_inclusive_ancestor(t, t));
    assert!(!a.is_inclusive_ancestor(head, t));

    // insert_before: a <b> before the <p>.
    let b = create(&mut a, element("b"));
    a.insert_before(body, b, p);
    assert_eq!(a.children(body), &[b, p]);
    assert_eq!(a.previous_sibling(p), Some(b));

    // Moving a node (append adopts it first): <b> to the end.
    a.append(body, b);
    assert_eq!(a.children(body), &[p, b]);
    assert_eq!(a.parent(b), Some(body));

    // remove detaches and keeps the record.
    a.remove(p);
    assert_eq!(a.children(body), &[b]);
    assert_eq!(a.parent(p), None);
    assert_eq!(a.children(p), &[t]);
    assert_eq!(local_name(&a, p), s("p"));
    assert!(!a.is_inclusive_ancestor(0, t));
    assert_eq!(a.len(), 7);

    // ... and the removed node may be inserted again.
    a.insert_before(body, p, b);
    assert_eq!(a.children(body), &[p, b]);

    // Attributes and the document's mode.
    a.append_attribute(
        b,
        ExecAttr {
            namespace: None,
            prefix: None,
            local_name: s("class"),
            value: s("x"),
        },
    );
    assert!(matches!(a.kind(b), ExecKind::Element { attributes, .. } if attributes.len() == 1));
    a.set_mode(DocumentMode::Quirks);
    assert!(matches!(
        a.kind(0),
        ExecKind::Document {
            mode: DocumentMode::Quirks,
            ..
        }
    ));
    assert_eq!(a.wrapper(b), None);
}

/// The adoption agency's "move all children": order kept, parents updated.
#[test]
fn reparent_children_moves_all_in_order() {
    let mut a = Arena::new(s(""));
    let from = create(&mut a, element("div"));
    let to = create(&mut a, element("span"));
    a.append(0, from);
    let kept = create(&mut a, text("0"));
    a.append(to, kept);
    let kids: Vec<usize> = (0..5)
        .map(|i| create(&mut a, text(&i.to_string())))
        .collect();
    for &k in &kids {
        a.append(from, k);
    }
    a.reparent_children(from, to);
    assert!(a.children(from).is_empty());
    let mut expected = vec![kept];
    expected.extend_from_slice(&kids);
    assert_eq!(a.children(to), expected.as_slice());
    for &k in &kids {
        assert_eq!(a.parent(k), Some(to));
    }
}

/// A template's contents: a fragment hosted by the template, not a child.
#[test]
fn template_contents() {
    let mut a = Arena::new(s(""));
    let t = create(&mut a, element("template"));
    a.append(0, t);
    let f = a.create_template_contents(t);
    assert!(f.is_some(), "the node limit is far away");
    let f = f.unwrap_or_default();
    assert!(matches!(a.kind(f), ExecKind::DocumentFragment { host: Some(h) } if *h == t));
    assert!(matches!(a.kind(t), ExecKind::Element { template_contents: Some(c), .. } if *c == f));
    assert!(a.children(t).is_empty());
    assert_eq!(a.parent(f), None);
    let x = create(&mut a, text("x"));
    a.append(f, x);
    assert_eq!(a.children(f), &[x]);
}

/// A deep chain is handled without recursion.
#[test]
fn deep_chain() {
    let mut a = Arena::new(s(""));
    // Miri interprets every step; a shorter chain keeps its run short.
    let depth: usize = if cfg!(miri) { 300 } else { 100_000 };
    let mut parent = 0;
    for _ in 0..depth {
        let n = create(&mut a, element("div"));
        a.append(parent, n);
        parent = n;
    }
    assert!(a.is_inclusive_ancestor(0, parent));
    assert_eq!(a.len(), depth.saturating_add(1));
}

// ---------------------------------------------------------------------------
// Attribute order, and fields no other test observes.

/// DOM §4.9: an element's attribute list is ordered, and "append an
/// attribute" (§4.9, step 1: "Append attribute to element's attribute
/// list") adds at the end. So attributes read back in the order appended,
/// after any the element was created with, whatever their names or
/// namespaces sort as.
#[test]
fn attributes_keep_the_order_they_were_appended_in() {
    let mut a = Arena::new(s(""));
    let e = create(
        &mut a,
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: s("div"),
            attributes: vec![attr(None, None, "m", "0")],
            template_contents: None,
            form_owner: None,
        },
    );
    // Names chosen so that neither sorted nor reversed order is the order
    // appended: z, a, xlink:href, a (again), b.
    let appended = [
        ("z", None, None, "1"),
        ("a", None, None, "2"),
        ("href", Some(Namespace::XLink), Some("xlink"), "3"),
        ("a", None, None, "4"),
        ("b", None, None, "5"),
    ];
    for (name, ns, prefix, value) in appended {
        a.append_attribute(e, attr(ns, prefix, name, value));
    }
    let got = attrs_of(&a, e);
    let want: Vec<String> = ["m=0", "z=1", "a=2", "xlink:href=3", "a=4", "b=5"]
        .iter()
        .map(|t| (*t).to_owned())
        .collect();
    assert_eq!(got, want);
}

fn attr(namespace: Option<Namespace>, prefix: Option<&str>, name: &str, value: &str) -> ExecAttr {
    ExecAttr {
        namespace,
        prefix: prefix.map(s),
        local_name: s(name),
        value: s(value),
    }
}

fn text_of(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn ns_name(n: &Option<Namespace>) -> &'static str {
    match n {
        None => "none",
        Some(Namespace::Html) => "html",
        Some(Namespace::MathMl) => "mathml",
        Some(Namespace::Svg) => "svg",
        Some(Namespace::XLink) => "xlink",
        Some(Namespace::Xml) => "xml",
        Some(Namespace::Xmlns) => "xmlns",
    }
}

/// `[prefix:]name=value` of each attribute, in list order (the prefix only
/// as the attribute stores it).
fn attrs_of(a: &Arena, n: usize) -> Vec<String> {
    match a.kind(n) {
        ExecKind::Element { attributes, .. } => attributes
            .iter()
            .map(|t| {
                let p = t
                    .prefix
                    .as_ref()
                    .map_or_else(String::new, |p| format!("{}:", text_of(p)));
                format!("{p}{}={}", text_of(&t.local_name), text_of(&t.value))
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// Every field of an element's kind, in a comparable form.
#[derive(Debug, PartialEq)]
struct ElementFields {
    namespace: &'static str,
    prefix: Option<String>,
    local_name: String,
    attrs: Vec<(&'static str, Option<String>, String, String)>,
    template_contents: Option<usize>,
    form_owner: Option<usize>,
    parent: Option<usize>,
    children: Vec<usize>,
}

fn element_fields(a: &Arena, n: usize) -> ElementFields {
    let ExecKind::Element {
        namespace,
        prefix,
        local_name,
        attributes,
        template_contents,
        form_owner,
    } = a.kind(n)
    else {
        // Not an element: a value no test expects, so the comparison fails.
        return ElementFields {
            namespace: "not an element",
            prefix: None,
            local_name: String::new(),
            attrs: Vec::new(),
            template_contents: None,
            form_owner: None,
            parent: None,
            children: Vec::new(),
        };
    };
    ElementFields {
        namespace: ns_name(namespace),
        prefix: prefix.as_ref().map(|p| text_of(p)),
        local_name: text_of(local_name),
        attrs: attributes
            .iter()
            .map(|t| {
                (
                    ns_name(&t.namespace),
                    t.prefix.as_ref().map(|p| text_of(p)),
                    text_of(&t.local_name),
                    text_of(&t.value),
                )
            })
            .collect(),
        template_contents: *template_contents,
        form_owner: *form_owner,
        parent: a.parent(n),
        children: a.children(n).to_vec(),
    }
}

/// An element with every optional field set: a namespace other than HTML,
/// a prefix, two attributes (one with a namespace and a prefix) and a form
/// owner. Returns it and the form (node 1, a `form` element).
fn rich_element(a: &mut Arena, namespace: Namespace, name: &str) -> (usize, usize) {
    let form = create(a, element("form"));
    let e = create(
        a,
        ExecKind::Element {
            namespace: Some(namespace),
            prefix: Some(s("pfx")),
            local_name: s(name),
            attributes: vec![
                attr(None, None, "k", "v"),
                attr(Some(Namespace::XLink), Some("xlink"), "href", "u"),
            ],
            template_contents: None,
            form_owner: Some(form),
        },
    );
    (e, form)
}

/// "append an attribute" changes the attribute list and nothing else of the
/// element, nor of any other node.
#[test]
fn append_attribute_leaves_every_other_field() {
    let mut a = Arena::new(s("u"));
    let (e, form) = rich_element(&mut a, Namespace::Svg, "g");
    let kid = create(&mut a, text("k"));
    a.append(0, e);
    a.append(e, kid);
    let before = element_fields(&a, e);
    let form_before = element_fields(&a, form);
    a.append_attribute(e, attr(Some(Namespace::Xml), Some("xml"), "lang", "en"));
    let after = element_fields(&a, e);
    let mut want = before;
    want.attrs
        .push(("xml", Some("xml".to_owned()), "lang".to_owned(), "en".to_owned()));
    assert_eq!(after, want);
    assert_eq!(after.prefix.as_deref(), Some("pfx"));
    assert_eq!(after.form_owner, Some(form));
    assert_eq!(element_fields(&a, form), form_before);
}

/// HTML §4.12.3 "template contents": creating them sets the element's
/// template contents and nothing else of it.
#[test]
fn create_template_contents_leaves_every_other_field() {
    let mut a = Arena::new(s("u"));
    let (t, form) = rich_element(&mut a, Namespace::Html, "template");
    let kid = create(&mut a, text("k"));
    a.append(0, t);
    a.append(t, kid);
    let before = element_fields(&a, t);
    assert_eq!(before.template_contents, None);
    let f = a.create_template_contents(t);
    assert!(f.is_some(), "the node limit is far away");
    let f = f.unwrap_or_default();
    let mut want = before;
    want.template_contents = Some(f);
    assert_eq!(element_fields(&a, t), want);
    assert_eq!(a.children(t), &[kid]);
    assert_eq!(a.parent(t), Some(0));
    assert_eq!(element_fields(&a, form).form_owner, None);
}

/// The document's fields: mode, URL and base URL (`Arena::new` makes the base
/// URL the URL, DOM §4.5 / the spec's `new_document`; the arena has no way
/// to set it apart).
fn document_fields(a: &Arena) -> (&'static str, String, String) {
    match a.kind(0) {
        ExecKind::Document { mode, url, base_url } => (
            match mode {
                DocumentMode::NoQuirks => "no-quirks",
                DocumentMode::Quirks => "quirks",
                DocumentMode::LimitedQuirks => "limited-quirks",
            },
            text_of(url),
            text_of(base_url),
        ),
        _ => ("not a document", String::new(), String::new()),
    }
}

/// Setting the mode changes only the mode: the URLs, the children and the
/// other nodes stay.
#[test]
fn set_mode_leaves_every_other_field() {
    let mut a = Arena::new(s("https://example.test/p"));
    let (e, _form) = rich_element(&mut a, Namespace::MathMl, "mi");
    a.append(0, e);
    let el_before = element_fields(&a, e);
    for (mode, name) in [
        (DocumentMode::Quirks, "quirks"),
        (DocumentMode::LimitedQuirks, "limited-quirks"),
        (DocumentMode::NoQuirks, "no-quirks"),
    ] {
        a.set_mode(mode);
        let (m, url, base) = document_fields(&a);
        assert_eq!(m, name);
        assert_eq!(url, "https://example.test/p");
        assert_eq!(base, "https://example.test/p");
        assert_eq!(a.children(0), &[e]);
        assert_eq!(a.parent(0), None);
        assert_eq!(element_fields(&a, e), el_before);
    }
}

/// Moving an element (append to another parent, insert before, move-all-
/// children, remove and insert again) changes only its parent and the
/// parents' children: its own kind, with every optional field, is kept.
#[test]
fn moving_an_element_keeps_its_fields() {
    let mut a = Arena::new(s(""));
    let (e, form) = rich_element(&mut a, Namespace::Svg, "g");
    let p1 = create(&mut a, element("div"));
    let p2 = create(&mut a, element("section"));
    let anchor = create(&mut a, text("anchor"));
    a.append(0, p1);
    a.append(0, p2);
    a.append(p2, anchor);
    a.append(p1, e);
    let mut want = element_fields(&a, e);
    let check = |a: &Arena, parent: usize, want: &ElementFields| {
        let w = ElementFields {
            namespace: want.namespace,
            prefix: want.prefix.clone(),
            local_name: want.local_name.clone(),
            attrs: want.attrs.clone(),
            template_contents: want.template_contents,
            form_owner: want.form_owner,
            parent: Some(parent),
            children: want.children.clone(),
        };
        assert_eq!(element_fields(a, e), w);
    };
    // To another parent, before a child.
    a.insert_before(p2, e, anchor);
    check(&a, p2, &want);
    assert_eq!(a.children(p2), &[e, anchor]);
    // Move-all-children, p2 to p1.
    a.reparent_children(p2, p1);
    check(&a, p1, &want);
    // Remove and insert again.
    a.remove(e);
    want.parent = None;
    assert_eq!(element_fields(&a, e), want);
    a.append(p2, e);
    check(&a, p2, &want);
    assert_eq!(element_fields(&a, form).form_owner, None);
}
