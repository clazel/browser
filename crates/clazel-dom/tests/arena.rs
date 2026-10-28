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
    assert!(matches!(a.kind(0), ExecKind::Document { mode: DocumentMode::NoQuirks, .. }));

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
        ExecAttr { namespace: None, prefix: None, local_name: s("class"), value: s("x") },
    );
    assert!(matches!(a.kind(b), ExecKind::Element { attributes, .. } if attributes.len() == 1));
    a.set_mode(DocumentMode::Quirks);
    assert!(matches!(a.kind(0), ExecKind::Document { mode: DocumentMode::Quirks, .. }));
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
    let kids: Vec<usize> = (0..5).map(|i| create(&mut a, text(&i.to_string()))).collect();
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
    assert!(
        matches!(a.kind(t), ExecKind::Element { template_contents: Some(c), .. } if *c == f)
    );
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
    let mut parent = 0;
    for _ in 0..100_000 {
        let n = create(&mut a, element("div"));
        a.append(parent, n);
        parent = n;
    }
    assert!(a.is_inclusive_ancestor(0, parent));
    assert_eq!(a.len(), 100_001);
}
