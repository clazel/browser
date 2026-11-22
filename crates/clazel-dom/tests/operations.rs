//! Unit tests of Phase 7 item 7.13's operations on the executable arena:
//! "ensure pre-insertion validity", "pre-insert", "insert" of a fragment,
//! "replace", "replace all", "adopt", shallow "clone a node" and the
//! attribute changes.
//!
//! The proofs show each operation equals its spec function and keeps the
//! tree well formed; these tests check the compiled code on the cases the
//! DOM Standard's algorithms (and the WPT `dom/nodes` tests `Node-insertBefore`,
//! `Node-replaceChild`, `Node-cloneNode`, `ParentNode-replaceChildren` and
//! `Document-adoptNode`, from which the cases are taken from memory) are
//! about. They matter most for step 6 of validity (a document's children),
//! which no theorem covers.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DomError, Namespace};

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

fn doctype(name: &str) -> ExecKind {
    ExecKind::DocumentType {
        name: s(name),
        public_id: Vec::new(),
        system_id: Vec::new(),
    }
}

fn fragment() -> ExecKind {
    ExecKind::DocumentFragment { host: None }
}

fn create(a: &mut Arena, kind: ExecKind) -> usize {
    let id = a.create(kind);
    assert!(id.is_some(), "the node limit is far away");
    id.unwrap_or_default()
}

fn attr(name: &str, value: &str) -> ExecAttr {
    ExecAttr {
        namespace: None,
        prefix: None,
        local_name: s(name),
        value: s(value),
    }
}

fn is_hierarchy(e: &Option<DomError>) -> bool {
    matches!(e, Some(DomError::HierarchyRequest))
}

fn is_not_found(e: &Option<DomError>) -> bool {
    matches!(e, Some(DomError::NotFound))
}

/// The parent/children links agree, there are no duplicates, node 0 has no
/// parent, and every chain of parents ends.
fn check(a: &Arena) {
    for n in 0..a.len() {
        let kids = a.children(n);
        for c in kids {
            assert_eq!(a.parent(*c), Some(n), "child {c} of {n}");
            assert_eq!(
                kids.iter().filter(|x| *x == c).count(),
                1,
                "duplicate child {c} of {n}"
            );
        }
        if let Some(p) = a.parent(n) {
            assert!(a.children(p).contains(&n), "{n} is not in its parent {p}");
        }
        let mut cur = n;
        for _ in 0..=a.len() {
            match a.parent(cur) {
                Some(p) => cur = p,
                None => break,
            }
        }
        assert_eq!(a.parent(cur), None, "cycle above {n}");
    }
    assert_eq!(a.parent(0), None);
}

/// Three elements `a`, `b` and `c`, appended in order to `parent`.
fn kids3(a: &mut Arena, parent: usize) -> (usize, usize, usize) {
    let x = create(a, element("a"));
    let y = create(a, element("b"));
    let z = create(a, element("c"));
    a.append(parent, x);
    a.append(parent, y);
    a.append(parent, z);
    (x, y, z)
}

/// A new document.
fn new_doc() -> Arena {
    Arena::new(s("about:blank"))
}

#[test]
fn document_children_rules() {
    let mut a = new_doc();
    let t = create(&mut a, text("x"));
    // 5. A Text node cannot be a child of a document.
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(t, 0, None)));

    let html = create(&mut a, element("html"));
    let dt = create(&mut a, doctype("html"));
    let dt2 = create(&mut a, doctype("html"));
    let e2 = create(&mut a, element("other"));
    // A doctype after the element is invalid; before it, valid.
    assert!(a.pre_insert(html, 0, None).is_none());
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(dt, 0, None)));
    assert!(a.ensure_pre_insertion_validity(dt, 0, Some(html)).is_none());
    assert!(a.pre_insert(dt, 0, Some(html)).is_none());
    assert_eq!(a.children(0), &[dt, html]);
    // A second doctype, or a second element, is invalid.
    assert!(is_hierarchy(&a.pre_insert(dt2, 0, Some(dt))));
    assert!(is_hierarchy(&a.pre_insert(dt2, 0, Some(html))));
    assert!(is_hierarchy(&a.pre_insert(e2, 0, None)));
    // An element before a doctype is invalid.
    assert!(is_hierarchy(&a.pre_insert(e2, 0, Some(dt))));
    assert_eq!(a.children(0), &[dt, html]);
    // Moving the element within the document is fine: the check sees the
    // element where it is, as the standard does (a parent with an element
    // child, here `html` itself, is invalid).
    assert!(is_hierarchy(&a.pre_insert(html, 0, None)));
    // A doctype is not allowed in an element.
    assert!(is_hierarchy(
        &a.ensure_pre_insertion_validity(dt2, html, None)
    ));
    check(&a);
}

#[test]
fn document_children_rules_for_fragments() {
    let mut a = new_doc();
    let f = create(&mut a, fragment());
    let e1 = create(&mut a, element("a"));
    let e2 = create(&mut a, element("b"));
    let t = create(&mut a, text("x"));
    a.append(f, e1);
    a.append(f, e2);
    // More than one element child.
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(f, 0, None)));
    // A Text child.
    let g = create(&mut a, fragment());
    let e3 = create(&mut a, element("c"));
    a.append(g, e3);
    a.append(g, t);
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(g, 0, None)));
    // One element child is fine in an empty document, not in one with an
    // element.
    let h = create(&mut a, fragment());
    let e4 = create(&mut a, element("d"));
    a.append(h, e4);
    assert!(a.pre_insert(h, 0, None).is_none());
    assert_eq!(a.children(0), &[e4]);
    assert!(a.children(h).is_empty());
    let h2 = create(&mut a, fragment());
    let e5 = create(&mut a, element("e"));
    a.append(h2, e5);
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(h2, 0, None)));
    check(&a);
}

#[test]
fn hierarchy_checks() {
    let mut a = new_doc();
    let html = create(&mut a, element("html"));
    let body = create(&mut a, element("body"));
    let p = create(&mut a, element("p"));
    let t = create(&mut a, text("x"));
    a.append(0, html);
    a.append(html, body);
    a.append(body, p);
    a.append(p, t);
    // 1. A text node cannot have children.
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(p, t, None)));
    // 2. A node cannot go into itself or a descendant.
    assert!(is_hierarchy(
        &a.ensure_pre_insertion_validity(html, p, None)
    ));
    assert!(is_hierarchy(
        &a.ensure_pre_insertion_validity(body, body, None)
    ));
    // 3. The reference child must be a child of the parent.
    assert!(is_not_found(&a.ensure_pre_insertion_validity(
        p,
        body,
        Some(t)
    )));
    // 4. The document node cannot be inserted (into a parentless element).
    let loose = create(&mut a, element("div"));
    assert!(is_hierarchy(
        &a.ensure_pre_insertion_validity(0, loose, None)
    ));
    // An error changes nothing.
    let before: Vec<Vec<usize>> = (0..a.len()).map(|n| a.children(n).to_vec()).collect();
    assert!(is_hierarchy(&a.pre_insert(html, p, None)));
    assert!(is_not_found(&a.pre_insert(p, body, Some(t))));
    let after: Vec<Vec<usize>> = (0..a.len()).map(|n| a.children(n).to_vec()).collect();
    assert_eq!(before, after);
    check(&a);
}

#[test]
fn a_template_cannot_go_into_its_own_contents() {
    let mut a = new_doc();
    let tpl = create(&mut a, element("template"));
    let contents = a.create_template_contents(tpl);
    assert!(contents.is_some());
    let contents = contents.unwrap_or_default();
    // The template is a host-including inclusive ancestor of its contents'
    // children and of the contents themselves.
    let p = create(&mut a, element("p"));
    a.append(contents, p);
    assert!(is_hierarchy(&a.ensure_pre_insertion_validity(tpl, p, None)));
    assert!(is_hierarchy(
        &a.ensure_pre_insertion_validity(tpl, contents, None)
    ));
    // A fragment that is the contents of a template can itself be inserted,
    // and then moves the template's children out.
    let host = create(&mut a, element("div"));
    assert!(a.pre_insert(contents, host, None).is_none());
    assert_eq!(a.children(host), &[p]);
    assert!(a.children(contents).is_empty());
    assert_eq!(a.parent(contents), None);
    check(&a);
}

#[test]
fn pre_insert_places_children() {
    let mut a = new_doc();
    let div = create(&mut a, element("div"));
    let (k0, k1, k2) = kids3(&mut a, div);
    let x = create(&mut a, element("x"));
    assert!(a.pre_insert(x, div, Some(k1)).is_none());
    assert_eq!(a.children(div), &[k0, x, k1, k2]);
    assert_eq!(a.next_sibling(x), Some(k1));
    assert_eq!(a.next_sibling(k2), None);
    assert_eq!(a.next_sibling(0), None);
    // Before itself: the reference child is its next sibling, so it stays.
    assert!(a.pre_insert(x, div, Some(x)).is_none());
    assert_eq!(a.children(div), &[k0, x, k1, k2]);
    // Before itself, as the last child: it stays last.
    assert!(a.pre_insert(k2, div, Some(k2)).is_none());
    assert_eq!(a.children(div), &[k0, x, k1, k2]);
    // Moving the first child to the end.
    assert!(a.pre_insert(k0, div, None).is_none());
    assert_eq!(a.children(div), &[x, k1, k2, k0]);
    // Moving a node before a later sibling.
    assert!(a.pre_insert(x, div, Some(k0)).is_none());
    assert_eq!(a.children(div), &[k1, k2, x, k0]);
    check(&a);
}

#[test]
fn inserting_a_fragment_moves_its_children_in_order() {
    let mut a = new_doc();
    let div = create(&mut a, element("div"));
    let (k0, k1, k2) = kids3(&mut a, div);
    let f = create(&mut a, fragment());
    let x = create(&mut a, element("x"));
    let y = create(&mut a, text("y"));
    a.append(f, x);
    a.append(f, y);
    assert!(a.pre_insert(f, div, Some(k1)).is_none());
    assert_eq!(a.children(div), &[k0, x, y, k1, k2]);
    assert!(a.children(f).is_empty());
    assert_eq!(a.parent(f), None);
    assert_eq!(a.parent(x), Some(div));
    assert_eq!(a.parent(y), Some(div));
    // An empty fragment changes nothing.
    assert!(a.pre_insert(f, div, Some(k0)).is_none());
    assert_eq!(a.children(div), &[k0, x, y, k1, k2]);
    // At the end.
    let g = create(&mut a, fragment());
    let z = create(&mut a, element("z"));
    a.append(g, z);
    assert!(a.pre_insert(g, div, None).is_none());
    assert_eq!(a.children(div), &[k0, x, y, k1, k2, z]);
    // A fragment cannot go into one of its own children.
    let h = create(&mut a, fragment());
    let w = create(&mut a, element("w"));
    a.append(h, w);
    assert!(is_hierarchy(&a.pre_insert(h, w, None)));
    assert_eq!(a.children(h), &[w]);
    check(&a);
}

#[test]
fn replace_swaps_in_place() {
    let mut a = new_doc();
    let div = create(&mut a, element("div"));
    let (k0, k1, k2) = kids3(&mut a, div);
    let x = create(&mut a, element("x"));
    assert!(a.replace(k1, x, div).is_none());
    assert_eq!(a.children(div), &[k0, x, k2]);
    assert_eq!(a.parent(k1), None);
    // Replacing a child with itself changes nothing.
    assert!(a.replace(x, x, div).is_none());
    assert_eq!(a.children(div), &[k0, x, k2]);
    // With its next sibling: the next sibling takes its place.
    assert!(a.replace(k0, x, div).is_none());
    assert_eq!(a.children(div), &[x, k2]);
    assert_eq!(a.parent(k0), None);
    // With a node that comes before it.
    assert!(a.replace(k2, x, div).is_none());
    assert_eq!(a.children(div), &[x]);
    // A node that is not a child.
    let other = create(&mut a, element("o"));
    assert!(is_not_found(&a.replace(other, x, div)));
    // A fragment.
    let f = create(&mut a, fragment());
    let p = create(&mut a, element("p"));
    let q = create(&mut a, element("q"));
    a.append(f, p);
    a.append(f, q);
    assert!(a.replace(x, f, div).is_none());
    assert_eq!(a.children(div), &[p, q]);
    assert!(a.children(f).is_empty());
    assert_eq!(a.parent(x), None);
    // The parent cannot be put into itself.
    assert!(is_hierarchy(&a.replace(p, div, div)));
    check(&a);
}

#[test]
fn replace_in_a_document() {
    let mut a = new_doc();
    let dt = create(&mut a, doctype("html"));
    let html = create(&mut a, element("html"));
    a.append(0, dt);
    a.append(0, html);
    // An element for the element is fine; for the doctype it is not (an
    // element child that is not the child).
    let e = create(&mut a, element("other"));
    assert!(is_hierarchy(&a.replace(dt, e, 0)));
    assert!(a.replace(html, e, 0).is_none());
    assert_eq!(a.children(0), &[dt, e]);
    // A doctype for the doctype is fine; for the element it is not (the
    // doctype after... an element is preceding).
    let dt2 = create(&mut a, doctype("html"));
    assert!(is_hierarchy(&a.replace(e, dt2, 0)));
    assert!(a.replace(dt, dt2, 0).is_none());
    assert_eq!(a.children(0), &[dt2, e]);
    // A text node cannot replace anything in a document.
    let t = create(&mut a, text("x"));
    assert!(is_hierarchy(&a.replace(e, t, 0)));
    // An element cannot replace the doctype when a doctype follows...
    let e2 = create(&mut a, element("e2"));
    assert!(is_hierarchy(&a.replace(dt2, e2, 0)));
    check(&a);
}

#[test]
fn replace_all_replaces_children() {
    let mut a = new_doc();
    let div = create(&mut a, element("div"));
    let (k0, k1, k2) = kids3(&mut a, div);
    let t = create(&mut a, text("hello"));
    a.replace_all(Some(t), div);
    assert_eq!(a.children(div), &[t]);
    for n in [k0, k1, k2] {
        assert_eq!(a.parent(n), None);
    }
    // A child of the parent itself.
    a.replace_all(Some(t), div);
    assert_eq!(a.children(div), &[t]);
    // No node.
    a.replace_all(None, div);
    assert!(a.children(div).is_empty());
    assert_eq!(a.parent(t), None);
    // A fragment.
    let f = create(&mut a, fragment());
    let x = create(&mut a, element("x"));
    let y = create(&mut a, element("y"));
    a.append(f, x);
    a.append(f, y);
    a.append(div, k0);
    a.replace_all(Some(f), div);
    assert_eq!(a.children(div), &[x, y]);
    assert!(a.children(f).is_empty());
    assert_eq!(a.parent(k0), None);
    // A node from elsewhere in the tree moves.
    let other = create(&mut a, element("other"));
    let z = create(&mut a, element("z"));
    a.append(other, z);
    a.replace_all(Some(z), div);
    assert_eq!(a.children(div), &[z]);
    assert!(a.children(other).is_empty());
    check(&a);
}

#[test]
fn adopt_detaches() {
    let mut a = new_doc();
    let div = create(&mut a, element("div"));
    let p = create(&mut a, element("p"));
    a.append(div, p);
    a.adopt(p);
    assert_eq!(a.parent(p), None);
    assert!(a.children(div).is_empty());
    // A node without a parent is left alone.
    a.adopt(p);
    assert_eq!(a.parent(p), None);
    check(&a);
}

fn attrs(a: &Arena, n: usize) -> Vec<(String, String)> {
    match a.kind(n) {
        ExecKind::Element { attributes, .. } => attributes
            .iter()
            .map(|x| {
                (
                    x.local_name
                        .iter()
                        .filter_map(|c| char::from_u32(*c))
                        .collect(),
                    x.value.iter().filter_map(|c| char::from_u32(*c)).collect(),
                )
            })
            .collect(),
        _ => Vec::new(),
    }
}

#[test]
fn attribute_changes() {
    let mut a = new_doc();
    let e = create(&mut a, element("e"));
    a.append_attribute(e, attr("a", "1"));
    a.append_attribute(e, attr("b", "2"));
    a.append_attribute(e, attr("c", "3"));
    a.change_attribute(e, 1, s("two"));
    assert_eq!(
        attrs(&a, e),
        [
            ("a".into(), "1".into()),
            ("b".into(), "two".into()),
            ("c".into(), "3".into())
        ]
    );
    a.replace_attribute(e, 0, attr("z", "26"));
    assert_eq!(
        attrs(&a, e),
        [
            ("z".into(), "26".into()),
            ("b".into(), "two".into()),
            ("c".into(), "3".into())
        ]
    );
    a.remove_attribute(e, 1);
    assert_eq!(
        attrs(&a, e),
        [("z".into(), "26".into()), ("c".into(), "3".into())]
    );
    a.remove_attribute(e, 1);
    a.remove_attribute(e, 0);
    assert!(attrs(&a, e).is_empty());
    check(&a);
}

#[test]
fn shallow_clone() {
    let mut a = new_doc();
    let e = create(
        &mut a,
        ExecKind::Element {
            namespace: Some(Namespace::Svg),
            prefix: Some(s("p")),
            local_name: s("circle"),
            attributes: vec![attr("r", "5"), attr("cx", "1")],
            template_contents: None,
            form_owner: None,
        },
    );
    let kid = create(&mut a, text("kid"));
    a.append(0, e);
    a.append(e, kid);
    let n = a.len();
    let copy = a.clone_node(e);
    assert_eq!(copy, Some(n));
    let c = copy.unwrap_or_default();
    // A shallow copy: same fields, no parent, no children.
    assert_eq!(a.parent(c), None);
    assert!(a.children(c).is_empty());
    assert_eq!(attrs(&a, c), attrs(&a, e));
    match a.kind(c) {
        ExecKind::Element {
            namespace,
            prefix,
            local_name,
            template_contents,
            form_owner,
            ..
        } => {
            assert!(matches!(namespace, Some(Namespace::Svg)));
            assert_eq!(prefix.as_deref(), Some(s("p").as_slice()));
            assert_eq!(*local_name, s("circle"));
            assert!(template_contents.is_none());
            assert!(form_owner.is_none());
        }
        other => assert!(matches!(other, ExecKind::Element { .. }), "an element"),
    }
    assert_eq!(a.len(), n + 1);
    // The original is untouched, and the copy is independent of it.
    assert_eq!(a.children(e), &[kid]);
    a.change_attribute(c, 0, s("9"));
    assert_eq!(attrs(&a, e).first().map(|x| x.1.as_str()), Some("5"));
    // Other kinds.
    let t = a.clone_node(kid).unwrap_or_default();
    assert!(matches!(a.kind(t), ExecKind::Text { data } if *data == s("kid")));
    let dt = create(&mut a, doctype("html"));
    let d2 = a.clone_node(dt).unwrap_or_default();
    assert!(matches!(a.kind(d2), ExecKind::DocumentType { name, .. } if *name == s("html")));
    let f = create(&mut a, fragment());
    let f2 = a.clone_node(f).unwrap_or_default();
    assert!(matches!(
        a.kind(f2),
        ExecKind::DocumentFragment { host: None }
    ));
    check(&a);
}

#[test]
fn cloning_a_template_gives_the_copy_contents_of_its_own() {
    let mut a = new_doc();
    let tpl = create(&mut a, element("template"));
    let contents = a.create_template_contents(tpl).unwrap_or_default();
    let p = create(&mut a, element("p"));
    a.append(contents, p);
    let n = a.len();
    let copy = a.clone_node(tpl).unwrap_or_default();
    assert_eq!(copy, n);
    assert_eq!(a.len(), n + 2);
    match a.kind(copy) {
        ExecKind::Element {
            template_contents: Some(c),
            ..
        } => {
            assert_eq!(*c, n + 1);
            // Shallow: the copy's contents are empty, and the original's
            // are as they were.
            assert!(a.children(*c).is_empty());
            assert!(
                matches!(a.kind(*c), ExecKind::DocumentFragment { host: Some(h) } if *h == copy)
            );
        }
        other => assert!(
            matches!(
                other,
                ExecKind::Element {
                    template_contents: Some(_),
                    ..
                }
            ),
            "a template"
        ),
    }
    assert_eq!(a.children(contents), &[p]);
    check(&a);
}

/// `copy` is a fresh copy of the host-including subtree at `src`: the same
/// shape, kinds and data, template contents included, and every node of it
/// is a new node (id >= `old_len`).
fn same_shape(a: &Arena, src: usize, copy: usize, old_len: usize) {
    assert!(copy >= old_len, "{copy} is not a new node");
    match (a.kind(src), a.kind(copy)) {
        (ExecKind::Text { data: x }, ExecKind::Text { data: y }) => assert_eq!(x, y),
        (ExecKind::Comment { data: x }, ExecKind::Comment { data: y }) => assert_eq!(x, y),
        (
            ExecKind::Element {
                local_name: x,
                template_contents: tx,
                ..
            },
            ExecKind::Element {
                local_name: y,
                template_contents: ty,
                form_owner,
                ..
            },
        ) => {
            assert_eq!(x, y);
            assert!(form_owner.is_none());
            assert_eq!(tx.is_some(), ty.is_some());
            if let (Some(sx), Some(sy)) = (tx, ty) {
                same_shape(a, *sx, *sy, old_len);
            }
            assert_eq!(attrs(a, src), attrs(a, copy));
        }
        (x, y) => assert!(
            std::mem::discriminant(x) == std::mem::discriminant(y),
            "kinds differ"
        ),
    }
    let (ks, kc) = (a.children(src), a.children(copy));
    assert_eq!(ks.len(), kc.len());
    for (s, c) in ks.iter().zip(kc) {
        assert_eq!(a.parent(*c), Some(copy));
        same_shape(a, *s, *c, old_len);
    }
}

#[test]
fn deep_clone_copies_the_whole_subtree() {
    let mut a = new_doc();
    let root = create(&mut a, element("div"));
    a.append(0, root);
    let p = create(&mut a, element("p"));
    let t = create(&mut a, text("hello"));
    let c = create(&mut a, ExecKind::Comment { data: s("note") });
    let q = create(&mut a, element("q"));
    let t2 = create(&mut a, text("deep"));
    a.append(root, p);
    a.append(p, t);
    a.append(root, c);
    a.append(root, q);
    a.append(q, t2);
    let before: Vec<Vec<usize>> = (0..a.len()).map(|n| a.children(n).to_vec()).collect();
    let n = a.len();
    let copy = a.clone_deep(root);
    assert_eq!(copy, Some(n));
    let copy = copy.unwrap_or_default();
    assert_eq!(a.len(), n + 6);
    assert_eq!(a.parent(copy), None);
    same_shape(&a, root, copy, n);
    // The source is untouched.
    for (i, kids) in before.iter().enumerate() {
        assert_eq!(a.children(i), kids.as_slice());
    }
    check(&a);
    // A leaf's deep clone is its shallow clone.
    let leaf = a.clone_deep(t2).unwrap_or_default();
    assert!(matches!(a.kind(leaf), ExecKind::Text { data } if *data == s("deep")));
    assert!(a.children(leaf).is_empty());
    check(&a);
}

#[test]
fn deep_clone_clones_template_contents_and_nests() {
    let mut a = new_doc();
    let outer = create(&mut a, element("template"));
    let oc = a.create_template_contents(outer).unwrap_or_default();
    let inner = create(&mut a, element("template"));
    let ic = a.create_template_contents(inner).unwrap_or_default();
    let span = create(&mut a, element("span"));
    let tx = create(&mut a, text("x"));
    a.append(oc, inner);
    a.append(ic, span);
    a.append(span, tx);
    // A template with ordinary children too.
    let kid = create(&mut a, element("b"));
    a.append(outer, kid);
    let n = a.len();
    let copy = a.clone_deep(outer).unwrap_or_default();
    assert_eq!(a.len(), n + 7);
    same_shape(&a, outer, copy, n);
    // The copy's contents is hosted by the copy; the source's is as it was.
    match a.kind(copy) {
        ExecKind::Element {
            template_contents: Some(c),
            ..
        } => {
            assert!(
                matches!(a.kind(*c), ExecKind::DocumentFragment { host: Some(h) } if *h == copy)
            );
            assert_ne!(*c, oc);
        }
        other => assert!(
            matches!(other, ExecKind::Element { .. }),
            "a template element"
        ),
    }
    assert_eq!(a.children(oc), &[inner]);
    check(&a);
    // Cloning a template's contents directly gives a fragment with no host.
    let f = a.clone_deep(oc).unwrap_or_default();
    assert!(matches!(
        a.kind(f),
        ExecKind::DocumentFragment { host: None }
    ));
    assert_eq!(a.children(f).len(), 1);
    same_shape(&a, oc, f, n);
    check(&a);
}

/// A deep clone that does not fit leaves the arena exactly as it was. The
/// arena is filled to the node limit, which Miri would take minutes to do.
#[test]
#[cfg_attr(miri, ignore = "creating four million nodes takes minutes under Miri")]
fn deep_clone_that_does_not_fit_changes_nothing() {
    let mut a = new_doc();
    let root = create(&mut a, element("div"));
    a.append(0, root);
    for _ in 0..4 {
        let k = create(&mut a, element("i"));
        a.append(root, k);
    }
    // Leave room for the copy of the root and two of its four children.
    while a.len() < clazel_dom::exec::MAX_NODES - 3 {
        assert!(a.create(text("filler")).is_some());
    }
    let n = a.len();
    let kids = a.children(root).to_vec();
    assert_eq!(a.clone_deep(root), None);
    assert_eq!(a.len(), n);
    assert_eq!(a.children(root), kids.as_slice());
    assert_eq!(a.parent(root), Some(0));
    for c in &kids {
        assert!(a.children(*c).is_empty());
        assert_eq!(a.parent(*c), Some(root));
    }
    // One that does fit still works.
    let first = kids.first().copied().unwrap_or_default();
    assert!(a.clone_deep(first).is_some());
    assert_eq!(a.len(), n + 1);
}
