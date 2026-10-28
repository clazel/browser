//! Frame lemmas: [`parser_inv`] split by the part of the parser it reads,
//! so that a helper that changes one part (the stack, the list, the
//! document) proves only that part.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An element record that may be on the stack of open elements.
pub open spec fn elem_ok(doc: Document, e: Elem) -> bool {
    &&& elem_in_doc(doc, e)
    &&& elem_tagged(e)
    &&& (is_html(e, Tag::Template) ==> has_template_contents(doc, e.id))
}

/// Every record of the stack is [`elem_ok`].
pub open spec fn open_ok(doc: Document, o: Seq<Elem>) -> bool {
    forall|i: int| 0 <= i < o.len() ==> elem_ok(doc, #[trigger] o[i])
}

/// An entry that may be in the list of active formatting elements.
pub open spec fn fmt_ok(doc: Document, x: Fmt) -> bool {
    match x {
        Fmt::Marker => true,
        Fmt::Entry { elem, token } => elem_in_doc(doc, elem) && elem_tagged(elem) && tok_tagged(token) && token.tag
            != Tag::Template,
    }
}

/// Every entry of the list is [`fmt_ok`].
pub open spec fn fmts_ok(doc: Document, f: Seq<Fmt>) -> bool {
    forall|i: int| 0 <= i < f.len() ==> fmt_ok(doc, #[trigger] f[i])
}

/// `termination::modes_ok` without its `formatting_ok` part (which
/// [`fmts_ok`] gives).
pub open spec fn modes_core(p: Parser) -> bool {
    &&& forall|i: int| 0 <= i < p.template_modes.len() ==> crate::termination::template_mode_ok(#[trigger] p.template_modes[i])
    &&& p.mode == Mode::InTableText ==> p.original_mode != Mode::Text && p.original_mode != Mode::InTableText
    &&& p.mode == Mode::Text ==> p.original_mode != Mode::Text && p.original_mode != Mode::InTableText
    &&& crate::termination::template_count(p) <= p.template_modes.len()
    &&& p.mode == Mode::InTemplate ==> p.template_modes.len() > 0
    &&& (p.mode == Mode::Text || p.mode == Mode::InTableText) && p.original_mode == Mode::InTemplate ==> p.template_modes.len() > 0
}

/// The rest of [`parser_inv`]: the document, the pointers, the context, the
/// redirection map and the modes.
pub open spec fn rest_ok(p: Parser) -> bool {
    &&& modes_core(p)
    &&& dom::wf(p.doc)
    &&& opt_valid(p.doc, p.head)
    &&& opt_valid(p.doc, p.form)
    &&& match p.context {
        None => true,
        Some(c) => elem_in_doc(p.doc, c) && elem_tagged(c),
    }
    &&& match p.redirect {
        None => true,
        Some((r, f)) => dom::valid(p.doc, r) && dom::valid(p.doc, f) && p.doc.nodes[f as int].kind is DocumentFragment,
    }
    &&& forall|n: NodeId|
        dom::valid(p.doc, n) && #[trigger] node_is_template(p.doc, n) && p.doc.nodes[n as int].children.len() > 0
            ==> has_template_contents(p.doc, n)
}

/// [`parser_inv`] is the conjunction of its parts.
pub proof fn lemma_inv_iff(p: Parser)
    ensures
        parser_inv(p) == (open_ok(p.doc, p.open) && fmts_ok(p.doc, p.formatting) && rest_ok(p)),
{
    if parser_inv(p) {
        assert forall|i: int| 0 <= i < p.formatting.len() implies fmt_ok(p.doc, #[trigger] p.formatting[i]) by {
            if p.formatting[i] is Entry {
            }
        }
    }
    if fmts_ok(p.doc, p.formatting) {
        assert forall|i: int| 0 <= i < p.formatting.len() && #[trigger] p.formatting[i] is Entry implies p.formatting[i]->Entry_token.tag
            != Tag::Template by {
            assert(fmt_ok(p.doc, p.formatting[i]));
        }
    }
    if open_ok(p.doc, p.open) && fmts_ok(p.doc, p.formatting) && rest_ok(p) {
        assert forall|i: int| 0 <= i < p.open.len() implies elem_in_doc(p.doc, #[trigger] p.open[i]) by {
            assert(elem_ok(p.doc, p.open[i]));
        }
        assert forall|i: int| 0 <= i < p.open.len() implies elem_tagged(#[trigger] p.open[i]) by {
            assert(elem_ok(p.doc, p.open[i]));
        }
        assert forall|i: int| 0 <= i < p.open.len() && is_html(#[trigger] p.open[i], Tag::Template) implies has_template_contents(
            p.doc,
            p.open[i].id,
        ) by {
            assert(elem_ok(p.doc, p.open[i]));
        }
        assert forall|i: int| 0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry implies elem_in_doc(
            p.doc,
            p.formatting[i]->Entry_elem,
        ) by {
            assert(fmt_ok(p.doc, p.formatting[i]));
        }
        assert forall|i: int| 0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry implies elem_tagged(
            p.formatting[i]->Entry_elem,
        ) && tok_tagged(p.formatting[i]->Entry_token) by {
            assert(fmt_ok(p.doc, p.formatting[i]));
        }
    }
}

/// A stack whose records all come from a stack that was [`open_ok`].
pub proof fn lemma_open_sub(doc: Document, o: Seq<Elem>, o2: Seq<Elem>)
    requires
        open_ok(doc, o),
        forall|j: int| 0 <= j < o2.len() ==> o.contains(#[trigger] o2[j]),
    ensures
        open_ok(doc, o2),
{
    assert forall|j: int| 0 <= j < o2.len() implies elem_ok(doc, #[trigger] o2[j]) by {
        assert(o.contains(o2[j]));
        let k = choose|k: int| 0 <= k < o.len() && o[k] == o2[j];
        assert(elem_ok(doc, o[k]));
    }
}

/// Popping keeps [`open_ok`].
pub proof fn lemma_open_drop_last(doc: Document, o: Seq<Elem>)
    requires
        open_ok(doc, o),
        o.len() > 0,
    ensures
        open_ok(doc, o.drop_last()),
{
    assert forall|j: int| 0 <= j < o.drop_last().len() implies elem_ok(doc, #[trigger] o.drop_last()[j]) by {
        assert(o.drop_last()[j] == o[j]);
    }
}

/// Removing an entry keeps [`open_ok`].
pub proof fn lemma_open_remove(doc: Document, o: Seq<Elem>, i: int)
    requires
        open_ok(doc, o),
        0 <= i < o.len(),
    ensures
        open_ok(doc, o.remove(i)),
{
    assert forall|j: int| 0 <= j < o.remove(i).len() implies elem_ok(doc, #[trigger] o.remove(i)[j]) by {
        if j < i {
            assert(o.remove(i)[j] == o[j]);
        } else {
            assert(o.remove(i)[j] == o[j + 1]);
        }
    }
}

/// Pushing an [`elem_ok`] record keeps [`open_ok`].
pub proof fn lemma_open_push(doc: Document, o: Seq<Elem>, e: Elem)
    requires
        open_ok(doc, o),
        elem_ok(doc, e),
    ensures
        open_ok(doc, o.push(e)),
{
    assert forall|j: int| 0 <= j < o.push(e).len() implies elem_ok(doc, #[trigger] o.push(e)[j]) by {
        if j < o.len() {
            assert(o.push(e)[j] == o[j]);
        }
    }
}

/// Removing an entry keeps [`fmts_ok`].
pub proof fn lemma_fmts_remove(doc: Document, f: Seq<Fmt>, i: int)
    requires
        fmts_ok(doc, f),
        0 <= i < f.len(),
    ensures
        fmts_ok(doc, f.remove(i)),
{
    assert forall|j: int| 0 <= j < f.remove(i).len() implies fmt_ok(doc, #[trigger] f.remove(i)[j]) by {
        if j < i {
            assert(f.remove(i)[j] == f[j]);
        } else {
            assert(f.remove(i)[j] == f[j + 1]);
        }
    }
}

/// Dropping the last entry keeps [`fmts_ok`].
pub proof fn lemma_fmts_drop_last(doc: Document, f: Seq<Fmt>)
    requires
        fmts_ok(doc, f),
        f.len() > 0,
    ensures
        fmts_ok(doc, f.drop_last()),
{
    assert forall|j: int| 0 <= j < f.drop_last().len() implies fmt_ok(doc, #[trigger] f.drop_last()[j]) by {
        assert(f.drop_last()[j] == f[j]);
    }
}

/// Pushing an [`fmt_ok`] entry keeps [`fmts_ok`].
pub proof fn lemma_fmts_push(doc: Document, f: Seq<Fmt>, x: Fmt)
    requires
        fmts_ok(doc, f),
        fmt_ok(doc, x),
    ensures
        fmts_ok(doc, f.push(x)),
{
    assert forall|j: int| 0 <= j < f.push(x).len() implies fmt_ok(doc, #[trigger] f.push(x)[j]) by {
        if j < f.len() {
            assert(f.push(x)[j] == f[j]);
        }
    }
}

/// Updating an entry with an [`fmt_ok`] one keeps [`fmts_ok`].
pub proof fn lemma_fmts_update(doc: Document, f: Seq<Fmt>, i: int, x: Fmt)
    requires
        fmts_ok(doc, f),
        fmt_ok(doc, x),
        0 <= i < f.len(),
    ensures
        fmts_ok(doc, f.update(i, x)),
{
    assert forall|j: int| 0 <= j < f.update(i, x).len() implies fmt_ok(doc, #[trigger] f.update(i, x)[j]) by {
        if j != i {
            assert(f.update(i, x)[j] == f[j]);
        }
    }
}

// ---------------------------------------------------------------------
// Changes of the document

/// What a node keeps when the document changes: an element stays an
/// element with the same namespace and local name, and keeps its template
/// contents; a fragment stays a fragment; no other node becomes an
/// element.
pub open spec fn kind_kept(a: NodeKind, b: NodeKind) -> bool {
    &&& a is Element ==> {
        &&& b is Element
        &&& b->Element_namespace == a->Element_namespace
        &&& b->Element_local_name == a->Element_local_name
        &&& (a->Element_template_contents is Some ==> b->Element_template_contents is Some)
    }
    &&& a is DocumentFragment ==> b is DocumentFragment
    &&& b is Element ==> a is Element
}

/// `d1` is a well-formed document that keeps every node of `d0`
/// ([`kind_kept`]), and every template element with a child in `d1` has
/// template contents or had a child in `d0`.
pub open spec fn doc_extends(d0: Document, d1: Document) -> bool {
    &&& dom::wf(d1)
    &&& d0.nodes.len() <= d1.nodes.len()
    &&& forall|i: int| 0 <= i < d0.nodes.len() ==> kind_kept(d0.nodes[i].kind, #[trigger] d1.nodes[i].kind)
    &&& forall|n: NodeId|
        dom::valid(d1, n) && #[trigger] node_is_template(d1, n) && d1.nodes[n as int].children.len() > 0 ==> has_template_contents(
            d1,
            n,
        ) || (n < d0.nodes.len() && d0.nodes[n as int].children.len() > 0)
}

/// [`elem_ok`] survives [`doc_extends`].
pub proof fn lemma_elem_ok_extends(d0: Document, d1: Document, e: Elem)
    requires
        elem_ok(d0, e),
        doc_extends(d0, d1),
    ensures
        elem_ok(d1, e),
{
    assert(kind_kept(d0.nodes[e.id as int].kind, d1.nodes[e.id as int].kind));
}

/// The document of a parser satisfying [`parser_inv`] can be replaced by
/// one that [`doc_extends`] it.
pub proof fn lemma_inv_doc(p: Parser, d: Document)
    requires
        parser_inv(p),
        doc_extends(p.doc, d),
    ensures
        parser_inv(Parser { doc: d, ..p }),
{
    let q = Parser { doc: d, ..p };
    lemma_inv_iff(p);
    lemma_inv_iff(q);
    assert forall|i: int| 0 <= i < q.open.len() implies elem_ok(d, #[trigger] q.open[i]) by {
        assert(elem_ok(p.doc, p.open[i]));
        lemma_elem_ok_extends(p.doc, d, p.open[i]);
    }
    assert forall|i: int| 0 <= i < q.formatting.len() implies fmt_ok(d, #[trigger] q.formatting[i]) by {
        assert(fmt_ok(p.doc, p.formatting[i]));
        if let Fmt::Entry { elem, token } = p.formatting[i] {
            assert(kind_kept(p.doc.nodes[elem.id as int].kind, d.nodes[elem.id as int].kind));
        }
    }
    if let Some(c) = p.context {
        assert(kind_kept(p.doc.nodes[c.id as int].kind, d.nodes[c.id as int].kind));
    }
    if let Some((r, f)) = p.redirect {
        assert(kind_kept(p.doc.nodes[f as int].kind, d.nodes[f as int].kind));
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(
        d,
        n,
    ) by {
        if !has_template_contents(d, n) {
            assert(n < p.doc.nodes.len() && p.doc.nodes[n as int].children.len() > 0);
            assert(kind_kept(p.doc.nodes[n as int].kind, d.nodes[n as int].kind));
            assert(node_is_template(p.doc, n));
            assert(has_template_contents(p.doc, n));
        }
    }
    assert(rest_ok(q));
}

/// Creating a node extends the document.
pub proof fn lemma_create_extends(doc: Document, k: NodeKind)
    requires
        dom::wf(doc),
        dom::creatable(doc, k),
        dom::can_create(doc, 1),
        !(k is Element) || k->Element_template_contents is None,
    ensures
        doc_extends(doc, dom::create_node(doc, k).0),
{
    clazel_dom::lemmas::theorem_create_node_wf(doc, k);
    let d = dom::create_node(doc, k).0;
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        assert(d.nodes[i] == doc.nodes[i]);
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(d, n)
        || (n < doc.nodes.len() && doc.nodes[n as int].children.len() > 0) by {
        if n < doc.nodes.len() {
            assert(d.nodes[n as int] == doc.nodes[n as int]);
        }
    }
}

/// Creating a template's contents extends the document.
pub proof fn lemma_create_template_contents_extends(doc: Document, t: NodeId)
    requires
        clazel_dom::contract::create_template_contents_requires(doc, t),
        dom::can_create(doc, 1),
    ensures
        doc_extends(doc, dom::create_template_contents(doc, t).0),
{
    clazel_dom::lemmas::theorem_create_template_contents_wf(doc, t);
    let d = dom::create_template_contents(doc, t).0;
    let d1 = dom::create_node(doc, NodeKind::DocumentFragment { host: Some(t) }).0;
    assert(d1.nodes.len() == doc.nodes.len() + 1);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        assert(d1.nodes[i] == doc.nodes[i]);
        if i != t {
            assert(d.nodes[i] == d1.nodes[i]);
        }
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(d, n)
        || (n < doc.nodes.len() && doc.nodes[n as int].children.len() > 0) by {
        if n < doc.nodes.len() && n != t {
            assert(d.nodes[n as int] == d1.nodes[n as int]);
            assert(d1.nodes[n as int] == doc.nodes[n as int]);
        } else if n == t {
        } else {
            assert(d.nodes[n as int] == d1.nodes[n as int]);
        }
    }
}

/// Inserting a node extends the document, provided its new parent is not a
/// template element without template contents.
pub proof fn lemma_insert_extends(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        dom::insert_requires(doc, node, parent, child),
        node_is_template(doc, parent) ==> has_template_contents(doc, parent),
    ensures
        doc_extends(doc, dom::insert(doc, node, parent, child)),
{
    clazel_dom::lemmas::theorem_insert_wf(doc, node, parent, child);
    let d = dom::insert(doc, node, parent, child);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        assert(d.nodes[i].kind == doc.nodes[i].kind);
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(d, n)
        || (n < doc.nodes.len() && doc.nodes[n as int].children.len() > 0) by {
        assert(d.nodes[n as int].kind == doc.nodes[n as int].kind);
        if n != parent && !has_template_contents(d, n) {
            lemma_insert_children_frame(doc, node, parent, child, n);
        }
    }
}

/// A node other than the parent keeps no more children than it had, when a
/// node is inserted (it may lose `node`, which moves).
pub proof fn lemma_insert_children_frame(doc: Document, node: NodeId, parent: NodeId, child: Option<NodeId>, n: NodeId)
    requires
        dom::insert_requires(doc, node, parent, child),
        dom::valid(doc, n),
        n != parent,
    ensures
        dom::insert(doc, node, parent, child).nodes[n as int].children.len() <= doc.nodes[n as int].children.len(),
{
    let d1 = dom::adopt(doc, node);
    if doc.nodes[node as int].parent is Some {
        clazel_dom::lemmas::theorem_remove_keeps_record(doc, node);
        clazel_dom::lemmas::theorem_remove_wf(doc, node);
        let par = doc.nodes[node as int].parent->Some_0;
        if n == par {
            assert(d1.nodes[n as int].children.len() == doc.nodes[n as int].children.len() - 1);
        } else {
            assert(d1.nodes[n as int].children == doc.nodes[n as int].children);
        }
    }
    if n == node {
        assert(dom::insert(doc, node, parent, child).nodes[n as int].children == d1.nodes[n as int].children);
    }
}

/// Removing a node extends the document.
pub proof fn lemma_remove_extends(doc: Document, node: NodeId)
    requires
        clazel_dom::contract::remove_requires(doc, node),
    ensures
        doc_extends(doc, dom::remove(doc, node)),
{
    clazel_dom::lemmas::theorem_remove_wf(doc, node);
    clazel_dom::lemmas::theorem_remove_keeps_record(doc, node);
    let d = dom::remove(doc, node);
    let par = doc.nodes[node as int].parent->Some_0;
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        assert(d.nodes[i].kind == doc.nodes[i].kind);
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(d, n)
        || (n < doc.nodes.len() && doc.nodes[n as int].children.len() > 0) by {
        if n != par {
            assert(d.nodes[n as int].children == doc.nodes[n as int].children);
        }
    }
}

/// Appending data to a `Text` node extends the document.
pub proof fn lemma_append_data_extends(doc: Document, n: NodeId, data: Seq<u32>)
    requires
        clazel_dom::contract::append_data_requires(doc, n),
    ensures
        doc_extends(doc, dom::append_data(doc, n, data)),
{
    clazel_dom::lemmas::theorem_append_data_wf(doc, n, data);
    let d = dom::append_data(doc, n, data);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        if i != n {
            assert(d.nodes[i] == doc.nodes[i]);
        }
    }
    assert forall|m: NodeId|
        dom::valid(d, m) && #[trigger] node_is_template(d, m) && d.nodes[m as int].children.len() > 0 implies has_template_contents(d, m)
        || (m < doc.nodes.len() && doc.nodes[m as int].children.len() > 0) by {
        if m != n {
            assert(d.nodes[m as int] == doc.nodes[m as int]);
        }
    }
}

/// [`doc_extends`] is transitive.
pub proof fn lemma_doc_extends_trans(d0: Document, d1: Document, d2: Document)
    requires
        doc_extends(d0, d1),
        doc_extends(d1, d2),
    ensures
        doc_extends(d0, d2),
{
    assert forall|i: int| 0 <= i < d0.nodes.len() implies kind_kept(d0.nodes[i].kind, #[trigger] d2.nodes[i].kind) by {
        assert(kind_kept(d0.nodes[i].kind, d1.nodes[i].kind));
        assert(kind_kept(d1.nodes[i].kind, d2.nodes[i].kind));
    }
    assert forall|n: NodeId|
        dom::valid(d2, n) && #[trigger] node_is_template(d2, n) && d2.nodes[n as int].children.len() > 0 implies has_template_contents(
        d2,
        n,
    ) || (n < d0.nodes.len() && d0.nodes[n as int].children.len() > 0) by {
        if !has_template_contents(d2, n) {
            assert(n < d1.nodes.len() && d1.nodes[n as int].children.len() > 0);
            assert(kind_kept(d1.nodes[n as int].kind, d2.nodes[n as int].kind));
            assert(node_is_template(d1, n));
            if has_template_contents(d1, n) {
                assert(has_template_contents(d2, n));
            }
        }
    }
}

} // verus!
