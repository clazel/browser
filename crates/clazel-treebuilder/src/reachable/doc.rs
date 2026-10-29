//! The document facts of a running reachable parser that the rules keep
//! between and within rule applications ([`dinv`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`dinv_of`] of the parser's document, stack, head element pointer and
/// redirection map.
pub open spec fn dinv(p: Parser) -> bool {
    dinv_of(p.doc, p.open, p.head, p.redirect)
}

/// The document is well formed; every record on the stack is an element
/// of it with its namespace and name, tagged by its name, and a `template`
/// record has template contents (`exec::frame::open_ok`); the head element
/// pointer names an HTML `head` element; the redirection map's target is a
/// fragment; and every `template` element with a child has template
/// contents.
#[verifier::opaque]
pub open spec fn dinv_of(doc: Document, open: Seq<Elem>, head: Option<NodeId>, redirect: Option<(NodeId, NodeId)>) -> bool {
    &&& dom::wf(doc)
    &&& crate::exec::frame::open_ok(doc, open)
    &&& match head {
        Some(h) => elem_in_doc(doc, head_elem(h)),
        None => true,
    }
    &&& match redirect {
        None => true,
        Some((r, f)) => dom::valid(doc, f) && doc.nodes[f as int].kind is DocumentFragment,
    }
    &&& forall|n: NodeId|
        dom::valid(doc, n) && #[trigger] node_is_template(doc, n) && doc.nodes[n as int].children.len() > 0
            ==> has_template_contents(doc, n)
}

/// Every HTML element of the document but the context element `ctx` (the
/// fragment case's, whose attributes are the caller's) has attributes with
/// no namespace and no prefix
/// (`independent::equivalence_body::attrs_plain`): the parser creates HTML
/// elements only for tokens, whose attributes are plain, and appends only
/// a token's attributes to an element.
pub open spec fn html_plain(doc: Document, ctx: Option<Elem>) -> bool {
    forall|i: int|
        0 <= i < doc.nodes.len() && (ctx is None || i != ctx->Some_0.id) && (#[trigger] doc.nodes[i]).kind is Element
            && doc.nodes[i].kind->Element_namespace == Some(Namespace::Html)
            ==> crate::independent::equivalence_body::attrs_plain(doc.nodes[i].kind->Element_attributes)
}

/// Node `n` may receive a child: it is a node, and no `template` element
/// without template contents.
pub open spec fn pok(doc: Document, n: NodeId) -> bool {
    dom::valid(doc, n) && (node_is_template(doc, n) ==> has_template_contents(doc, n))
}

/// What [`dinv_of`] says.
pub proof fn lemma_dinv(p: Parser)
    requires
        dinv(p),
    ensures
        dom::wf(p.doc),
        crate::exec::frame::open_ok(p.doc, p.open),
        match p.head {
            Some(h) => elem_in_doc(p.doc, head_elem(h)),
            None => true,
        },
        match p.redirect {
            None => true,
            Some((r, f)) => dom::valid(p.doc, f) && p.doc.nodes[f as int].kind is DocumentFragment,
        },
        forall|n: NodeId|
            dom::valid(p.doc, n) && #[trigger] node_is_template(p.doc, n) && p.doc.nodes[n as int].children.len() > 0
                ==> has_template_contents(p.doc, n),
{
    reveal(dinv_of);
}

/// [`dinv`] gives `invariant::templates_wf`.
pub proof fn lemma_dinv_templates_wf(p: Parser)
    requires
        dinv(p),
    ensures
        templates_wf(p),
{
    lemma_dinv(p);
    assert forall|i: int| 0 <= i < p.open.len() && is_html(#[trigger] p.open[i], Tag::Template) implies has_template_contents(
        p.doc,
        p.open[i].id,
    ) by {
        assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
    }
}

/// What [`dinv`] says of one record of the stack.
pub proof fn lemma_dinv_at(p: Parser, i: int)
    requires
        dinv(p),
        0 <= i < p.open.len(),
    ensures
        dom::wf(p.doc),
        crate::exec::frame::elem_ok(p.doc, p.open[i]),
        pok(p.doc, p.open[i].id),
{
    lemma_dinv(p);
    assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
}

/// [`dinv_of`] from its parts.
pub proof fn lemma_dinv_intro(p: Parser)
    requires
        dom::wf(p.doc),
        crate::exec::frame::open_ok(p.doc, p.open),
        match p.head {
            Some(h) => elem_in_doc(p.doc, head_elem(h)),
            None => true,
        },
        match p.redirect {
            None => true,
            Some((r, f)) => dom::valid(p.doc, f) && p.doc.nodes[f as int].kind is DocumentFragment,
        },
        forall|n: NodeId|
            dom::valid(p.doc, n) && #[trigger] node_is_template(p.doc, n) && p.doc.nodes[n as int].children.len() > 0
                ==> has_template_contents(p.doc, n),
    ensures
        dinv(p),
{
    reveal(dinv_of);
}

/// A document that `exec::frame::doc_extends` the parser's keeps
/// [`dinv`].
pub proof fn lemma_dinv_doc(p: Parser, d: Document)
    requires
        dinv(p),
        crate::exec::frame::doc_extends(p.doc, d),
    ensures
        dinv(Parser { doc: d, ..p }),
{
    lemma_dinv(p);
    let q = Parser { doc: d, ..p };
    assert forall|i: int| 0 <= i < q.open.len() implies crate::exec::frame::elem_ok(d, #[trigger] q.open[i]) by {
        assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
        crate::exec::frame::lemma_elem_ok_extends(p.doc, d, p.open[i]);
    }
    if let Some(h) = p.head {
        assert(crate::exec::frame::kind_kept(p.doc.nodes[h as int].kind, d.nodes[h as int].kind));
    }
    if let Some((r, f)) = p.redirect {
        assert(crate::exec::frame::kind_kept(p.doc.nodes[f as int].kind, d.nodes[f as int].kind));
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(
        d,
        n,
    ) by {
        if !has_template_contents(d, n) {
            assert(n < p.doc.nodes.len() && p.doc.nodes[n as int].children.len() > 0);
            assert(crate::exec::frame::kind_kept(p.doc.nodes[n as int].kind, d.nodes[n as int].kind));
            assert(node_is_template(p.doc, n));
        }
    }
    lemma_dinv_intro(q);
}

/// A new stack of records that are `exec::frame::elem_ok` keeps [`dinv`].
pub proof fn lemma_dinv_open(p: Parser, o: Seq<Elem>)
    requires
        dinv(p),
        crate::exec::frame::open_ok(p.doc, o),
    ensures
        dinv(Parser { open: o, ..p }),
{
    lemma_dinv(p);
    lemma_dinv_intro(Parser { open: o, ..p });
}

/// A stack whose records all come from the parser's keeps [`dinv`].
pub proof fn lemma_dinv_sub(p: Parser, o: Seq<Elem>)
    requires
        dinv(p),
        forall|j: int| 0 <= j < o.len() ==> p.open.contains(#[trigger] o[j]),
    ensures
        dinv(Parser { open: o, ..p }),
{
    lemma_dinv(p);
    crate::exec::frame::lemma_open_sub(p.doc, p.open, o);
    lemma_dinv_open(p, o);
}

/// A stack whose records come from the parser's or are `e`, a record that
/// is `exec::frame::elem_ok`, keeps [`dinv`].
pub proof fn lemma_dinv_with(p: Parser, o: Seq<Elem>, e: Elem)
    requires
        dinv(p),
        crate::exec::frame::elem_ok(p.doc, e),
        forall|j: int| 0 <= j < o.len() ==> #[trigger] o[j] == e || p.open.contains(o[j]),
    ensures
        dinv(Parser { open: o, ..p }),
{
    lemma_dinv(p);
    assert forall|j: int| 0 <= j < o.len() implies crate::exec::frame::elem_ok(p.doc, #[trigger] o[j]) by {
        if o[j] != e {
            let k = choose|k: int| 0 <= k < p.open.len() && p.open[k] == o[j];
            assert(crate::exec::frame::elem_ok(p.doc, p.open[k]));
        }
    }
    lemma_dinv_open(p, o);
}

/// A template's contents may receive a child (it is a fragment).
pub proof fn lemma_contents_pok(doc: Document, n: NodeId)
    requires
        dom::wf(doc),
        has_template_contents(doc, n),
    ensures
        pok(doc, template_contents(doc, n)),
        dom::valid(doc, template_contents(doc, n)),
{
    crate::exec::insert::lemma_wf_contents(doc, n);
}

/// Setting the document's mode extends a well-formed document.
pub proof fn lemma_set_mode_extends(doc: Document, mode: DocumentMode)
    requires
        dom::wf(doc),
    ensures
        crate::exec::frame::doc_extends(doc, dom::set_mode(doc, mode)),
{
    clazel_dom::lemmas::theorem_set_mode_wf(doc, mode);
    crate::exec::insert::lemma_wf_nonempty(doc);
    let d = dom::set_mode(doc, mode);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies crate::exec::frame::kind_kept(
        doc.nodes[i].kind,
        #[trigger] d.nodes[i].kind,
    ) by {
        if i != 0 {
            assert(d.nodes[i] == doc.nodes[i]);
        }
    }
    assert forall|m: NodeId|
        dom::valid(d, m) && #[trigger] node_is_template(d, m) && d.nodes[m as int].children.len() > 0 implies has_template_contents(
        d,
        m,
    ) || (m < doc.nodes.len() && doc.nodes[m as int].children.len() > 0) by {
        if m != 0 {
            assert(d.nodes[m as int] == doc.nodes[m as int]);
        }
    }
}

/// [`pok`] survives `exec::frame::doc_extends`.
pub proof fn lemma_pok_extends(d0: Document, d1: Document, n: NodeId)
    requires
        pok(d0, n),
        crate::exec::frame::doc_extends(d0, d1),
    ensures
        pok(d1, n),
{
    assert(crate::exec::frame::kind_kept(d0.nodes[n as int].kind, d1.nodes[n as int].kind));
}

/// A record that is `exec::frame::elem_ok` names a node that may receive
/// a child.
pub proof fn lemma_elem_pok(doc: Document, e: Elem)
    requires
        crate::exec::frame::elem_ok(doc, e),
    ensures
        pok(doc, e.id),
{
}

/// [`dom_insert`] into a parent that may receive a child extends a
/// well-formed document.
pub proof fn lemma_dom_insert_extends(p: Parser, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        dom::wf(p.doc),
        pok(p.doc, parent),
    ensures
        crate::exec::frame::doc_extends(p.doc, dom_insert(p, node, parent, child).doc),
        dom_insert(p, node, parent, child) == (Parser { doc: dom_insert(p, node, parent, child).doc, ..p }),
        dom_insert(p, node, parent, child).doc.nodes.len() == p.doc.nodes.len(),
{
    crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
    let d1 = dom::adopt(p.doc, node);
    assert(d1.nodes.len() == p.doc.nodes.len());
    if !p.stopped && insert_valid(p.doc, node, parent, child) {
        crate::exec::frame::lemma_insert_extends(p.doc, node, parent, child);
    }
}

/// Creating a node of a kind the arena accepts extends a well-formed
/// document.
pub proof fn lemma_create_doc_extends(p: Parser, k: NodeKind)
    requires
        dom::wf(p.doc),
        dom::creatable(p.doc, k),
    ensures
        crate::exec::frame::doc_extends(p.doc, create(p, k).0.doc),
        !create(p, k).0.stopped ==> create(p, k).1 as int == p.doc.nodes.len() && create(p, k).0.doc.nodes[create(
            p,
            k,
        ).1 as int].kind == k,
        !create(p, k).0.stopped ==> create(p, k).0 == (Parser { doc: create(p, k).0.doc, ..p }),
        create(p, k).0.doc.nodes.len() >= p.doc.nodes.len(),
        p.stopped ==> create(p, k).0 == p,
{
    crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
    if !p.stopped && dom::can_create(p.doc, 1) {
        crate::exec::frame::lemma_create_extends(p.doc, k);
    }
}

/// "Set the Document to" a mode extends a well-formed document.
pub proof fn lemma_set_document_mode_extends(p: Parser, mode: DocumentMode)
    requires
        dom::wf(p.doc),
    ensures
        crate::exec::frame::doc_extends(p.doc, set_document_mode(p, mode).doc),
        set_document_mode(p, mode) == (Parser { doc: set_document_mode(p, mode).doc, ..p }),
{
    crate::exec::modes::in_body_start_lemmas::lemma_doc_extends_refl(p.doc);
    if !p.stopped {
        lemma_set_mode_extends(p.doc, mode);
    }
}

/// The Document node may receive a child.
pub proof fn lemma_document_pok(doc: Document)
    requires
        dom::wf(doc),
    ensures
        pok(doc, 0),
        pok(doc, document_location().parent),
{
    crate::exec::insert::lemma_wf_nonempty(doc);
}

/// The stack is rooted at an HTML `html` element.
pub open spec fn rooted(p: Parser) -> bool {
    p.open.len() > 0 && is_html(p.open[0], Tag::Html)
}

/// §13.2.6.1 "appropriate place for inserting a node" on a rooted stack,
/// with an override target that is a record of the document, gives a
/// parent that may receive a child.
pub proof fn lemma_place_pok(p: Parser, ov: Option<Elem>)
    requires
        dinv(p),
        rooted(p),
        match ov {
            Some(e) => crate::exec::frame::elem_ok(p.doc, e),
            None => true,
        },
    ensures
        pok(p.doc, appropriate_place(p, ov).parent),
{
    lemma_dinv(p);
    let target = match ov {
        Some(e) => e,
        None => current_node(p),
    };
    assert(crate::exec::frame::elem_ok(p.doc, target)) by {
        if ov is None {
            assert(crate::exec::frame::elem_ok(p.doc, p.open[p.open.len() - 1]));
        }
    }
    if p.foster && is_table_like(target) {
        let f = |e: Elem| is_html(e, Tag::Template) || is_html(e, Tag::Table);
        let i = last_index_where(p.open, p.open.len() as int, f);
        crate::exec::stack::lemma_last_index_where(p.open, p.open.len() as int, f);
        if i < 0 {
            assert(crate::exec::frame::elem_ok(p.doc, p.open[0]));
        } else if is_html(p.open[i], Tag::Template) {
            assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
            lemma_contents_pok(p.doc, p.open[i].id);
        } else {
            let t = p.open[i].id;
            assert(crate::exec::frame::elem_ok(p.doc, p.open[i]));
            match p.doc.nodes[t as int].parent {
                Some(par) => {
                    crate::exec::insert::lemma_wf_parent(p.doc, t);
                    if node_is_template(p.doc, par) {
                        lemma_contents_pok(p.doc, par);
                    }
                },
                None => {
                    assert(i != 0);
                    assert(crate::exec::frame::elem_ok(p.doc, p.open[i - 1]));
                    if is_html(p.open[i - 1], Tag::Template) {
                        lemma_contents_pok(p.doc, p.open[i - 1].id);
                    }
                },
            }
        }
    } else if is_html(target, Tag::Template) {
        lemma_contents_pok(p.doc, target.id);
    }
}

/// §13.2.6.1 "adjusted insertion location": on a rooted stack, or with a
/// location whose parent may receive a child, the parent may receive a
/// child.
pub proof fn lemma_adjusted_pok(p: Parser, loc: Option<Location>)
    requires
        dinv(p),
        match loc {
            Some(l) => pok(p.doc, l.parent),
            None => rooted(p),
        },
    ensures
        pok(p.doc, adjusted_location(p, loc).parent),
{
    lemma_dinv(p);
    if loc is None {
        lemma_place_pok(p, None);
    }
}

} // verus!
