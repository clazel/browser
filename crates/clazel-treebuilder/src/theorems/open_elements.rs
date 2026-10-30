//! `theorem_open_elements_in_doc` (Phase 4 item 4.9): one `dispatch` step
//! keeps `invariant::ids_in_doc` (every id on the stack of open elements and
//! in the list of active formatting elements is an element of the document
//! with the record's namespace and name, and the head and form element
//! pointers, the context and the redirection map name nodes of it) and
//! `clazel_dom::spec::wf`.
//!
//! The proof. [`st`] is `wf` of the document and `ids_in_doc`. Every helper
//! of the transcription keeps it and only extends the document ([`dext`]:
//! the arena grows and an element keeps its namespace and local name, a
//! fragment stays a fragment), and adds at most a stated number of nodes
//! ([`kp`]); the elements it pushes onto the stack or the list are ones it
//! created. Every guarded DOM call meets `clazel-dom`'s preconditions, so
//! `clazel_dom::lemmas` gives `wf` and the kinds of the old nodes. The
//! helpers also keep [`fx`] (no entry of the list is for a `template` start
//! tag, and no two entries are for the same element), which
//! [`super::nodes`] needs to count the nodes the adoption agency creates,
//! [`od`] (until parsing stops, no two entries of the stack of open
//! elements are for the same element: every element pushed is new, but the
//! `head` element "after head" pushes back and then removes; see
//! [`theorem_open_distinct`]), and the insertion target redirection map.
//!
//! The hypotheses. A few rules read an entry of the stack of open
//! elements without checking that the stack has one ("in body"'s `html` and
//! `body` start tags give the attributes of `open[0]` and `open[1]` to those
//! elements), and "after head" pushes the head element pointer's node as a
//! `head` element record. With an empty stack the transcription leaves the
//! document unspecified (a `Seq` update out of range), and with a head
//! element pointer that does not name a `head` element the stack would hold
//! a wrong record. So the theorems assume what the executable step assumes:
//! `invariant::dispatch_needs` (every rule application of the step meets
//! `invariant::rooted_needs`; `reachable::run::lemma_dispatch_reach` proves
//! it from `invariant::reachable_inv`), and, until parsing stops,
//! `invariant::head_ok` (part of `parser_inv`), which the step keeps.
//! `theorem_doc_wf` (the document stays well formed) comes out of the same
//! proof. `super::reachable` discharges these hypotheses for every parser
//! reachable from `new_parser` or `fragment_parser`
//! (`theorem_reachable_doc_wf`, `theorem_reachable_open_elements_in_doc`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The relations

/// Node kind `b` keeps what the parse state relies on of `a`: an element's
/// namespace and local name, and that a fragment is a fragment.
pub open spec fn kind_ok(a: NodeKind, b: NodeKind) -> bool {
    &&& a is Element ==> {
        &&& b is Element
        &&& b->Element_namespace == a->Element_namespace
        &&& b->Element_local_name == a->Element_local_name
    }
    &&& a is DocumentFragment ==> b is DocumentFragment
}

/// `d1` extends `d0`: no node is lost and every node keeps [`kind_ok`].
pub open spec fn dext(d0: Document, d1: Document) -> bool {
    &&& d0.nodes.len() <= d1.nodes.len()
    &&& forall|i: int| 0 <= i < d0.nodes.len() ==> kind_ok(d0.nodes[i].kind, #[trigger] d1.nodes[i].kind)
}

/// What the theorem carries: the document is well formed, every id of the
/// parse state is a node of it, and until parsing stops the head element
/// pointer names an HTML `head` element (`invariant::head_ok`, which "after
/// head" needs).
#[verifier::opaque]
pub open spec fn st(p: Parser) -> bool {
    dom::wf(p.doc) && ids_in_doc(p) && (p.stopped || head_ok(p))
}

/// No two entries of the list of active formatting elements are for the
/// same element.
pub open spec fn fmt_unique(p: Parser) -> bool {
    forall|i: int, j: int|
        0 <= i < p.formatting.len() && 0 <= j < p.formatting.len() && i != j && (#[trigger] p.formatting[i]) is Entry && (
        #[trigger] p.formatting[j]) is Entry ==> p.formatting[i]->Entry_elem.id != p.formatting[j]->Entry_elem.id
}

/// The facts about the list of active formatting elements that the node
/// count needs: `termination::formatting_ok` and [`fmt_unique`].
pub open spec fn fx(p: Parser) -> bool {
    crate::termination::formatting_ok(p) && fmt_unique(p)
}

/// Until parsing stops, the stack of open elements holds distinct elements
/// (`independent::equivalence_foreign::open_distinct`).
pub open spec fn od(p: Parser) -> bool {
    p.stopped || crate::independent::equivalence_foreign::open_distinct(p.open)
}

/// Every entry of the list of active formatting elements is for an HTML
/// element (the parser pushes only elements it creates for formatting
/// tags in the HTML namespace).
pub open spec fn fh(p: Parser) -> bool {
    forall|i: int| 0 <= i < p.formatting.len() && (#[trigger] p.formatting[i]) is Entry ==> p.formatting[i]->Entry_elem.ns
        == Namespace::Html
}

/// `q` comes from `p` keeping [`st`], extending the document by at most `c`
/// nodes, keeping [`fx`], [`od`] and [`fh`], and keeping the insertion
/// target redirection map (no rule changes it).
#[verifier::opaque]
pub open spec fn kp(p: Parser, q: Parser, c: nat) -> bool {
    &&& st(q)
    &&& dext(p.doc, q.doc)
    &&& q.doc.nodes.len() <= p.doc.nodes.len() + c
    &&& fx(p) ==> fx(q)
    &&& od(p) ==> od(q)
    &&& fh(p) ==> fh(q)
    &&& q.redirect == p.redirect
}

/// The nodes an element created for a token takes: two for an HTML
/// `template` (its template contents), else one.
pub open spec fn elem_cost(ns: Namespace, tag: Tag) -> nat {
    if ns == Namespace::Html && tag == Tag::Template {
        2
    } else {
        1
    }
}

// ---------------------------------------------------------------------
// The relations compose

/// [`dext`] is reflexive.
pub proof fn lemma_dext_refl(d: Document)
    ensures
        dext(d, d),
{
}

/// [`dext`] is transitive.
pub proof fn lemma_dext_trans(d0: Document, d1: Document, d2: Document)
    requires
        dext(d0, d1),
        dext(d1, d2),
    ensures
        dext(d0, d2),
{
    assert forall|i: int| 0 <= i < d0.nodes.len() implies kind_ok(d0.nodes[i].kind, #[trigger] d2.nodes[i].kind) by {
        assert(kind_ok(d0.nodes[i].kind, d1.nodes[i].kind));
        assert(kind_ok(d1.nodes[i].kind, d2.nodes[i].kind));
    }
}

/// What [`st`] says.
pub proof fn lemma_st(p: Parser)
    requires
        st(p),
    ensures
        dom::wf(p.doc),
        ids_in_doc(p),
        p.stopped || head_ok(p),
{
    reveal(st);
}

/// What [`kp`] says.
pub proof fn lemma_kp(p: Parser, q: Parser, c: nat)
    requires
        kp(p, q, c),
    ensures
        st(q),
        dext(p.doc, q.doc),
        q.doc.nodes.len() <= p.doc.nodes.len() + c,
        fx(p) ==> fx(q),
        od(p) ==> od(q),
        fh(p) ==> fh(q),
        q.redirect == p.redirect,
{
    reveal(kp);
}

/// A well-formed arena holds the document node.
pub proof fn lemma_wf_nonempty(d: Document)
    requires
        dom::wf(d),
    ensures
        d.nodes.len() >= 1,
{
    let _ = clazel_dom::lemmas::lemma_wf_witness(d);
}

/// [`kp`] is reflexive.
pub proof fn lemma_kp_refl(p: Parser)
    requires
        st(p),
    ensures
        kp(p, p, 0),
{
    reveal(kp);
}

/// [`kp`] composes.
pub proof fn lemma_kp_trans(p: Parser, q: Parser, r: Parser, c1: nat, c2: nat)
    requires
        kp(p, q, c1),
        kp(q, r, c2),
    ensures
        kp(p, r, c1 + c2),
{
    reveal(kp);
    lemma_dext_trans(p.doc, q.doc, r.doc);
}

/// [`kp`] to a parser that differs from `q` only in fields [`st`] and [`fx`]
/// do not read.
pub proof fn lemma_kp_fields(p: Parser, q: Parser, r: Parser, c: nat)
    requires
        kp(p, q, c),
        r.doc == q.doc,
        r.open == q.open,
        r.formatting == q.formatting,
        r.head == q.head,
        r.form == q.form,
        r.context == q.context,
        r.redirect == q.redirect,
        r.stopped == q.stopped,
    ensures
        kp(p, r, c),
{
    reveal(kp);
    reveal(st);
}

/// [`kp`] with a larger bound.
pub proof fn lemma_kp_weaken(p: Parser, q: Parser, c1: nat, c2: nat)
    requires
        kp(p, q, c1),
        c1 <= c2,
    ensures
        kp(p, q, c2),
{
    reveal(kp);
}

/// An element of `d0` is one of `d1`.
pub proof fn lemma_elem_dext(d0: Document, d1: Document, e: Elem)
    requires
        elem_in_doc(d0, e),
        dext(d0, d1),
    ensures
        elem_in_doc(d1, e),
{
    assert(kind_ok(d0.nodes[e.id as int].kind, d1.nodes[e.id as int].kind));
}

/// Replacing the document by a well-formed extension keeps [`st`].
pub proof fn lemma_st_doc(p: Parser, d: Document)
    requires
        st(p),
        dom::wf(d),
        dext(p.doc, d),
    ensures
        st(Parser { doc: d, ..p }),
        kp(p, Parser { doc: d, ..p }, (d.nodes.len() - p.doc.nodes.len()) as nat),
{
    reveal(st);
    reveal(kp);
    let q = Parser { doc: d, ..p };
    assert forall|i: int| 0 <= i < q.open.len() implies elem_in_doc(d, #[trigger] q.open[i]) by {
        assert(elem_in_doc(p.doc, p.open[i]));
        lemma_elem_dext(p.doc, d, p.open[i]);
    }
    assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_in_doc(
        d,
        q.formatting[i]->Entry_elem,
    ) by {
        assert(elem_in_doc(p.doc, p.formatting[i]->Entry_elem));
        lemma_elem_dext(p.doc, d, p.formatting[i]->Entry_elem);
    }
    if let Some(c) = p.context {
        lemma_elem_dext(p.doc, d, c);
    }
    if let Some((r, f)) = p.redirect {
        assert(kind_ok(p.doc.nodes[f as int].kind, d.nodes[f as int].kind));
    }
    if !p.stopped {
        if let Some(h) = p.head {
            lemma_elem_dext(p.doc, d, head_elem(h));
        }
    }
}

/// A parser with the same document and pointers whose stack holds elements
/// of the document and whose list is a list of `p`'s keeps [`st`] (the
/// stack and list helpers).
pub proof fn lemma_st_lists(p: Parser, q: Parser)
    requires
        st(p),
        q.doc == p.doc,
        q.head == p.head,
        q.form == p.form,
        q.context == p.context,
        q.redirect == p.redirect,
        q.stopped == p.stopped,
        forall|i: int| 0 <= i < q.open.len() ==> elem_in_doc(q.doc, #[trigger] q.open[i]),
        forall|i: int|
            0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry ==> elem_in_doc(q.doc, q.formatting[i]->Entry_elem),
    ensures
        st(q),
        kp(p, q, 0) <==> ((fx(p) ==> fx(q)) && (od(p) ==> od(q)) && (fh(p) ==> fh(q))),
{
    reveal(st);
    reveal(kp);
}

// ---------------------------------------------------------------------
// Guarded DOM calls

/// `insert`, when [`insert_valid`] holds.
pub proof fn lemma_dom_insert(p: Parser, node: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        st(p),
    ensures
        kp(p, dom_insert(p, node, parent, child), 0),
        dom_insert(p, node, parent, child) == (Parser { doc: dom_insert(p, node, parent, child).doc, ..p }),
        p.stopped ==> dom_insert(p, node, parent, child) == p,
{
    reveal(st);
    if !(p.stopped || !insert_valid(p.doc, node, parent, child)) {
        let d = dom::insert(p.doc, node, parent, child);
        clazel_dom::lemmas::theorem_insert_wf(p.doc, node, parent, child);
        clazel_dom::lemmas::theorem_ids_stable(p.doc);
        assert(clazel_dom::lemmas::ids_stable(p.doc, d, 0, -1));
        assert forall|i: int| 0 <= i < p.doc.nodes.len() implies kind_ok(p.doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
            assert(d.nodes[i].kind == p.doc.nodes[i].kind);
        }
        lemma_st_doc(p, d);
    } else {
        lemma_kp_refl(p);
    }
}

/// `remove`, when the node has a parent.
pub proof fn lemma_dom_remove(p: Parser, node: NodeId)
    requires
        st(p),
    ensures
        kp(p, dom_remove(p, node), 0),
        dom_remove(p, node) == (Parser { doc: dom_remove(p, node).doc, ..p }),
        p.stopped ==> dom_remove(p, node) == p,
{
    reveal(st);
    if !(p.stopped || !dom::valid(p.doc, node) || p.doc.nodes[node as int].parent is None) {
        let d = dom::remove(p.doc, node);
        clazel_dom::lemmas::theorem_remove_wf(p.doc, node);
        clazel_dom::lemmas::theorem_ids_stable(p.doc);
        assert(clazel_dom::lemmas::ids_stable(p.doc, d, 0, -1));
        assert forall|i: int| 0 <= i < p.doc.nodes.len() implies kind_ok(p.doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
            assert(d.nodes[i].kind == p.doc.nodes[i].kind);
        }
        lemma_st_doc(p, d);
    } else {
        lemma_kp_refl(p);
    }
}

/// Stop parsing.
pub proof fn lemma_stop_parsing(p: Parser)
    requires
        st(p),
    ensures
        kp(p, stop_parsing(p), 0),
        stop_parsing(p).doc == p.doc,
        stop_parsing(p).formatting == p.formatting,
        stop_parsing(p).stopped,
{
    reveal(st);
    reveal(kp);
}

/// Create a node of a kind the arena accepts.
pub proof fn lemma_create(p: Parser, k: NodeKind)
    requires
        st(p),
        dom::creatable(p.doc, k),
    ensures
        ({
            let (q, id) = create(p, k);
            &&& kp(p, q, 1)
            &&& docish(p, q)
            &&& dom::valid(q.doc, id)
            &&& !q.stopped ==> {
                &&& q == Parser { doc: q.doc, ..p }
                &&& id == p.doc.nodes.len()
                &&& q.doc.nodes.len() == p.doc.nodes.len() + 1
                &&& q.doc.nodes[id as int].kind == k
            }
        }),
{
    lemma_st(p);
    lemma_wf_nonempty(p.doc);
    if p.stopped {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 1);
    } else if !dom::can_create(p.doc, 1) {
        lemma_stop_parsing(p);
        lemma_kp_weaken(p, stop_parsing(p), 0, 1);
    } else {
        lemma_st(p);
        let d = dom::create_node(p.doc, k).0;
        clazel_dom::lemmas::theorem_create_node_wf(p.doc, k);
        assert forall|i: int| 0 <= i < p.doc.nodes.len() implies kind_ok(p.doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
            assert(d.nodes[i] == p.doc.nodes[i]);
        }
        lemma_st_doc(p, d);
    }
}

/// Set the document's mode.
pub proof fn lemma_set_document_mode(p: Parser, mode: DocumentMode)
    requires
        st(p),
    ensures
        kp(p, set_document_mode(p, mode), 0),
        set_document_mode(p, mode) == (Parser { doc: set_document_mode(p, mode).doc, ..p }),
{
    reveal(st);
    if !p.stopped {
        let d = dom::set_mode(p.doc, mode);
        clazel_dom::lemmas::theorem_set_mode_wf(p.doc, mode);
        clazel_dom::lemmas::theorem_ids_stable(p.doc);
        assert(clazel_dom::lemmas::ids_stable(p.doc, d, 0, 0));
        assert forall|i: int| 0 <= i < p.doc.nodes.len() implies kind_ok(p.doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
            if i != 0 {
                assert(d.nodes[i].kind == p.doc.nodes[i].kind);
            }
        }
        lemma_st_doc(p, d);
    } else {
        lemma_kp_refl(p);
    }
}

/// Append data to a `Text` node.
pub proof fn lemma_append_data(p: Parser, n: NodeId, data: Seq<u32>)
    requires
        st(p),
        dom::valid(p.doc, n),
        p.doc.nodes[n as int].kind is Text,
    ensures
        kp(p, Parser { doc: dom::append_data(p.doc, n, data), ..p }, 0),
{
    reveal(st);
    let d = dom::append_data(p.doc, n, data);
    clazel_dom::lemmas::theorem_append_data_wf(p.doc, n, data);
    clazel_dom::lemmas::theorem_ids_stable(p.doc);
    assert(clazel_dom::lemmas::ids_stable(p.doc, d, 0, n as int));
    assert forall|i: int| 0 <= i < p.doc.nodes.len() implies kind_ok(p.doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        if i != n {
            assert(d.nodes[i].kind == p.doc.nodes[i].kind);
        }
    }
    lemma_st_doc(p, d);
}

/// Append an attribute to an element.
pub proof fn lemma_append_attribute(p: Parser, e: NodeId, a: Attr)
    requires
        st(p),
        dom::valid(p.doc, e),
        p.doc.nodes[e as int].kind is Element,
    ensures
        kp(p, Parser { doc: dom::append_attribute(p.doc, e, a), ..p }, 0),
        dom::append_attribute(p.doc, e, a).nodes[e as int].kind is Element,
{
    reveal(st);
    let d = dom::append_attribute(p.doc, e, a);
    clazel_dom::lemmas::theorem_append_attribute_wf(p.doc, e, a);
    clazel_dom::lemmas::theorem_ids_stable(p.doc);
    assert(clazel_dom::lemmas::ids_stable(p.doc, d, 0, e as int));
    assert forall|i: int| 0 <= i < p.doc.nodes.len() implies kind_ok(p.doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        if i != e {
            assert(d.nodes[i].kind == p.doc.nodes[i].kind);
        }
    }
    lemma_st_doc(p, d);
}

// ---------------------------------------------------------------------
// Creating and inserting nodes (§13.2.6.1)

/// Only the document changes, or parsing stops (and the stack is emptied):
/// the frame of the inserting helpers.
pub open spec fn docish(p: Parser, q: Parser) -> bool {
    &&& q.formatting == p.formatting
    &&& q.pending_table_text == p.pending_table_text
    &&& q.template_modes == p.template_modes
    &&& q.mode == p.mode
    &&& q.original_mode == p.original_mode
    &&& q.head == p.head
    &&& q.form == p.form
    &&& q.context == p.context
    &&& (p.stopped ==> q == p)
    &&& (q.open == p.open || (q.stopped && q.open.len() == 0))
}

/// [`docish`] composes.
pub proof fn lemma_docish_trans(p: Parser, q: Parser, r: Parser)
    requires
        docish(p, q),
        docish(q, r),
    ensures
        docish(p, r),
{
}

/// The form owner create an element for a token gives.
pub open spec fn owner_of(p: Parser, t: TagTok, ns: Namespace, intended_parent: NodeId) -> Option<NodeId> {
    if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, intended_parent, p.form->Some_0) {
        p.form
    } else {
        None
    }
}

/// Create an element for a token: a new element (and, for a template, its
/// template contents).
pub proof fn lemma_create_element_for_token(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    requires
        st(p),
    ensures
        ({
            let (q, e) = create_element_for_token(p, t, ns, ip);
            &&& kp(p, q, elem_cost(ns, t.tag))
            &&& docish(p, q)
            &&& dom::valid(q.doc, e.id)
            &&& e.ns == ns
            &&& e.tag == t.tag
            &&& e.name == t.name
            &&& !q.stopped ==> {
                &&& q == Parser { doc: q.doc, ..p }
                &&& e.id == p.doc.nodes.len()
                &&& elem_in_doc(q.doc, e)
            }
        }),
{
    hide(create);
    let owner = owner_of(p, t, ns, ip);
    let k = NodeKind::Element {
        namespace: Some(ns),
        prefix: None,
        local_name: t.name,
        attributes: t.attrs,
        template_contents: None,
        form_owner: owner,
    };
    lemma_st(p);
    assert(dom::creatable(p.doc, k));
    lemma_create(p, k);
    let (p1, id) = create(p, k);
    lemma_kp(p, p1, 1);
    let e = create_element_for_token(p, t, ns, ip).1;
    if ns == Namespace::Html && t.tag == Tag::Template && !p1.stopped {
        if !dom::can_create(p1.doc, 1) {
            lemma_stop_parsing(p1);
            lemma_kp_trans(p, p1, stop_parsing(p1), 1, 0);
            lemma_kp_weaken(p, stop_parsing(p1), 1, 2);
        } else {
            let d = dom::create_template_contents(p1.doc, id).0;
            lemma_st(p1);
            assert(clazel_dom::contract::create_template_contents_requires(p1.doc, id));
            clazel_dom::lemmas::theorem_create_template_contents_wf(p1.doc, id);
            clazel_dom::lemmas::theorem_ids_stable(p1.doc);
            assert(clazel_dom::lemmas::ids_stable(p1.doc, d, 1, id as int));
            assert forall|i: int| 0 <= i < p1.doc.nodes.len() implies kind_ok(
                p1.doc.nodes[i].kind,
                #[trigger] d.nodes[i].kind,
            ) by {
                if i != id {
                    assert(d.nodes[i].kind == p1.doc.nodes[i].kind);
                }
            }
            lemma_st_doc(p1, d);
            lemma_kp_trans(p, p1, Parser { doc: d, ..p1 }, 1, 1);
            assert(elem_in_doc(d, e));
        }
    } else {
        lemma_kp_weaken(p, p1, 1, elem_cost(ns, t.tag));
        if !p1.stopped {
            assert(elem_in_doc(p1.doc, e));
        }
    }
}

/// Insert an element at the adjusted insertion location.
pub proof fn lemma_insert_element_at(p: Parser, el: NodeId, loc: Option<Location>)
    requires
        st(p),
    ensures
        kp(p, insert_element_at(p, el, loc), 0),
        insert_element_at(p, el, loc) == (Parser { doc: insert_element_at(p, el, loc).doc, ..p }),
        p.stopped ==> insert_element_at(p, el, loc) == p,
{
    let l = adjusted_location(p, loc);
    lemma_dom_insert(p, el, l.parent, l.child);
    lemma_kp_refl(p);
}

/// Insert a foreign element: the element is created, inserted and pushed.
pub proof fn lemma_insert_foreign_element(p: Parser, t: TagTok, ns: Namespace)
    requires
        st(p),
    ensures
        ({
            let (q, e) = insert_foreign_element(p, t, ns);
            &&& kp(p, q, elem_cost(ns, t.tag))
            &&& dom::valid(q.doc, e.id)
            &&& q.formatting == p.formatting
            &&& q.pending_table_text == p.pending_table_text
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.head == p.head
            &&& q.form == p.form
            &&& q.context == p.context
            &&& (p.stopped ==> q == p)
            &&& e.ns == ns
            &&& e.tag == t.tag
            &&& e.name == t.name
            &&& !q.stopped ==> {
                &&& q.open == p.open.push(e)
                &&& e.id == p.doc.nodes.len()
                &&& elem_in_doc(q.doc, e)
            }
            &&& q.stopped ==> q.open.len() == 0 || q.open == p.open
        }),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    let ip = appropriate_place(p, None).parent;
    lemma_create_element_for_token(p, t, ns, ip);
    let (p1, e) = create_element_for_token(p, t, ns, ip);
    lemma_kp(p, p1, elem_cost(ns, t.tag));
    lemma_insert_element_at(p1, e.id, None);
    let p2 = insert_element_at(p1, e.id, None);
    lemma_kp_trans(p, p1, p2, elem_cost(ns, t.tag), 0);
    if !p2.stopped {
        lemma_kp(p1, p2, 0);
        lemma_elem_dext(p1.doc, p2.doc, e);
        let q = push(p2, e);
        lemma_st(p2);
        assert forall|i: int| 0 <= i < q.open.len() implies elem_in_doc(q.doc, #[trigger] q.open[i]) by {
            if i < p2.open.len() {
                assert(q.open[i] == p2.open[i]);
            }
        }
        lemma_fresh(p, e.id);
        if od(p2) {
            lemma_distinct_push(p2.open, e);
        }
        lemma_st_lists(p2, q);
        lemma_kp_trans(p, p2, q, elem_cost(ns, t.tag), 0);
    }
}

/// Insert an HTML element.
pub proof fn lemma_insert_html_element(p: Parser, t: TagTok)
    requires
        st(p),
    ensures
        ({
            let (q, e) = insert_html_element(p, t);
            &&& kp(p, q, elem_cost(Namespace::Html, t.tag))
            &&& dom::valid(q.doc, e.id)
            &&& q.formatting == p.formatting
            &&& q.pending_table_text == p.pending_table_text
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.head == p.head
            &&& q.form == p.form
            &&& q.context == p.context
            &&& (p.stopped ==> q == p)
            &&& e.ns == Namespace::Html
            &&& e.tag == t.tag
            &&& e.name == t.name
            &&& !q.stopped ==> {
                &&& q.open == p.open.push(e)
                &&& e.id == p.doc.nodes.len()
                &&& elem_in_doc(q.doc, e)
            }
            &&& q.stopped ==> q.open.len() == 0 || q.open == p.open
        }),
{
    hide(insert_foreign_element);
    lemma_insert_foreign_element(p, t, Namespace::Html);
}

/// Insert characters: data is appended to a `Text` node, or a new one is
/// inserted.
pub proof fn lemma_insert_characters(p: Parser, data: Seq<u32>)
    requires
        st(p),
    ensures
        kp(p, insert_characters(p, data), 1),
        docish(p, insert_characters(p, data)),
{
    hide(create);
    hide(dom_insert);
    hide(adjusted_location);
    let loc = adjusted_location(p, None);
    let doc = p.doc;
    if p.stopped || doc.nodes[loc.parent as int].kind is Document {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 1);
    } else {
        let prev = match loc.child {
            Some(c) => dom::previous_sibling(doc, c),
            None => dom::last_child(doc, loc.parent),
        };
        if prev is Some && dom::valid(doc, prev->Some_0) && doc.nodes[prev->Some_0 as int].kind is Text {
            lemma_append_data(p, prev->Some_0, data);
            lemma_kp_weaken(p, Parser { doc: dom::append_data(p.doc, prev->Some_0, data), ..p }, 0, 1);
        } else {
            lemma_create(p, NodeKind::Text { data });
            let (p1, text) = create(p, NodeKind::Text { data });
            lemma_kp(p, p1, 1);
            lemma_dom_insert(p1, text, loc.parent, loc.child);
            lemma_kp_trans(p, p1, dom_insert(p1, text, loc.parent, loc.child), 1, 0);
        }
    }
}

/// Insert a character.
pub proof fn lemma_insert_char(p: Parser, c: u32)
    requires
        st(p),
    ensures
        kp(p, insert_char(p, c), 1),
        docish(p, insert_char(p, c)),
{
    hide(insert_characters);
    lemma_insert_characters(p, seq![c]);
}

/// Insert a comment.
pub proof fn lemma_insert_comment(p: Parser, data: Seq<u32>, loc: Option<Location>)
    requires
        st(p),
    ensures
        kp(p, insert_comment(p, data, loc), 1),
        docish(p, insert_comment(p, data, loc)),
{
    hide(create);
    hide(dom_insert);
    hide(adjusted_location);
    let l = adjusted_location(p, loc);
    lemma_create(p, NodeKind::Comment { data });
    let (p1, c) = create(p, NodeKind::Comment { data });
    lemma_kp(p, p1, 1);
    lemma_dom_insert(p1, c, l.parent, l.child);
    lemma_kp_trans(p, p1, dom_insert(p1, c, l.parent, l.child), 1, 0);
}

/// Insert a processing instruction.
pub proof fn lemma_insert_pi(p: Parser, target: Seq<u32>, data: Seq<u32>, loc: Option<Location>)
    requires
        st(p),
    ensures
        kp(p, insert_pi(p, target, data, loc), 1),
        docish(p, insert_pi(p, target, data, loc)),
{
    hide(create);
    hide(dom_insert);
    hide(adjusted_location);
    let l = adjusted_location(p, loc);
    lemma_create(p, NodeKind::ProcessingInstruction { target, data });
    let (p1, n) = create(p, NodeKind::ProcessingInstruction { target, data });
    lemma_kp(p, p1, 1);
    lemma_dom_insert(p1, n, l.parent, l.child);
    lemma_kp_trans(p, p1, dom_insert(p1, n, l.parent, l.child), 1, 0);
}

/// The generic raw text and RCDATA element parsing algorithms.
pub proof fn lemma_generic_text_parsing(p: Parser, t: TagTok, rawtext: bool)
    requires
        st(p),
    ensures
        kp(p, generic_text_parsing(p, t, rawtext), elem_cost(Namespace::Html, t.tag)),
        generic_text_parsing(p, t, rawtext).formatting == p.formatting,
{
    hide(insert_html_element);
    lemma_insert_html_element(p, t);
    let p1 = insert_html_element(p, t).0;
    lemma_kp_fields(p, p1, generic_text_parsing(p, t, rawtext), elem_cost(Namespace::Html, t.tag));
}

// ---------------------------------------------------------------------
// Distinct stacks ([`od`])

/// No entry of the stack `o` is for the element `id`.
pub open spec fn not_on(o: Seq<Elem>, id: NodeId) -> bool {
    forall|j: int| 0 <= j < o.len() ==> (#[trigger] o[j]).id != id
}

/// A prefix of a stack of distinct elements holds distinct elements.
pub proof fn lemma_distinct_prefix(o: Seq<Elem>, q: Seq<Elem>)
    requires
        crate::independent::equivalence_foreign::open_distinct(o),
        q.len() <= o.len(),
        forall|i: int| 0 <= i < q.len() ==> #[trigger] q[i] == o[i],
    ensures
        crate::independent::equivalence_foreign::open_distinct(q),
{
    assert forall|j: int, k: int| 0 <= j < k < q.len() implies #[trigger] q[j].id != #[trigger] q[k].id by {
        assert(q[j] == o[j]);
        assert(q[k] == o[k]);
    }
}

/// Pushing an element that is not on a stack of distinct elements.
pub proof fn lemma_distinct_push(o: Seq<Elem>, e: Elem)
    requires
        crate::independent::equivalence_foreign::open_distinct(o),
        not_on(o, e.id),
    ensures
        crate::independent::equivalence_foreign::open_distinct(o.push(e)),
{
    let q = o.push(e);
    assert forall|j: int, k: int| 0 <= j < k < q.len() implies #[trigger] q[j].id != #[trigger] q[k].id by {
        assert(q[j] == o[j]);
        if k < o.len() {
            assert(q[k] == o[k]);
        }
    }
}

/// Removing an entry of a stack of distinct elements: the rest are
/// distinct, and none is for the removed element.
pub proof fn lemma_distinct_remove(o: Seq<Elem>, i: int)
    requires
        crate::independent::equivalence_foreign::open_distinct(o),
        0 <= i < o.len(),
    ensures
        crate::independent::equivalence_foreign::open_distinct(o.remove(i)),
        not_on(o.remove(i), o[i].id),
{
    let q = o.remove(i);
    assert forall|j: int| 0 <= j < q.len() implies #[trigger] q[j] == o[if j < i {
        j
    } else {
        j + 1
    }] by {}
    assert forall|j: int, k: int| 0 <= j < k < q.len() implies #[trigger] q[j].id != #[trigger] q[k].id by {
        let j0 = if j < i {
            j
        } else {
            j + 1
        };
        let k0 = if k < i {
            k
        } else {
            k + 1
        };
        assert(q[j] == o[j0]);
        assert(q[k] == o[k0]);
    }
    assert forall|j: int| 0 <= j < q.len() implies (#[trigger] q[j]).id != o[i].id by {
        if j < i {
            assert(q[j] == o[j]);
        } else {
            assert(q[j] == o[j + 1]);
        }
    }
}

/// Replacing an entry of a stack of distinct elements by an element no
/// other entry is for.
pub proof fn lemma_distinct_update(o: Seq<Elem>, i: int, e: Elem)
    requires
        crate::independent::equivalence_foreign::open_distinct(o),
        0 <= i < o.len(),
        forall|j: int| 0 <= j < o.len() && j != i ==> (#[trigger] o[j]).id != e.id,
    ensures
        crate::independent::equivalence_foreign::open_distinct(o.update(i, e)),
{
    let q = o.update(i, e);
    assert forall|j: int, k: int| 0 <= j < k < q.len() implies #[trigger] q[j].id != #[trigger] q[k].id by {
        if j != i {
            assert(q[j] == o[j]);
        }
        if k != i {
            assert(q[k] == o[k]);
        }
    }
}

/// Removing an entry of a stack of distinct elements and inserting an
/// element that was not on it.
pub proof fn lemma_distinct_remove_insert(o: Seq<Elem>, j: int, k: int, e: Elem)
    requires
        crate::independent::equivalence_foreign::open_distinct(o),
        not_on(o, e.id),
        0 <= j < o.len(),
        0 <= k <= o.len() - 1,
    ensures
        crate::independent::equivalence_foreign::open_distinct(o.remove(j).insert(k, e)),
{
    let o1 = o.remove(j);
    lemma_distinct_remove(o, j);
    assert forall|m: int| 0 <= m < o1.len() implies (#[trigger] o1[m]).id != e.id by {
        if m < j {
            assert(o1[m] == o[m]);
        } else {
            assert(o1[m] == o[m + 1]);
        }
    }
    lemma_distinct_insert(o1, k, e);
}

/// Inserting an element that is not on a stack of distinct elements.
pub proof fn lemma_distinct_insert(o: Seq<Elem>, k: int, e: Elem)
    requires
        crate::independent::equivalence_foreign::open_distinct(o),
        not_on(o, e.id),
        0 <= k <= o.len(),
    ensures
        crate::independent::equivalence_foreign::open_distinct(o.insert(k, e)),
{
    let q = o.insert(k, e);
    assert forall|a: int, b: int| 0 <= a < b < q.len() implies #[trigger] q[a].id != #[trigger] q[b].id by {
        if a < k {
            assert(q[a] == o[a]);
        } else if a > k {
            assert(q[a] == o[a - 1]);
        }
        if b < k {
            assert(q[b] == o[b]);
        } else if b > k {
            assert(q[b] == o[b - 1]);
        }
    }
}

// ---------------------------------------------------------------------
// The stack of open elements and the list of active formatting elements

/// `q` is `p` with a prefix of its stack.
pub open spec fn pops(p: Parser, q: Parser) -> bool {
    &&& q == Parser { open: q.open, ..p }
    &&& q.open.len() <= p.open.len()
    &&& forall|i: int| 0 <= i < q.open.len() ==> #[trigger] q.open[i] == p.open[i]
}

/// [`pops`] keeps [`st`].
pub proof fn lemma_pops_kp(p: Parser, q: Parser)
    requires
        st(p),
        pops(p, q),
    ensures
        kp(p, q, 0),
{
    lemma_st(p);
    assert forall|i: int| 0 <= i < q.open.len() implies elem_in_doc(q.doc, #[trigger] q.open[i]) by {
        assert(q.open[i] == p.open[i]);
    }
    if od(p) && !p.stopped {
        lemma_distinct_prefix(p.open, q.open);
    }
    lemma_st_lists(p, q);
}

/// [`pops`] composes.
pub proof fn lemma_pops_trans(p: Parser, q: Parser, r: Parser)
    requires
        pops(p, q),
        pops(q, r),
    ensures
        pops(p, r),
{
    assert forall|i: int| 0 <= i < r.open.len() implies #[trigger] r.open[i] == p.open[i] by {
        assert(r.open[i] == q.open[i]);
        assert(q.open[i] == p.open[i]);
    }
}

/// "Pop the current node".
pub proof fn lemma_pop(p: Parser)
    ensures
        pops(p, pop(p)),
{
}

/// Pop while the current node satisfies `f`.
pub proof fn lemma_pop_while(p: Parser, f: spec_fn(Elem) -> bool)
    ensures
        pops(p, pop_while(p, f)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        lemma_pop(p);
        lemma_pop_while(pop(p), f);
        lemma_pops_trans(p, pop(p), pop_while(pop(p), f));
    }
}

/// Generate implied end tags.
pub proof fn lemma_generate_implied_end_tags(p: Parser, except: Option<Tag>)
    ensures
        pops(p, generate_implied_end_tags(p, except)),
{
    lemma_pop_while(p, |e: Elem| implied_end_tag(e) && !(except is Some && e.tag == except->Some_0));
}

/// Generate all implied end tags thoroughly.
pub proof fn lemma_generate_all_implied_end_tags_thoroughly(p: Parser)
    ensures
        pops(p, generate_all_implied_end_tags_thoroughly(p)),
{
    lemma_pop_while(
        p,
        |e: Elem|
            e.ns == Namespace::Html && match e.tag {
                Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb
                | Tag::Rp | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
                _ => false,
            },
    );
}

/// Pop until an HTML element named `tag` has been popped.
pub proof fn lemma_pop_until_popped(p: Parser, tag: Tag)
    ensures
        pops(p, pop_until_popped(p, tag)),
    decreases p.open.len(),
{
    lemma_pop(p);
    if p.open.len() > 0 && !is_html(current_node(p), tag) {
        lemma_pop_until_popped(pop(p), tag);
        lemma_pops_trans(p, pop(p), pop_until_popped(pop(p), tag));
    }
}

/// Pop until a heading has been popped.
pub proof fn lemma_pop_until_heading_popped(p: Parser)
    ensures
        pops(p, pop_until_heading_popped(p)),
    decreases p.open.len(),
{
    lemma_pop(p);
    if p.open.len() > 0 && !is_heading(current_node(p)) {
        lemma_pop_until_heading_popped(pop(p));
        lemma_pops_trans(p, pop(p), pop_until_heading_popped(pop(p)));
    }
}

/// Pop until a node has been popped.
pub proof fn lemma_pop_until_node_popped(p: Parser, id: NodeId)
    ensures
        pops(p, pop_until_node_popped(p, id)),
    decreases p.open.len(),
{
    lemma_pop(p);
    if p.open.len() > 0 && current_node(p).id != id {
        lemma_pop_until_node_popped(pop(p), id);
        lemma_pops_trans(p, pop(p), pop_until_node_popped(pop(p), id));
    }
}

/// Pop until a named HTML element has been popped.
pub proof fn lemma_pop_until_named_popped(p: Parser, name: Seq<u32>)
    ensures
        pops(p, pop_until_named_popped(p, name)),
    decreases p.open.len(),
{
    lemma_pop(p);
    if p.open.len() > 0 && !is_html_named(current_node(p), name) {
        lemma_pop_until_named_popped(pop(p), name);
        lemma_pops_trans(p, pop(p), pop_until_named_popped(pop(p), name));
    }
}

/// Pop until a cell has been popped.
pub proof fn lemma_pop_until_cell_popped(p: Parser)
    ensures
        pops(p, pop_until_cell_popped(p)),
    decreases p.open.len(),
{
    lemma_pop(p);
    if p.open.len() > 0 && !(is_html(current_node(p), Tag::Td) || is_html(current_node(p), Tag::Th)) {
        lemma_pop_until_cell_popped(pop(p));
        lemma_pops_trans(p, pop(p), pop_until_cell_popped(pop(p)));
    }
}

/// Close a `p` element.
pub proof fn lemma_close_p_element(p: Parser)
    ensures
        pops(p, close_p_element(p)),
{
    let q = generate_implied_end_tags(p, Some(Tag::P));
    lemma_generate_implied_end_tags(p, Some(Tag::P));
    lemma_pop_until_popped(q, Tag::P);
    lemma_pops_trans(p, q, pop_until_popped(q, Tag::P));
}

/// Close a `p` element if one is in button scope.
pub proof fn lemma_close_p_if_in_button_scope(p: Parser)
    ensures
        pops(p, close_p_if_in_button_scope(p)),
{
    lemma_close_p_element(p);
}

/// The index `last_index_where` finds is an index of the stack, or -1.
pub proof fn lemma_last_index_where_range(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= i <= open.len(),
    ensures
        -1 <= last_index_where(open, i, f) < i,
        last_index_where(open, i, f) >= 0 ==> f(open[last_index_where(open, i, f)]),
    decreases i,
{
    if i > 0 && !f(open[i - 1]) {
        lemma_last_index_where_range(open, i - 1, f);
    }
}

/// Remove an entry of the stack.
pub proof fn lemma_remove_open_at(p: Parser, i: int)
    requires
        st(p),
        0 <= i < p.open.len(),
    ensures
        kp(p, remove_open_at(p, i), 0),
        remove_open_at(p, i) == (Parser { open: remove_open_at(p, i).open, ..p }),
        remove_open_at(p, i).open.len() == p.open.len() - 1,
{
    lemma_st(p);
    let q = remove_open_at(p, i);
    assert forall|j: int| 0 <= j < q.open.len() implies elem_in_doc(q.doc, #[trigger] q.open[j]) by {
        if j < i {
            assert(q.open[j] == p.open[j]);
        } else {
            assert(q.open[j] == p.open[j + 1]);
        }
    }
    if od(p) && !p.stopped {
        lemma_distinct_remove(p.open, i);
    }
    lemma_st_lists(p, q);
}

/// Reset the insertion mode appropriately.
pub proof fn lemma_reset_insertion_mode(p: Parser)
    requires
        st(p),
    ensures
        kp(p, reset_insertion_mode(p), 0),
        reset_insertion_mode(p) == (Parser { mode: reset_insertion_mode(p).mode, ..p }),
{
    lemma_kp_refl(p);
    lemma_kp_fields(p, p, reset_insertion_mode(p), 0);
}

/// Insert a marker.
pub proof fn lemma_push_marker(p: Parser)
    requires
        st(p),
    ensures
        kp(p, push_marker(p), 0),
        push_marker(p) == (Parser { formatting: push_marker(p).formatting, ..p }),
        push_marker(p).formatting.len() == p.formatting.len() + 1,
{
    lemma_st(p);
    let q = push_marker(p);
    assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_in_doc(
        q.doc,
        q.formatting[i]->Entry_elem,
    ) by {
        assert(q.formatting[i] == p.formatting[i]);
    }
    if fx(p) {
        assert forall|i: int, j: int|
            0 <= i < q.formatting.len() && 0 <= j < q.formatting.len() && i != j && (#[trigger] q.formatting[i]) is Entry && (
            #[trigger] q.formatting[j]) is Entry implies q.formatting[i]->Entry_elem.id != q.formatting[j]->Entry_elem.id by {
            assert(q.formatting[i] == p.formatting[i]);
            assert(q.formatting[j] == p.formatting[j]);
        }
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            assert(q.formatting[i] == p.formatting[i]);
        }
    }
    if fh(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.ns
            == Namespace::Html by {
            assert(q.formatting[i] == p.formatting[i]);
        }
    }
    lemma_st_lists(p, q);
}

/// `q`'s list is a prefix of `p`'s and nothing else changes.
pub open spec fn fmt_prefix(p: Parser, q: Parser) -> bool {
    &&& q == Parser { formatting: q.formatting, ..p }
    &&& q.formatting.len() <= p.formatting.len()
    &&& forall|i: int| 0 <= i < q.formatting.len() ==> #[trigger] q.formatting[i] == p.formatting[i]
}

/// [`fmt_prefix`] keeps [`st`] and [`fx`].
pub proof fn lemma_fmt_prefix_kp(p: Parser, q: Parser)
    requires
        st(p),
        fmt_prefix(p, q),
    ensures
        kp(p, q, 0),
{
    lemma_st(p);
    assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_in_doc(
        q.doc,
        q.formatting[i]->Entry_elem,
    ) by {
        assert(q.formatting[i] == p.formatting[i]);
    }
    if fx(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            assert(q.formatting[i] == p.formatting[i]);
        }
        assert forall|i: int, j: int|
            0 <= i < q.formatting.len() && 0 <= j < q.formatting.len() && i != j && (#[trigger] q.formatting[i]) is Entry && (
            #[trigger] q.formatting[j]) is Entry implies q.formatting[i]->Entry_elem.id != q.formatting[j]->Entry_elem.id by {
            assert(q.formatting[i] == p.formatting[i]);
            assert(q.formatting[j] == p.formatting[j]);
        }
    }
    if fh(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.ns
            == Namespace::Html by {
            assert(q.formatting[i] == p.formatting[i]);
        }
    }
    lemma_st_lists(p, q);
}

/// Clear the list of active formatting elements up to the last marker.
pub proof fn lemma_clear_to_last_marker(p: Parser)
    ensures
        fmt_prefix(p, clear_to_last_marker(p)),
    decreases p.formatting.len(),
{
    if p.formatting.len() > 0 {
        let q = Parser { formatting: p.formatting.drop_last(), ..p };
        if !(p.formatting.last() is Marker) {
            lemma_clear_to_last_marker(q);
            let r = clear_to_last_marker(q);
            assert forall|i: int| 0 <= i < r.formatting.len() implies #[trigger] r.formatting[i] == p.formatting[i] by {
                assert(r.formatting[i] == q.formatting[i]);
            }
        }
    }
}

/// [`fx`] of a list: no entry for a `template` start tag, no element twice.
pub open spec fn fx_seq(f: Seq<Fmt>) -> bool {
    &&& forall|i: int| 0 <= i < f.len() && #[trigger] f[i] is Entry ==> f[i]->Entry_token.tag != Tag::Template
    &&& forall|i: int, j: int|
        0 <= i < f.len() && 0 <= j < f.len() && i != j && (#[trigger] f[i]) is Entry && (#[trigger] f[j]) is Entry
            ==> f[i]->Entry_elem.id != f[j]->Entry_elem.id
}

/// [`fx`] is [`fx_seq`] of the list.
pub proof fn lemma_fx_seq(p: Parser)
    ensures
        fx(p) == fx_seq(p.formatting),
{
}

/// Removing an entry keeps [`fx_seq`].
pub proof fn lemma_fx_seq_remove(f: Seq<Fmt>, k: int)
    requires
        0 <= k < f.len(),
        fx_seq(f),
    ensures
        fx_seq(f.remove(k)),
{
    let g = f.remove(k);
    assert forall|i: int| 0 <= i < g.len() implies #[trigger] g[i] == f[if i < k {
        i
    } else {
        i + 1
    }] by {}
    assert forall|i: int, j: int|
        0 <= i < g.len() && 0 <= j < g.len() && i != j && (#[trigger] g[i]) is Entry && (#[trigger] g[j]) is Entry implies g[i]->Entry_elem.id
        != g[j]->Entry_elem.id by {
        let i0 = if i < k {
            i
        } else {
            i + 1
        };
        let j0 = if j < k {
            j
        } else {
            j + 1
        };
        assert(g[i] == f[i0]);
        assert(g[j] == f[j0]);
    }
}

/// Removing an entry of the list keeps [`st`] and [`fx`].
pub proof fn lemma_fmt_remove(p: Parser, k: int)
    requires
        st(p),
        0 <= k < p.formatting.len(),
    ensures
        kp(p, Parser { formatting: p.formatting.remove(k), ..p }, 0),
{
    lemma_st(p);
    let q = Parser { formatting: p.formatting.remove(k), ..p };
    assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_in_doc(
        q.doc,
        q.formatting[i]->Entry_elem,
    ) by {
        if i < k {
            assert(q.formatting[i] == p.formatting[i]);
        } else {
            assert(q.formatting[i] == p.formatting[i + 1]);
        }
    }
    lemma_fx_seq(p);
    lemma_fx_seq(q);
    if fx(p) {
        lemma_fx_seq_remove(p.formatting, k);
    }
    if fh(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.ns
            == Namespace::Html by {
            if i < k {
                assert(q.formatting[i] == p.formatting[i]);
            } else {
                assert(q.formatting[i] == p.formatting[i + 1]);
            }
        }
    }
    lemma_st_lists(p, q);
}

// ---------------------------------------------------------------------
// Without a count

/// [`kp`] without the count of new nodes (the adoption agency's count needs
/// [`fx`]).
#[verifier::opaque]
pub open spec fn kpu(p: Parser, q: Parser) -> bool {
    &&& st(q)
    &&& dext(p.doc, q.doc)
    &&& fx(p) ==> fx(q)
    &&& od(p) ==> od(q)
    &&& fh(p) ==> fh(q)
    &&& q.redirect == p.redirect
}

/// What [`kpu`] says.
pub proof fn lemma_kpu(p: Parser, q: Parser)
    requires
        kpu(p, q),
    ensures
        st(q),
        dext(p.doc, q.doc),
        fx(p) ==> fx(q),
        od(p) ==> od(q),
        fh(p) ==> fh(q),
        q.redirect == p.redirect,
{
    reveal(kpu);
}

/// [`kpu`] from its parts.
pub proof fn lemma_kpu_intro(p: Parser, q: Parser)
    requires
        st(q),
        dext(p.doc, q.doc),
        fx(p) ==> fx(q),
        od(p) ==> od(q),
        fh(p) ==> fh(q),
        q.redirect == p.redirect,
    ensures
        kpu(p, q),
{
    reveal(kpu);
}

/// [`kp`] implies [`kpu`].
pub proof fn lemma_kp_kpu(p: Parser, q: Parser, c: nat)
    requires
        kp(p, q, c),
    ensures
        kpu(p, q),
{
    reveal(kp);
    reveal(kpu);
}

/// [`kpu`] with a count is [`kp`].
pub proof fn lemma_kpu_kp(p: Parser, q: Parser, c: nat)
    requires
        kpu(p, q),
        q.doc.nodes.len() <= p.doc.nodes.len() + c,
    ensures
        kp(p, q, c),
{
    reveal(kp);
    reveal(kpu);
}

/// [`kpu`] composes.
pub proof fn lemma_kpu_trans(p: Parser, q: Parser, r: Parser)
    requires
        kpu(p, q),
        kpu(q, r),
    ensures
        kpu(p, r),
{
    reveal(kpu);
    lemma_dext_trans(p.doc, q.doc, r.doc);
}

/// [`kpu`] to a parser that differs from `q` only in fields [`st`] and
/// [`fx`] do not read.
pub proof fn lemma_kpu_fields(p: Parser, q: Parser, r: Parser)
    requires
        kpu(p, q),
        r.doc == q.doc,
        r.open == q.open,
        r.formatting == q.formatting,
        r.head == q.head,
        r.form == q.form,
        r.context == q.context,
        r.redirect == q.redirect,
        r.stopped == q.stopped,
    ensures
        kpu(p, r),
{
    lemma_kpu(p, q);
    lemma_kp_refl(q);
    lemma_kp_fields(q, q, r, 0);
    lemma_kp(q, r, 0);
    reveal(kpu);
}

// ---------------------------------------------------------------------
// Indices

/// `fmt_index_of` finds the last entry for `id`.
pub proof fn lemma_fmt_index_of(f: Seq<Fmt>, i: int, id: NodeId)
    requires
        0 <= i <= f.len(),
    ensures
        -1 <= fmt_index_of(f, i, id) < i,
        fmt_index_of(f, i, id) >= 0 ==> f[fmt_index_of(f, i, id)] is Entry && f[fmt_index_of(f, i, id)]->Entry_elem.id == id,
        forall|j: int| 0 <= j < i && (#[trigger] f[j]) is Entry && f[j]->Entry_elem.id == id ==> j <= fmt_index_of(f, i, id),
    decreases i,
{
    if i > 0 && !(f[i - 1] is Entry && f[i - 1]->Entry_elem.id == id) {
        lemma_fmt_index_of(f, i - 1, id);
    }
}

/// `fmt_last_where` finds an entry at or after `from`.
pub proof fn lemma_fmt_last_where(f: Seq<Fmt>, from: int, i: int, pred: spec_fn(Elem) -> bool)
    requires
        0 <= from,
        0 <= i <= f.len(),
    ensures
        -1 <= fmt_last_where(f, from, i, pred) < i,
        fmt_last_where(f, from, i, pred) >= 0 ==> from <= fmt_last_where(f, from, i, pred) && f[fmt_last_where(
            f,
            from,
            i,
            pred,
        )] is Entry && pred(f[fmt_last_where(f, from, i, pred)]->Entry_elem),
    decreases i - from,
{
    if i > from && !(f[i - 1] is Entry && pred(f[i - 1]->Entry_elem)) {
        lemma_fmt_last_where(f, from, i - 1, pred);
    }
}

/// `after_last_marker` is an index of the list.
pub proof fn lemma_after_last_marker(f: Seq<Fmt>, i: int)
    requires
        0 <= i,
    ensures
        0 <= after_last_marker(f, i) <= i,
    decreases i,
{
    if i > 0 && !(f[i - 1] is Marker) {
        lemma_after_last_marker(f, i - 1);
    }
}

/// The family's indices are indices of the list.
pub proof fn lemma_family_indices(f: Seq<Fmt>, from: int, i: int, e: Elem, t: TagTok)
    ensures
        forall|k: int| 0 <= k < family_indices(f, from, i, e, t).len() ==> from <= #[trigger] family_indices(f, from, i, e, t)[k] < i,
    decreases i - from,
{
    if i > from {
        lemma_family_indices(f, from, i - 1, e, t);
        let rest = family_indices(f, from, i - 1, e, t);
        if same_family(f[i - 1], e, t) {
            assert forall|k: int| 0 <= k < rest.push(i - 1).len() implies from <= #[trigger] rest.push(i - 1)[k] < i by {
                if k < rest.len() {
                    assert(rest.push(i - 1)[k] == rest[k]);
                }
            }
        }
    }
}

/// `last_index_where` finds the last match.
pub proof fn lemma_last_index_where_last(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= i <= open.len(),
    ensures
        forall|j: int| 0 <= j < i && f(#[trigger] open[j]) ==> j <= last_index_where(open, i, f),
    decreases i,
{
    lemma_last_index_where_range(open, i, f);
    if i > 0 && !f(open[i - 1]) {
        lemma_last_index_where_last(open, i - 1, f);
    }
}

/// `first_special_from` finds an index at or after `j`.
pub proof fn lemma_first_special_from(open: Seq<Elem>, j: int)
    ensures
        first_special_from(open, j) == -1 || (j <= first_special_from(open, j) < open.len()),
    decreases open.len() - j,
{
    if !(j < 0 || j >= open.len()) && !is_special(open[j]) {
        lemma_first_special_from(open, j + 1);
    }
}

/// The rewind step stays in the list.
pub proof fn lemma_reconstruct_rewind(p: Parser, i: int)
    ensures
        0 <= reconstruct_rewind(p, i),
        0 <= i ==> reconstruct_rewind(p, i) <= i,
    decreases i,
{
    if i > 0 {
        let e = p.formatting[i - 1];
        if !(e is Marker) && !fmt_on_stack(p, e) {
            lemma_reconstruct_rewind(p, i - 1);
        }
    }
}

// ---------------------------------------------------------------------
// Editing the list of active formatting elements

/// A node id at or past the end of the arena is not that of any entry.
pub proof fn lemma_fresh(p: Parser, id: NodeId)
    requires
        st(p),
        id >= p.doc.nodes.len(),
    ensures
        forall|j: int| 0 <= j < p.formatting.len() && (#[trigger] p.formatting[j]) is Entry ==> p.formatting[j]->Entry_elem.id != id,
        forall|j: int| 0 <= j < p.open.len() ==> (#[trigger] p.open[j]).id != id,
{
    lemma_st(p);
    assert forall|j: int| 0 <= j < p.formatting.len() && (#[trigger] p.formatting[j]) is Entry implies p.formatting[j]->Entry_elem.id
        != id by {
        assert(elem_in_doc(p.doc, p.formatting[j]->Entry_elem));
    }
    assert forall|j: int| 0 <= j < p.open.len() implies (#[trigger] p.open[j]).id != id by {
        assert(elem_in_doc(p.doc, p.open[j]));
    }
}

/// An entry that may join the list: an element of the document, not that
/// of any entry (other than the one at `skip`).
pub open spec fn fmt_entry_ok(p: Parser, x: Fmt, skip: int) -> bool {
    &&& x is Entry
    &&& elem_in_doc(p.doc, x->Entry_elem)
    &&& x->Entry_elem.ns == Namespace::Html
    &&& forall|j: int|
        0 <= j < p.formatting.len() && j != skip && (#[trigger] p.formatting[j]) is Entry ==> p.formatting[j]->Entry_elem.id
            != x->Entry_elem.id
}

/// [`kp`] for a step that keeps the document.
pub proof fn lemma_kp_same_doc(p: Parser, q: Parser)
    requires
        st(p),
        st(q),
        q.doc == p.doc,
        fx(p) ==> fx(q),
        od(p) ==> od(q),
        fh(p) ==> fh(q),
        q.redirect == p.redirect,
    ensures
        kp(p, q, 0),
{
    reveal(kp);
}

/// Replacing an entry of the list.
pub proof fn lemma_fmt_update(p: Parser, k: int, x: Fmt)
    requires
        st(p),
        0 <= k < p.formatting.len(),
        fmt_entry_ok(p, x, k),
    ensures
        st(Parser { formatting: p.formatting.update(k, x), ..p }),
        fx(p) && x->Entry_token.tag != Tag::Template ==> fx(Parser { formatting: p.formatting.update(k, x), ..p }),
        fh(p) ==> fh(Parser { formatting: p.formatting.update(k, x), ..p }),
{
    lemma_st(p);
    let q = Parser { formatting: p.formatting.update(k, x), ..p };
    assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_in_doc(
        q.doc,
        q.formatting[i]->Entry_elem,
    ) by {
        if i != k {
            assert(q.formatting[i] == p.formatting[i]);
        }
    }
    if fx(p) && x->Entry_token.tag != Tag::Template {
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            if i != k {
                assert(q.formatting[i] == p.formatting[i]);
            }
        }
        assert forall|i: int, j: int|
            0 <= i < q.formatting.len() && 0 <= j < q.formatting.len() && i != j && (#[trigger] q.formatting[i]) is Entry && (
            #[trigger] q.formatting[j]) is Entry implies q.formatting[i]->Entry_elem.id != q.formatting[j]->Entry_elem.id by {
            if i != k {
                assert(q.formatting[i] == p.formatting[i]);
            }
            if j != k {
                assert(q.formatting[j] == p.formatting[j]);
            }
        }
    }
    if fh(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.ns
            == Namespace::Html by {
            if i != k {
                assert(q.formatting[i] == p.formatting[i]);
            }
        }
    }
    lemma_st_lists(p, q);
    reveal(kp);
}

/// Inserting an entry into the list at `k` (the end if `k` is its length).
#[verifier::spinoff_prover]
pub proof fn lemma_fmt_insert(p: Parser, k: int, x: Fmt)
    requires
        st(p),
        0 <= k <= p.formatting.len(),
        fmt_entry_ok(p, x, -1),
    ensures
        st(Parser { formatting: p.formatting.insert(k, x), ..p }),
        fx(p) && x->Entry_token.tag != Tag::Template ==> fx(Parser { formatting: p.formatting.insert(k, x), ..p }),
        fh(p) ==> fh(Parser { formatting: p.formatting.insert(k, x), ..p }),
{
    lemma_st(p);
    let q = Parser { formatting: p.formatting.insert(k, x), ..p };
    assert forall|i: int| 0 <= i < q.formatting.len() && i != k implies #[trigger] q.formatting[i] == p.formatting[if i < k {
        i
    } else {
        i - 1
    }] by {}
    assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies elem_in_doc(
        q.doc,
        q.formatting[i]->Entry_elem,
    ) by {
        if i < k {
            assert(q.formatting[i] == p.formatting[i]);
        } else if i > k {
            assert(q.formatting[i] == p.formatting[i - 1]);
        }
    }
    if fx(p) && x->Entry_token.tag != Tag::Template {
        assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
            != Tag::Template by {
            if i < k {
                assert(q.formatting[i] == p.formatting[i]);
            } else if i > k {
                assert(q.formatting[i] == p.formatting[i - 1]);
            }
        }
        assert forall|i: int, j: int|
            0 <= i < q.formatting.len() && 0 <= j < q.formatting.len() && i != j && (#[trigger] q.formatting[i]) is Entry && (
            #[trigger] q.formatting[j]) is Entry implies q.formatting[i]->Entry_elem.id != q.formatting[j]->Entry_elem.id by {
            if i < k {
                assert(q.formatting[i] == p.formatting[i]);
            } else if i > k {
                assert(q.formatting[i] == p.formatting[i - 1]);
            }
            if j < k {
                assert(q.formatting[j] == p.formatting[j]);
            } else if j > k {
                assert(q.formatting[j] == p.formatting[j - 1]);
            }
        }
    }
    if fh(p) {
        assert forall|i: int| 0 <= i < q.formatting.len() && (#[trigger] q.formatting[i]) is Entry implies q.formatting[i]->Entry_elem.ns
            == Namespace::Html by {
            if i < k {
                assert(q.formatting[i] == p.formatting[i]);
            } else if i > k {
                assert(q.formatting[i] == p.formatting[i - 1]);
            }
        }
    }
    lemma_st_lists(p, q);
    reveal(kp);
}

/// Push onto the list of active formatting elements an element created
/// after every entry, for a token that is not `template`.
pub proof fn lemma_push_formatting(p: Parser, e: Elem, t: TagTok)
    requires
        st(p),
        !p.stopped ==> elem_in_doc(p.doc, e),
        !p.stopped ==> forall|j: int|
            0 <= j < p.formatting.len() && (#[trigger] p.formatting[j]) is Entry ==> p.formatting[j]->Entry_elem.id != e.id,
        t.tag != Tag::Template,
        e.ns == Namespace::Html,
    ensures
        kp(p, push_formatting(p, e, t), 0),
        push_formatting(p, e, t) == (Parser { formatting: push_formatting(p, e, t).formatting, ..p }),
{
    if p.stopped {
        lemma_kp_refl(p);
    } else {
        let f = p.formatting;
        let from = after_last_marker(f, f.len() as int);
        lemma_after_last_marker(f, f.len() as int);
        let fam = family_indices(f, from, f.len() as int, e, t);
        lemma_family_indices(f, from, f.len() as int, e, t);
        let x = Fmt::Entry { elem: e, token: t };
        if fam.len() >= 3 {
            assert(from <= fam[0] < f.len());
            lemma_fmt_remove(p, fam[0]);
            let p1 = Parser { formatting: f.remove(fam[0]), ..p };
            lemma_kp(p, p1, 0);
            assert forall|j: int| 0 <= j < p1.formatting.len() && (#[trigger] p1.formatting[j]) is Entry implies p1.formatting[j]->Entry_elem.id
                != e.id by {
                if j < fam[0] {
                    assert(p1.formatting[j] == f[j]);
                } else {
                    assert(p1.formatting[j] == f[j + 1]);
                }
            }
            assert(fmt_entry_ok(p1, x, -1));
            lemma_fmt_insert(p1, p1.formatting.len() as int, x);
            assert(p1.formatting.insert(p1.formatting.len() as int, x) =~= p1.formatting.push(x));
            lemma_kp_same_doc(p1, push_formatting(p, e, t));
            lemma_kp_trans(p, p1, push_formatting(p, e, t), 0, 0);
        } else {
            assert(fmt_entry_ok(p, x, -1));
            lemma_fmt_insert(p, f.len() as int, x);
            assert(f.insert(f.len() as int, x) =~= f.push(x));
            lemma_kp_same_doc(p, push_formatting(p, e, t));
        }
    }
}

/// Reconstruct from entry `i`: every new element is pushed and replaces its
/// entry; at most one new element per entry from `i` on, two (a template's
/// contents) without [`fx`].
pub proof fn lemma_reconstruct_create(p: Parser, i: int)
    requires
        st(p),
        0 <= i,
    ensures
        ({
            let q = reconstruct_create(p, i);
            let n = if i < p.formatting.len() {
                (p.formatting.len() - i) as nat
            } else {
                0
            };
            &&& kp(p, q, 2 * n)
            &&& fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + n
            &&& q.formatting.len() == p.formatting.len()
            &&& q.pending_table_text == p.pending_table_text
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.head == p.head
            &&& q.form == p.form
            &&& q.context == p.context
            &&& (p.stopped ==> q == p)
        }),
    decreases p.formatting.len() - i,
{
    hide(insert_html_element);
    if i < 0 || i >= p.formatting.len() || p.stopped || !(p.formatting[i] is Entry) {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * (if i < p.formatting.len() {
            (p.formatting.len() - i) as nat
        } else {
            0
        }));
    } else {
        let n = (p.formatting.len() - i) as nat;
        let token = p.formatting[i]->Entry_token;
        lemma_insert_html_element(p, token);
        let (p1, ne) = insert_html_element(p, token);
        lemma_kp(p, p1, elem_cost(Namespace::Html, token.tag));
        if fx(p) {
            assert(token.tag != Tag::Template);
        }
        let x = Fmt::Entry { elem: ne, token };
        let p2 = if p1.stopped {
            p1
        } else {
            Parser { formatting: p1.formatting.update(i, x), ..p1 }
        };
        if !p1.stopped {
            lemma_fresh(p, ne.id);
            assert(fmt_entry_ok(p1, x, i));
            lemma_fmt_update(p1, i, x);
            lemma_kp_same_doc(p1, p2);
        } else {
            lemma_kp_refl(p1);
        }
        lemma_kp_trans(p, p1, p2, elem_cost(Namespace::Html, token.tag), 0);
        lemma_kp(p, p2, elem_cost(Namespace::Html, token.tag));
        if i + 1 < p2.formatting.len() && p2.formatting.len() == p.formatting.len() {
            lemma_reconstruct_create(p2, i + 1);
            let q = reconstruct_create(p2, i + 1);
            lemma_kp_trans(p, p2, q, elem_cost(Namespace::Html, token.tag), 2 * ((p2.formatting.len() - (i + 1)) as nat));
            lemma_kp_weaken(p, q, elem_cost(Namespace::Html, token.tag) + 2 * ((p2.formatting.len() - (i + 1)) as nat), 2 * n);
        } else {
            lemma_kp_weaken(p, p2, elem_cost(Namespace::Html, token.tag), 2 * n);
        }
    }
}

/// Reconstruct the active formatting elements: one new element per entry,
/// two without [`fx`].
pub proof fn lemma_reconstruct_formatting(p: Parser)
    requires
        st(p),
    ensures
        ({
            let q = reconstruct_formatting(p);
            &&& kp(p, q, 2 * p.formatting.len())
            &&& fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + p.formatting.len()
            &&& q.formatting.len() == p.formatting.len()
            &&& q.pending_table_text == p.pending_table_text
            &&& q.template_modes == p.template_modes
            &&& q.mode == p.mode
            &&& q.original_mode == p.original_mode
            &&& q.head == p.head
            &&& q.form == p.form
            &&& q.context == p.context
            &&& (p.stopped ==> q == p)
        }),
{
    hide(reconstruct_create);
    let n = p.formatting.len();
    if n == 0 || p.formatting[n - 1] is Marker || fmt_on_stack(p, p.formatting[n - 1]) {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * n);
    } else {
        let i = reconstruct_rewind(p, n - 1);
        lemma_reconstruct_rewind(p, n - 1);
        lemma_reconstruct_create(p, i);
        lemma_kp_weaken(p, reconstruct_create(p, i), 2 * ((n - i) as nat), 2 * n);
    }
}

/// Add the token's attributes the element lacks.
pub proof fn lemma_add_missing_attributes(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int)
    requires
        st(p),
        dom::valid(p.doc, el),
        p.doc.nodes[el as int].kind is Element,
    ensures
        kp(p, add_missing_attributes(p, el, attrs, i), 0),
        add_missing_attributes(p, el, attrs, i) == (Parser { doc: add_missing_attributes(p, el, attrs, i).doc, ..p }),
    decreases attrs.len() - i,
{
    if i < 0 || i >= attrs.len() {
        lemma_kp_refl(p);
    } else {
        let a = attrs[i];
        let q = if !p.stopped && !element_has_attribute_named(p.doc, el, a.local_name) {
            Parser { doc: dom::append_attribute(p.doc, el, a), ..p }
        } else {
            p
        };
        if !p.stopped && !element_has_attribute_named(p.doc, el, a.local_name) {
            lemma_append_attribute(p, el, a);
            lemma_kp(p, q, 0);
        } else {
            lemma_kp_refl(p);
        }
        lemma_add_missing_attributes(q, el, attrs, i + 1);
        lemma_kp_trans(p, q, add_missing_attributes(q, el, attrs, i + 1), 0, 0);
    }
}

/// Move the children of a node (step 4.17 of the adoption agency).
pub proof fn lemma_dom_reparent_children(p: Parser, from: NodeId, to: NodeId)
    requires
        st(p),
    ensures
        kp(p, dom_reparent_children(p, from, to), 0),
        dom_reparent_children(p, from, to) == (Parser { doc: dom_reparent_children(p, from, to).doc, ..p }),
{
    lemma_st(p);
    let d = p.doc;
    if p.stopped || !(dom::valid(d, from) && dom::valid(d, to) && from != to && dom::may_have_children(d.nodes[from as int].kind)
        && dom::may_have_children(d.nodes[to as int].kind) && !dom::is_inclusive_ancestor(d, from, to)) {
        lemma_kp_refl(p);
    } else {
        let d1 = dom::reparent_children(d, from, to);
        assert(dom::reparent_children_requires(d, from, to));
        clazel_dom::lemmas::theorem_reparent_children_wf(d, from, to);
        clazel_dom::lemmas::theorem_ids_stable(d);
        assert(clazel_dom::lemmas::ids_stable(d, d1, 0, -1));
        assert forall|i: int| 0 <= i < d.nodes.len() implies kind_ok(d.nodes[i].kind, #[trigger] d1.nodes[i].kind) by {
            assert(d1.nodes[i].kind == d.nodes[i].kind);
        }
        lemma_st_doc(p, d1);
    }
}

/// Replace an entry of the stack with an element of the document.
pub proof fn lemma_open_update(p: Parser, i: int, e: Elem)
    requires
        st(p),
        0 <= i < p.open.len(),
        elem_in_doc(p.doc, e),
        not_on(p.open, e.id),
    ensures
        kp(p, Parser { open: p.open.update(i, e), ..p }, 0),
{
    lemma_st(p);
    let q = Parser { open: p.open.update(i, e), ..p };
    assert forall|j: int| 0 <= j < q.open.len() implies elem_in_doc(q.doc, #[trigger] q.open[j]) by {
        if j != i {
            assert(q.open[j] == p.open[j]);
        }
    }
    if od(p) && !p.stopped {
        lemma_distinct_update(p.open, i, e);
    }
    lemma_st_lists(p, q);
}

/// Remove an entry of the stack and insert an element of the document.
#[verifier::spinoff_prover]
pub proof fn lemma_open_remove_insert(p: Parser, j: int, k: int, e: Elem)
    requires
        st(p),
        0 <= j < p.open.len(),
        0 <= k <= p.open.len() - 1,
        elem_in_doc(p.doc, e),
        not_on(p.open, e.id),
    ensures
        kp(p, Parser { open: p.open.remove(j).insert(k, e), ..p }, 0),
{
    lemma_st(p);
    let o1 = p.open.remove(j);
    let q = Parser { open: o1.insert(k, e), ..p };
    assert forall|m: int| 0 <= m < o1.len() implies elem_in_doc(p.doc, #[trigger] o1[m]) by {
        if m < j {
            assert(o1[m] == p.open[m]);
        } else {
            assert(o1[m] == p.open[m + 1]);
        }
    }
    assert forall|m: int| 0 <= m < q.open.len() implies elem_in_doc(q.doc, #[trigger] q.open[m]) by {
        if m < k {
            assert(q.open[m] == o1[m]);
        } else if m > k {
            assert(q.open[m] == o1[m - 1]);
        }
    }
    if od(p) && !p.stopped {
        lemma_distinct_remove_insert(p.open, j, k, e);
    }
    lemma_st_lists(p, q);
}

/// Remove entry `fi` of the list and insert `x` at `k`.
pub proof fn lemma_fmt_remove_insert(p: Parser, fi: int, k: int, x: Fmt)
    requires
        st(p),
        0 <= fi < p.formatting.len(),
        0 <= k <= p.formatting.len() - 1,
        fmt_entry_ok(p, x, fi),
    ensures
        st(Parser { formatting: p.formatting.remove(fi).insert(k, x), ..p }),
        fx(p) && x->Entry_token.tag != Tag::Template ==> fx(Parser { formatting: p.formatting.remove(fi).insert(k, x), ..p }),
        fh(p) ==> fh(Parser { formatting: p.formatting.remove(fi).insert(k, x), ..p }),
{
    lemma_fmt_remove(p, fi);
    let pa = Parser { formatting: p.formatting.remove(fi), ..p };
    lemma_kp(p, pa, 0);
    assert forall|j: int| 0 <= j < pa.formatting.len() && (#[trigger] pa.formatting[j]) is Entry implies pa.formatting[j]->Entry_elem.id
        != x->Entry_elem.id by {
        if j < fi {
            assert(pa.formatting[j] == p.formatting[j]);
        } else {
            assert(pa.formatting[j] == p.formatting[j + 1]);
        }
    }
    assert(fmt_entry_ok(pa, x, -1));
    lemma_fmt_insert(pa, k, x);
}

// ---------------------------------------------------------------------
// The adoption agency algorithm (§13.2.6.4.7, "in body")

/// formattingElement has an entry in the list and is on the stack.
pub open spec fn fe_in(p: Parser, fe: Elem) -> bool {
    &&& fmt_index_of(p.formatting, p.formatting.len() as int, fe.id) >= 0
    &&& exists|j: int| 0 <= j < p.open.len() && (#[trigger] p.open[j]).id == fe.id
}

/// The most new nodes the inner loop makes from innerLoopCounter `c` on:
/// one for each round with the counter at most 3.
pub open spec fn inner_bound(c: nat) -> nat {
    if c >= 3 {
        0
    } else {
        (3 - c) as nat
    }
}

/// Step 4.16.4: an entry is dropped from the list; with [`fx`], once the
/// counter is above 3 node has no entry left.
pub proof fn lemma_inner_drop(p: Parser, node_id: NodeId, c: nat, fe: Elem)
    requires
        st(p),
        node_id != fe.id,
        fmt_index_of(p.formatting, p.formatting.len() as int, fe.id) >= 0,
    ensures
        ({
            let p1 = crate::exec::modes::adoption::inner_drop(p, node_id, c);
            &&& kp(p, p1, 0)
            &&& p1 == Parser { formatting: p1.formatting, ..p }
            &&& fmt_index_of(p1.formatting, p1.formatting.len() as int, fe.id) >= 0
            &&& fx(p) && c > 3 ==> !in_formatting(p1, node_id)
            &&& p1.formatting.len() <= p.formatting.len()
        }),
{
    reveal(crate::exec::modes::adoption::inner_drop);
    let f = p.formatting;
    if c > 3 && in_formatting(p, node_id) {
        let k = fmt_index_of(f, f.len() as int, node_id);
        lemma_fmt_index_of(f, f.len() as int, node_id);
        lemma_fmt_remove(p, k);
        crate::reachable::adoption::lemma_in_formatting_remove(f, k, fe.id);
        let g = f.remove(k);
        if fx(p) && in_formatting(Parser { formatting: g, ..p }, node_id) {
            let j = fmt_index_of(g, g.len() as int, node_id);
            lemma_fmt_index_of(g, g.len() as int, node_id);
            if j < k {
                assert(g[j] == f[j]);
            } else {
                assert(g[j] == f[j + 1]);
            }
            assert(false);
        }
    } else {
        lemma_kp_refl(p);
    }
}

/// Steps 4.16.6 to 4.16.11: one new element, which replaces node on the
/// stack and in the list.
pub proof fn lemma_inner_replace(p1: Parser, ca: Elem, i: int, node_id: NodeId, last: Elem, bm: Bookmark, fe: Elem)
    requires
        st(p1),
        !p1.stopped ==> {
            &&& in_formatting(p1, node_id)
            &&& node_id != fe.id
            &&& 0 <= i < p1.open.len()
            &&& p1.open[i].id == node_id
            &&& fe_in(p1, fe)
        },
    ensures
        ({
            let r = crate::exec::modes::adoption::inner_replace(p1, ca, i, node_id, last, bm);
            &&& kpu(p1, r.0)
            &&& fx(p1) ==> r.0.doc.nodes.len() <= p1.doc.nodes.len() + 1
            &&& !r.0.stopped ==> fe_in(r.0, fe) && r.0.open.len() == p1.open.len()
            &&& r.0.formatting.len() == p1.formatting.len()
        }),
{
    hide(create_element_for_token);
    hide(dom_insert);
    reveal(crate::exec::modes::adoption::inner_replace);
    let f = p1.formatting;
    let k = fmt_index_of(f, f.len() as int, node_id);
    let token = f[k]->Entry_token;
    lemma_create_element_for_token(p1, token, Namespace::Html, ca.id);
    let (p2, ne) = create_element_for_token(p1, token, Namespace::Html, ca.id);
    lemma_kp(p1, p2, elem_cost(Namespace::Html, token.tag));
    lemma_kp_kpu(p1, p2, elem_cost(Namespace::Html, token.tag));
    if p1.stopped {
        return;
    }
    lemma_fmt_index_of(f, f.len() as int, node_id);
    if fx(p1) {
        assert(token.tag != Tag::Template);
    }
    if p2.stopped {
        return;
    }
    let x = Fmt::Entry { elem: ne, token };
    lemma_fresh(p1, ne.id);
    assert(fmt_entry_ok(p2, x, k));
    lemma_fmt_update(p2, k, x);
    let pa = Parser { formatting: f.update(k, x), ..p2 };
    lemma_kp_same_doc(p2, pa);
    lemma_open_update(pa, i, ne);
    let p3 = Parser { formatting: f.update(k, x), open: p2.open.update(i, ne), ..p2 };
    assert(p3 == Parser { open: pa.open.update(i, ne), ..pa });
    lemma_kp_trans(p2, pa, p3, 0, 0);
    lemma_kp(pa, p3, 0);
    lemma_dom_insert(p3, last.id, ne.id, None);
    let p4 = dom_insert(p3, last.id, ne.id, None);
    lemma_kp_trans(p2, p3, p4, 0, 0);
    lemma_kp_trans(p1, p2, p4, elem_cost(Namespace::Html, token.tag), 0);
    lemma_kp(p1, p4, elem_cost(Namespace::Html, token.tag));
    lemma_kp_kpu(p1, p4, elem_cost(Namespace::Html, token.tag));
    crate::reachable::adoption::lemma_in_formatting_update(f, k, x, fe.id);
    let j = choose|j: int| 0 <= j < p1.open.len() && (#[trigger] p1.open[j]).id == fe.id;
    assert(p4.open[j] == p1.open[j]);
}

/// Step 4.16, the inner loop: at most [`inner_bound`] new nodes with
/// [`fx`].
pub proof fn lemma_ai(p: Parser, fe: Elem, ca: Elem, node_idx: int, last: Elem, counter: nat, bm: Bookmark)
    requires
        st(p),
        0 <= node_idx <= p.open.len(),
        !p.stopped ==> fe_in(p, fe),
    ensures
        ({
            let q = crate::exec::modes::adoption::ai(p, fe, ca, node_idx, last, counter, bm).0;
            &&& kpu(p, q)
            &&& fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + inner_bound(counter)
            &&& !q.stopped ==> fe_in(q, fe)
            &&& q.formatting.len() <= p.formatting.len()
        }),
    decreases node_idx,
{
    use crate::exec::modes::adoption::{ai, inner_drop, inner_replace};
    if p.stopped || node_idx <= 0 {
        reveal(ai);
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
        return;
    }
    crate::exec::modes::adoption::lemma_ai_unfold(p, fe, ca, node_idx, last, counter, bm);
    let c = counter + 1;
    let i = node_idx - 1;
    let node_id = p.open[i].id;
    if node_id == fe.id {
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
        return;
    }
    lemma_inner_drop(p, node_id, c, fe);
    let p1 = inner_drop(p, node_id, c);
    lemma_kp(p, p1, 0);
    lemma_kp_kpu(p, p1, 0);
    let j = choose|j: int| 0 <= j < p.open.len() && (#[trigger] p.open[j]).id == fe.id;
    if !in_formatting(p1, node_id) {
        lemma_remove_open_at(p1, i);
        let p2 = remove_open_at(p1, i);
        lemma_kp(p1, p2, 0);
        lemma_kp_kpu(p1, p2, 0);
        lemma_kpu_trans(p, p1, p2);
        if j < i {
            assert(p2.open[j] == p.open[j]);
        } else {
            assert(p2.open[j - 1] == p.open[j]);
        }
        assert(fe_in(p2, fe));
        lemma_ai(p2, fe, ca, i, last, c, bm);
        lemma_kpu_trans(p, p2, ai(p2, fe, ca, i, last, c, bm).0);
    } else {
        lemma_inner_replace(p1, ca, i, node_id, last, bm, fe);
        let r = inner_replace(p1, ca, i, node_id, last, bm);
        lemma_kpu_trans(p, p1, r.0);
        lemma_kpu(p1, r.0);
        if !r.0.stopped {
            lemma_ai(r.0, fe, ca, i, r.1, c, r.2);
            lemma_kpu_trans(p, r.0, ai(r.0, fe, ca, i, r.1, c, r.2).0);
        }
    }
}

/// Steps 4.17 to 4.21: lastNode is moved.
pub proof fn lemma_place_last(p: Parser, ca: Elem, last_id: NodeId)
    requires
        st(p),
    ensures
        kp(p, crate::exec::modes::adoption::place_last(p, ca, last_id), 0),
        crate::exec::modes::adoption::place_last(p, ca, last_id) == (Parser {
            doc: crate::exec::modes::adoption::place_last(p, ca, last_id).doc,
            ..p
        }),
{
    hide(dom_insert);
    hide(dom_remove);
    reveal(crate::exec::modes::adoption::place_last);
    let l = adjusted_location(p, Some(appropriate_place(p, Some(ca))));
    lemma_dom_remove(p, last_id);
    let p1 = dom_remove(p, last_id);
    lemma_kp(p, p1, 0);
    lemma_dom_insert(p1, last_id, l.parent, l.child);
    lemma_kp_trans(p, p1, dom_insert(p1, last_id, l.parent, l.child), 0, 0);
}

/// Steps 4.22 to 4.24: one new element replaces formattingElement in the
/// list and goes on the stack after furthestBlock.
pub proof fn lemma_finish_mid(p2: Parser, fe: Elem, fb_id: NodeId, bm: Bookmark)
    requires
        st(p2),
        !p2.stopped ==> fe_in(p2, fe),
    ensures
        ({
            let r = crate::exec::modes::adoption::finish_mid(p2, fe, fb_id, bm);
            &&& kpu(p2, r.0)
            &&& fx(p2) ==> r.0.doc.nodes.len() <= p2.doc.nodes.len() + 1
            &&& r.0.formatting.len() == p2.formatting.len()
        }),
{
    hide(create_element_for_token);
    reveal(crate::exec::modes::adoption::finish_mid);
    let f = p2.formatting;
    let fi = fmt_index_of(f, f.len() as int, fe.id);
    let token = f[fi]->Entry_token;
    lemma_create_element_for_token(p2, token, Namespace::Html, fb_id);
    let (p3, ne) = create_element_for_token(p2, token, Namespace::Html, fb_id);
    lemma_kp(p2, p3, elem_cost(Namespace::Html, token.tag));
    lemma_kp_kpu(p2, p3, elem_cost(Namespace::Html, token.tag));
    if p2.stopped {
        return;
    }
    lemma_fmt_index_of(f, f.len() as int, fe.id);
    if fx(p2) {
        assert(token.tag != Tag::Template);
    }
    if p3.stopped {
        return;
    }
    let entry = Fmt::Entry { elem: ne, token };
    let f1 = f.remove(fi);
    let k = match bm {
        Bookmark::FormattingElement => fi,
        Bookmark::After(b) => fmt_index_of(f1, f1.len() as int, b) + 1,
    };
    if let Bookmark::After(b) = bm {
        lemma_fmt_index_of(f1, f1.len() as int, b);
    }
    lemma_fresh(p2, ne.id);
    assert(fmt_entry_ok(p3, entry, fi));
    lemma_fmt_remove_insert(p3, fi, k, entry);
    let f2 = f1.insert(k, entry);
    let pa = Parser { formatting: f2, ..p3 };
    lemma_kp_same_doc(p3, pa);
    let jw = choose|j: int| 0 <= j < p2.open.len() && (#[trigger] p2.open[j]).id == fe.id;
    let pred = |e: Elem| e.id == fe.id;
    lemma_last_index_where_last(p3.open, p3.open.len() as int, pred);
    lemma_last_index_where_range(p3.open, p3.open.len() as int, pred);
    assert(pred(p3.open[jw]));
    let j = open_index_of(p3, fe.id);
    let o1 = p3.open.remove(j);
    let pb = |e: Elem| e.id == fb_id;
    lemma_last_index_where_range(o1, o1.len() as int, pb);
    let k2 = last_index_where(o1, o1.len() as int, pb) + 1;
    lemma_open_remove_insert(pa, j, k2, ne);
    let q = Parser { formatting: f2, open: o1.insert(k2, ne), ..p3 };
    assert(q == Parser { open: pa.open.remove(j).insert(k2, ne), ..pa });
    lemma_kp_trans(p3, pa, q, 0, 0);
    lemma_kp_trans(p2, p3, q, elem_cost(Namespace::Html, token.tag), 0);
    lemma_kp(p2, q, elem_cost(Namespace::Html, token.tag));
    lemma_kp_kpu(p2, q, elem_cost(Namespace::Html, token.tag));
}

/// Steps 4.27 to 4.29: children move to the new element, which is inserted.
pub proof fn lemma_finish_end(p4: Parser, fb_id: NodeId, ne_id: NodeId)
    requires
        st(p4),
    ensures
        kp(p4, crate::exec::modes::adoption::finish_end(p4, fb_id, ne_id), 0),
        crate::exec::modes::adoption::finish_end(p4, fb_id, ne_id).formatting == p4.formatting,
{
    hide(dom_insert);
    hide(dom_reparent_children);
    reveal(crate::exec::modes::adoption::finish_end);
    lemma_dom_reparent_children(p4, fb_id, ne_id);
    let p5 = dom_reparent_children(p4, fb_id, ne_id);
    lemma_kp(p4, p5, 0);
    let l2 = adjusted_location(p5, Some(Location { parent: fb_id, child: None }));
    lemma_dom_insert(p5, ne_id, l2.parent, l2.child);
    lemma_kp_trans(p4, p5, dom_insert(p5, ne_id, l2.parent, l2.child), 0, 0);
}

/// Steps 4.17 to 4.29 of one outer round: one new node with [`fx`].
pub proof fn lemma_af(p: Parser, fe: Elem, fb: Elem, ca: Elem, last: Elem, bm: Bookmark)
    requires
        st(p),
        !p.stopped ==> fe_in(p, fe),
    ensures
        ({
            let q = crate::exec::modes::adoption::af(p, fe, fb, ca, last, bm);
            &&& kpu(p, q)
            &&& fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + 1
            &&& q.formatting.len() <= p.formatting.len()
        }),
{
    use crate::exec::modes::adoption::{af, place_last, finish_mid, finish_end};
    crate::exec::modes::adoption::lemma_af_unfold(p, fe, fb, ca, last, bm);
    if p.stopped {
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
        return;
    }
    lemma_place_last(p, ca, last.id);
    let p2 = place_last(p, ca, last.id);
    lemma_kp(p, p2, 0);
    lemma_kp_kpu(p, p2, 0);
    lemma_finish_mid(p2, fe, fb.id, bm);
    let r = finish_mid(p2, fe, fb.id, bm);
    lemma_kpu_trans(p, p2, r.0);
    lemma_kpu(p2, r.0);
    if !r.0.stopped {
        lemma_finish_end(r.0, fb.id, r.1.id);
        lemma_kp_kpu(r.0, finish_end(r.0, fb.id, r.1.id), 0);
        lemma_kp(r.0, finish_end(r.0, fb.id, r.1.id), 0);
        lemma_kpu_trans(p, r.0, finish_end(r.0, fb.id, r.1.id));
    }
}

/// The parser of an adoption agency outcome.
pub open spec fn aa_q(o: AdoptionOutcome) -> Parser {
    match o {
        AdoptionOutcome::Done(q) => q,
        AdoptionOutcome::AnyOtherEndTag(q) => q,
    }
}

/// Step 4, the outer loop from outerLoopCounter `counter`: four new nodes
/// a round with [`fx`] (three in the inner loop, one in step 4.22).
pub proof fn lemma_ao(p: Parser, tt: TagTok, counter: nat)
    requires
        st(p),
        counter <= 8,
    ensures
        kpu(p, aa_q(crate::exec::modes::adoption::ao(p, tt, counter))),
        fx(p) ==> aa_q(crate::exec::modes::adoption::ao(p, tt, counter)).doc.nodes.len() <= p.doc.nodes.len() + 4 * (8
            - counter),
        aa_q(crate::exec::modes::adoption::ao(p, tt, counter)).formatting.len() <= p.formatting.len(),
    decreases 8 - counter,
{
    use crate::exec::modes::adoption::{ao, ai, af};
    if p.stopped || counter >= 8 {
        reveal(ao);
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
        return;
    }
    crate::exec::modes::adoption::lemma_ao_unfold(p, tt, counter);
    let f = p.formatting;
    let from = after_last_marker(f, f.len() as int);
    lemma_after_last_marker(f, f.len() as int);
    let fi = fmt_last_where(f, from, f.len() as int, |e: Elem| e.name == tt.name);
    lemma_fmt_last_where(f, from, f.len() as int, |e: Elem| e.name == tt.name);
    if fi < 0 {
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
        return;
    }
    let fe = f[fi]->Entry_elem;
    let fe_idx = open_index_of(p, fe.id);
    lemma_last_index_where_range(p.open, p.open.len() as int, |e: Elem| e.id == fe.id);
    if fe_idx < 0 {
        lemma_fmt_remove(p, fi);
        lemma_kp_kpu(p, Parser { formatting: f.remove(fi), ..p }, 0);
        lemma_kp(p, Parser { formatting: f.remove(fi), ..p }, 0);
        return;
    }
    if !has_node_in_scope(p, fe.id, Scope::Default) {
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
        return;
    }
    let fb_idx = first_special_from(p.open, fe_idx + 1);
    lemma_first_special_from(p.open, fe_idx + 1);
    if fb_idx < 0 {
        let q = pop_until_node_popped(p, fe.id);
        lemma_pop_until_node_popped(p, fe.id);
        lemma_pops_kp(p, q);
        lemma_kp(p, q, 0);
        lemma_fmt_remove(q, fi);
        lemma_kp_trans(p, q, Parser { formatting: q.formatting.remove(fi), ..q }, 0, 0);
        lemma_kp_kpu(p, Parser { formatting: q.formatting.remove(fi), ..q }, 0);
        lemma_kp(p, Parser { formatting: q.formatting.remove(fi), ..q }, 0);
        return;
    }
    let fb = p.open[fb_idx];
    let ca = p.open[fe_idx - 1];
    crate::exec::modes::adoption::lemma_fmt_index_of_found(f, f.len() as int, fe.id, fi);
    assert(p.open[fe_idx].id == fe.id);
    assert(fe_in(p, fe));
    lemma_ai(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
    let r = ai(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
    lemma_kpu(p, r.0);
    lemma_af(r.0, fe, fb, ca, r.1, r.2);
    let p1 = af(r.0, fe, fb, ca, r.1, r.2);
    lemma_kpu_trans(p, r.0, p1);
    lemma_kpu(r.0, p1);
    lemma_ao(p1, tt, counter + 1);
    lemma_kpu_trans(p, p1, aa_q(ao(p1, tt, counter + 1)));
}

/// The adoption agency algorithm: at most 32 new nodes with [`fx`] (eight
/// outer rounds of four).
pub proof fn lemma_adoption_agency(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpu(p, aa_q(adoption_agency(p, tt))),
        fx(p) ==> aa_q(adoption_agency(p, tt)).doc.nodes.len() <= p.doc.nodes.len() + 32,
        aa_q(adoption_agency(p, tt)).formatting.len() <= p.formatting.len(),
{
    crate::exec::modes::adoption::lemma_aa_start(p, tt);
    if p.open.len() > 0 && current_node(p).ns == Namespace::Html && current_node(p).name == tt.name && !in_formatting(
        p,
        current_node(p).id,
    ) {
        lemma_pop(p);
        lemma_pops_kp(p, pop(p));
        lemma_kp_kpu(p, pop(p), 0);
        lemma_kp(p, pop(p), 0);
    } else {
        lemma_ao(p, tt, 0);
    }
}

/// "Any other end tag", the loop from index `i`.
pub proof fn lemma_any_other_end_tag_loop(p: Parser, tt: TagTok, i: int)
    ensures
        pops(p, any_other_end_tag_loop(p, tt, i)),
    decreases i + 1,
{
    if i >= 0 {
        let node = p.open[i];
        if is_html_named(node, tt.name) {
            let q = generate_implied_end_tags(p, Some(tt.tag));
            lemma_generate_implied_end_tags(p, Some(tt.tag));
            lemma_pop_until_node_popped(q, node.id);
            lemma_pops_trans(p, q, pop_until_node_popped(q, node.id));
        } else if !is_special(node) {
            lemma_any_other_end_tag_loop(p, tt, i - 1);
        }
    }
}

/// The adoption agency algorithm as "in body" runs it.
pub proof fn lemma_in_body_adoption(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpu(p, in_body_adoption(p, tt)),
        fx(p) ==> in_body_adoption(p, tt).doc.nodes.len() <= p.doc.nodes.len() + 32,
        in_body_adoption(p, tt).formatting.len() <= p.formatting.len(),
{
    hide(adoption_agency);
    hide(any_other_end_tag_loop);
    lemma_adoption_agency(p, tt);
    let o = adoption_agency(p, tt);
    lemma_kpu(p, aa_q(o));
    if let AdoptionOutcome::AnyOtherEndTag(q) = o {
        lemma_any_other_end_tag_loop(q, tt, q.open.len() - 1);
        lemma_pops_kp(q, in_body_any_other_end_tag(q, tt));
        lemma_kp_kpu(q, in_body_any_other_end_tag(q, tt), 0);
        lemma_kp(q, in_body_any_other_end_tag(q, tt), 0);
        lemma_kpu_trans(p, q, in_body_any_other_end_tag(q, tt));
    }
}

// ---------------------------------------------------------------------
// Rule applications

/// The nodes "in table text"'s anything else may create for its pending
/// character tokens (in the mode, for a token other than a character):
/// each goes through the "in body" rules, which reconstruct the active
/// formatting elements (one element per entry) and insert the character
/// (one `Text` node).
pub open spec fn flush(p: Parser, t: Tok) -> nat {
    if p.mode == Mode::InTableText && !(t is Char) {
        p.pending_table_text.len() * (p.formatting.len() + 1)
    } else {
        0
    }
}

/// The most nodes a rule application that handles the token (`Done`)
/// creates, besides two per entry of the list of active formatting
/// elements: the adoption agency's 32 and one element ("in body"'s `nobr`
/// start tag reconstructs twice around the adoption agency).
pub open spec fn done_max() -> nat {
    33
}

/// How a reprocessing edge from (`r`, `p`, `t`) to (`r2`, `q`, `t2`) may
/// create nodes: none (and the list does not grow and [`flush`] does not
/// increase); one implicit element, as the growth budget drops; or the
/// pending characters ("in table text"'s anything else).
pub open spec fn edge_nodes(r: Rules, p: Parser, t: Tok, r2: Rules, q: Parser, t2: Tok) -> bool {
    let (np, nq) = (p.doc.nodes.len(), q.doc.nodes.len());
    ||| (nq == np && q.formatting.len() <= p.formatting.len() && flush(q, t2) <= flush(p, t))
    ||| (nq <= np + 1 && crate::termination::growth(r2, t2) < crate::termination::growth(r, t) && q.template_modes.len()
        == p.template_modes.len() && crate::termination::img(t2) == crate::termination::img(t) && q.formatting.len()
        == p.formatting.len() && flush(q, t2) == 0)
    ||| (nq <= np + flush(p, t) && flush(q, t2) == 0 && q.formatting.len() == p.formatting.len() && crate::termination::growth(
        r2,
        t2,
    ) <= crate::termination::growth(r, t) && q.template_modes.len() == p.template_modes.len() && crate::termination::img(t2)
        == crate::termination::img(t))
}

/// What every rule application satisfies: the new state keeps [`st`]
/// ([`kpu`]); with [`fx`], handling the token creates at most
/// [`done_max`] nodes and two per entry of the list, and a reprocessing
/// edge satisfies [`edge_nodes`].
pub open spec fn app_ok(r: Rules, p: Parser, t: Tok, o: Outcome) -> bool {
    match o {
        Outcome::Done(q) => kpu(p, q) && (fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + done_max() + 2
            * p.formatting.len()),
        Outcome::Reprocess(q, t2) => kpu(p, q) && (fx(p) ==> edge_nodes(r, p, t, Rules::Html(q.mode), q, t2)),
        Outcome::Using(m, q, t2) => kpu(p, q) && (fx(p) ==> edge_nodes(r, p, t, Rules::Html(m), q, t2)),
    }
}

/// [`app_ok`] for an outcome whose edges create no node: it holds for
/// every set of rules.
pub open spec fn app_quiet(p: Parser, t: Tok, o: Outcome) -> bool {
    match o {
        Outcome::Done(q) => kpu(p, q) && (fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + done_max() + 2
            * p.formatting.len()),
        Outcome::Reprocess(q, t2) => kp(p, q, 0) && q.formatting.len() <= p.formatting.len() && flush(q, t2) <= flush(p, t),
        Outcome::Using(m, q, t2) => kp(p, q, 0) && q.formatting.len() <= p.formatting.len() && flush(q, t2) <= flush(p, t),
    }
}

/// [`app_quiet`] implies [`app_ok`].
pub proof fn lemma_quiet_ok(r: Rules, p: Parser, t: Tok, o: Outcome)
    requires
        app_quiet(p, t, o),
    ensures
        app_ok(r, p, t, o),
{
    match o {
        Outcome::Done(q) => {},
        Outcome::Reprocess(q, t2) => {
            lemma_kp(p, q, 0);
            lemma_kp_kpu(p, q, 0);
        },
        Outcome::Using(m, q, t2) => {
            lemma_kp(p, q, 0);
            lemma_kp_kpu(p, q, 0);
        },
    }
}

/// A handled token with a [`kp`] bound.
pub proof fn lemma_done(p: Parser, t: Tok, q: Parser, c: nat)
    requires
        kp(p, q, c),
        c <= done_max() + 2 * p.formatting.len(),
    ensures
        app_quiet(p, t, Outcome::Done(q)),
{
    lemma_kp(p, q, c);
    lemma_kp_kpu(p, q, c);
}

/// A token handled with no change to what [`st`] reads.
pub proof fn lemma_done_same(p: Parser, t: Tok, q: Parser)
    requires
        st(p),
        q.doc == p.doc,
        q.open == p.open,
        q.formatting == p.formatting,
        q.head == p.head,
        q.form == p.form,
        q.context == p.context,
        q.redirect == p.redirect,
        q.stopped == p.stopped,
    ensures
        app_quiet(p, t, Outcome::Done(q)),
{
    lemma_kp_refl(p);
    lemma_kp_fields(p, p, q, 0);
    lemma_done(p, t, q, 0);
}

/// "Using the rules for" with the parser unchanged.
pub proof fn lemma_using_same(p: Parser, t: Tok, m: Mode)
    requires
        st(p),
    ensures
        app_quiet(p, t, Outcome::Using(m, p, t)),
{
    lemma_kp_refl(p);
}

/// An edge to a parser of [`kp`] with no new node.
pub proof fn lemma_quiet_edge(p: Parser, t: Tok, q: Parser, t2: Tok)
    requires
        kp(p, q, 0),
        q.formatting.len() <= p.formatting.len(),
        flush(q, t2) <= flush(p, t),
    ensures
        app_quiet(p, t, Outcome::Reprocess(q, t2)),
{
}

/// An edge that creates one implicit element as the growth budget drops.
pub proof fn lemma_growth_edge(r: Rules, p: Parser, t: Tok, q: Parser)
    requires
        kp(p, q, 1),
        crate::termination::growth(Rules::Html(q.mode), t) < crate::termination::growth(r, t),
        q.template_modes.len() == p.template_modes.len(),
        q.formatting.len() == p.formatting.len(),
        q.mode != Mode::InTableText,
    ensures
        app_ok(r, p, t, Outcome::Reprocess(q, t)),
{
    lemma_kp(p, q, 1);
    lemma_kp_kpu(p, q, 1);
}

// ---------------------------------------------------------------------
// The early modes

/// §13.2.6.4.1 "initial".
pub proof fn lemma_mode_initial(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_initial(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(create);
    hide(dom_insert);
    hide(set_document_mode);
    hide(initial_doctype);
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_done_same(p, t, p);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, Some(document_location()));
        lemma_done(p, t, insert_comment(p, t->Comment_0, Some(document_location())), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location()));
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())), 1);
    } else if t is Doctype {
        lemma_initial_doctype(p, t->Doctype_name, t->Doctype_public_id, t->Doctype_system_id, t->Doctype_force_quirks);
        lemma_done(p, t, initial_doctype(p, t->Doctype_name, t->Doctype_public_id, t->Doctype_system_id, t->Doctype_force_quirks), 1);
    } else {
        lemma_set_document_mode(p, DocumentMode::Quirks);
        let q = set_document_mode(p, DocumentMode::Quirks);
        lemma_kp_fields(p, q, Parser { mode: Mode::BeforeHtml, ..q }, 0);
    }
}

/// The "initial" mode's DOCTYPE token: one `DocumentType` node.
pub proof fn lemma_initial_doctype(
    p: Parser,
    name: Option<Seq<u32>>,
    public_id: Option<Seq<u32>>,
    system_id: Option<Seq<u32>>,
    force_quirks: bool,
)
    requires
        st(p),
    ensures
        kp(p, initial_doctype(p, name, public_id, system_id, force_quirks), 1),
{
    hide(create);
    hide(dom_insert);
    hide(set_document_mode);
    hide(doctype_is_quirks);
    hide(doctype_is_limited_quirks);
    let k = NodeKind::DocumentType { name: or_empty(name), public_id: or_empty(public_id), system_id: or_empty(system_id) };
    lemma_create(p, k);
    let (p1, doctype) = create(p, k);
    lemma_kp(p, p1, 1);
    let p2 = if p1.stopped || has_doctype_child(p1.doc, 0) || has_element_child(p1.doc, 0) {
        p1
    } else {
        dom_insert(p1, doctype, 0, None)
    };
    lemma_dom_insert(p1, doctype, 0, None);
    lemma_kp_refl(p1);
    lemma_kp_trans(p, p1, p2, 1, 0);
    lemma_kp(p, p2, 1);
    lemma_set_document_mode(p2, DocumentMode::Quirks);
    lemma_set_document_mode(p2, DocumentMode::LimitedQuirks);
    lemma_kp_refl(p2);
    let p3 = if doctype_is_quirks(name, public_id, system_id, force_quirks) {
        set_document_mode(p2, DocumentMode::Quirks)
    } else if doctype_is_limited_quirks(public_id, system_id) {
        set_document_mode(p2, DocumentMode::LimitedQuirks)
    } else {
        p2
    };
    lemma_kp_trans(p, p2, p3, 1, 0);
    lemma_kp_fields(p, p3, Parser { mode: Mode::BeforeHtml, ..p3 }, 1);
}

/// §13.2.6.4.2 "before html".
pub proof fn lemma_mode_before_html(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_ok(Rules::Html(Mode::BeforeHtml), p, t, mode_before_html(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(create_element_for_token);
    hide(insert_element_at);
    let r = Rules::Html(Mode::BeforeHtml);
    let o = mode_before_html(env, p, t);
    if t is Doctype || (t is Char && is_ascii_whitespace(t->Char_0)) || (t is End && !(t->End_0.tag == Tag::Head || t->End_0.tag
        == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br)) {
        lemma_done_same(p, t, p);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, Some(document_location()));
        lemma_done(p, t, insert_comment(p, t->Comment_0, Some(document_location())), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location()));
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())), 1);
        lemma_quiet_ok(r, p, t, o);
    } else {
        let tt = if t is Start && t->Start_0.tag == Tag::Html {
            t->Start_0
        } else {
            start_tag_named(seq![0x68u32, 0x74, 0x6d, 0x6c])
        };
        lemma_create_element_for_token(p, tt, Namespace::Html, 0);
        let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
        lemma_kp(p, p1, elem_cost(Namespace::Html, tt.tag));
        lemma_insert_element_at(p1, e.id, Some(document_location()));
        let p2 = insert_element_at(p1, e.id, Some(document_location()));
        lemma_kp_trans(p, p1, p2, elem_cost(Namespace::Html, tt.tag), 0);
        lemma_kp(p, p2, elem_cost(Namespace::Html, tt.tag));
        let p3 = push(p2, e);
        if !p2.stopped {
            lemma_kp(p1, p2, 0);
            lemma_elem_dext(p1.doc, p2.doc, e);
            lemma_st(p2);
            assert forall|i: int| 0 <= i < p3.open.len() implies elem_in_doc(p3.doc, #[trigger] p3.open[i]) by {
                if i < p2.open.len() {
                    assert(p3.open[i] == p2.open[i]);
                }
            }
            lemma_fresh(p, e.id);
            if od(p2) {
                lemma_distinct_push(p2.open, e);
            }
            lemma_st_lists(p2, p3);
        } else {
            lemma_kp_refl(p2);
        }
        lemma_kp_trans(p, p2, p3, elem_cost(Namespace::Html, tt.tag), 0);
        let q = Parser { mode: Mode::BeforeHead, ..p3 };
        lemma_kp_fields(p, p3, q, elem_cost(Namespace::Html, tt.tag));
        if t is Start && t->Start_0.tag == Tag::Html {
            lemma_done(p, t, q, elem_cost(Namespace::Html, tt.tag));
            lemma_quiet_ok(r, p, t, o);
        } else {
            assert(tt.tag == Tag::Html) by {
                assert(tag_of(seq![0x68u32, 0x74, 0x6d, 0x6c]) == Tag::Html) by (compute);
            }
            lemma_growth_edge(r, p, t, q);
        }
    }
}

/// §13.2.6.4.3 "before head".
pub proof fn lemma_mode_before_head(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        crate::exec::modes::initial::tok_ok(t),
    ensures
        app_ok(Rules::Html(Mode::BeforeHead), p, t, mode_before_head(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    let r = Rules::Html(Mode::BeforeHead);
    let o = mode_before_head(env, p, t);
    if t is Doctype || (t is Char && is_ascii_whitespace(t->Char_0)) || (t is End && !(t->End_0.tag == Tag::Head || t->End_0.tag
        == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br)) {
        lemma_done_same(p, t, p);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && t->Start_0.tag == Tag::Html {
        lemma_using_same(p, t, Mode::InBody);
        lemma_quiet_ok(r, p, t, o);
    } else {
        lemma_before_head_insert(r, p, t);
    }
}

/// "before head"'s `head` start tag and anything else: the `head` element.
pub proof fn lemma_before_head_insert(r: Rules, p: Parser, t: Tok)
    requires
        st(p),
        crate::exec::modes::initial::tok_ok(t),
        r == Rules::Html(Mode::BeforeHead),
        !(t is Doctype || (t is Char && is_ascii_whitespace(t->Char_0)) || (t is End && !(t->End_0.tag == Tag::Head
            || t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br)) || t is Comment || t is Pi
            || (t is Start && t->Start_0.tag == Tag::Html)),
    ensures
        app_ok(r, p, t, if t is Start && t->Start_0.tag == Tag::Head {
            Outcome::Done(Parser { head: Some(insert_html_element(p, t->Start_0).1.id), mode: Mode::InHead, ..insert_html_element(p, t->Start_0).0 })
        } else {
            before_head_anything_else(p, t)
        }),
{
    hide(insert_html_element);
    let o = if t is Start && t->Start_0.tag == Tag::Head {
        Outcome::Done(Parser { head: Some(insert_html_element(p, t->Start_0).1.id), mode: Mode::InHead, ..insert_html_element(p, t->Start_0).0 })
    } else {
        before_head_anything_else(p, t)
    };
    let tt = if t is Start && t->Start_0.tag == Tag::Head {
        t->Start_0
    } else {
        start_tag_named(seq![0x68u32, 0x65, 0x61, 0x64])
    };
    lemma_insert_html_element(p, tt);
    let (p1, e) = insert_html_element(p, tt);
    lemma_kp(p, p1, elem_cost(Namespace::Html, tt.tag));
    let q = Parser { head: Some(e.id), mode: Mode::InHead, ..p1 };
    crate::exec::modes::before_head::lemma_tag_of_head(tt.name);
    assert(tt.name == seq![0x68u32, 0x65, 0x61, 0x64]) by {
        if !(t is Start && t->Start_0.tag == Tag::Head) {
            assert(start_tag_named(seq![0x68u32, 0x65, 0x61, 0x64]).name == seq![0x68u32, 0x65, 0x61, 0x64]);
        }
    }
    if !p1.stopped {
        assert(elem_in_doc(q.doc, head_elem(e.id)));
    }
    lemma_st_head(p1, q);
    lemma_kp_trans(p, p1, q, elem_cost(Namespace::Html, tt.tag), 0);
    if t is Start && t->Start_0.tag == Tag::Head {
        lemma_done(p, t, q, elem_cost(Namespace::Html, tt.tag));
        lemma_quiet_ok(r, p, t, o);
    } else {
        assert(tt.tag == Tag::Head) by {
            assert(tag_of(seq![0x68u32, 0x65, 0x61, 0x64]) == Tag::Head) by (compute);
        }
        lemma_growth_edge(r, p, t, q);
    }
}

/// Setting the head element pointer to a node of the document.
pub proof fn lemma_st_head(p: Parser, q: Parser)
    requires
        st(p),
        q.doc == p.doc,
        q.open == p.open,
        q.formatting == p.formatting,
        q.form == p.form,
        q.context == p.context,
        q.redirect == p.redirect,
        q.stopped == p.stopped,
        opt_valid(q.doc, q.head),
        q.stopped || head_ok(q),
    ensures
        kp(p, q, 0),
{
    reveal(st);
    reveal(kp);
}

/// Push an element of the document onto the stack.
pub proof fn lemma_push_elem(p: Parser, e: Elem)
    requires
        st(p),
        !p.stopped ==> elem_in_doc(p.doc, e),
        !p.stopped ==> not_on(p.open, e.id),
    ensures
        kp(p, push(p, e), 0),
{
    if p.stopped {
        lemma_kp_refl(p);
    } else {
        lemma_st(p);
        let q = push(p, e);
        assert forall|i: int| 0 <= i < q.open.len() implies elem_in_doc(q.doc, #[trigger] q.open[i]) by {
            if i < p.open.len() {
                assert(q.open[i] == p.open[i]);
            }
        }
        if od(p) {
            lemma_distinct_push(p.open, e);
        }
        lemma_st_lists(p, q);
    }
}

/// A [`pops`] step followed by a change of fields [`st`] does not read is
/// a handled token.
pub proof fn lemma_done_pops(p: Parser, t: Tok, q: Parser, r: Parser)
    requires
        st(p),
        pops(p, q),
        r.doc == q.doc,
        r.open == q.open,
        r.formatting == q.formatting,
        r.head == q.head,
        r.form == q.form,
        r.context == q.context,
        r.redirect == q.redirect,
        r.stopped == q.stopped,
    ensures
        app_quiet(p, t, Outcome::Done(r)),
        kp(p, r, 0),
{
    lemma_pops_kp(p, q);
    lemma_kp_fields(p, q, r, 0);
    lemma_done(p, t, r, 0);
}

/// A [`pops`] step followed by a change of fields [`st`] does not read, as
/// a reprocessing edge with the same list and pending characters.
pub proof fn lemma_edge_pops(p: Parser, t: Tok, q: Parser, r: Parser)
    requires
        st(p),
        pops(p, q),
        r.doc == q.doc,
        r.open == q.open,
        r.formatting == q.formatting,
        r.head == q.head,
        r.form == q.form,
        r.context == q.context,
        r.redirect == q.redirect,
        r.stopped == q.stopped,
        flush(r, t) <= flush(p, t),
    ensures
        app_quiet(p, t, Outcome::Reprocess(r, t)),
{
    lemma_pops_kp(p, q);
    lemma_kp_fields(p, q, r, 0);
}

/// An element inserted and then popped ("acknowledge the self-closing
/// flag"), or left on the stack, with fields changed after.
pub proof fn lemma_done_insert(p: Parser, t: Tok, tt: TagTok, pop_it: bool, r: Parser)
    requires
        st(p),
        ({
            let q1 = insert_html_element(p, tt).0;
            let q = if pop_it {
                pop(q1)
            } else {
                q1
            };
            &&& r.doc == q.doc
            &&& r.open == q.open
            &&& r.formatting == q.formatting
            &&& r.head == q.head
            &&& r.form == q.form
            &&& r.context == q.context
            &&& r.redirect == q.redirect
            &&& r.stopped == q.stopped
        }),
    ensures
        app_quiet(p, t, Outcome::Done(r)),
        kp(p, r, 2),
{
    hide(insert_html_element);
    lemma_insert_html_element(p, tt);
    let q1 = insert_html_element(p, tt).0;
    lemma_kp_weaken(p, q1, elem_cost(Namespace::Html, tt.tag), 2);
    lemma_kp(p, q1, 2);
    let q = if pop_it {
        pop(q1)
    } else {
        q1
    };
    lemma_pop(q1);
    lemma_pops_kp(q1, pop(q1));
    lemma_kp_refl(q1);
    lemma_kp_trans(p, q1, q, 2, 0);
    lemma_kp_fields(p, q, r, 2);
    lemma_done(p, t, r, 2);
}

/// Composing a step of [`kp`] with no new node and the same list and
/// pending characters with a quiet rule application.
pub proof fn lemma_quiet_compose(p: Parser, p1: Parser, t: Tok, o: Outcome)
    requires
        kp(p, p1, 0),
        p1.formatting.len() == p.formatting.len(),
        flush(p1, t) == flush(p, t),
        app_quiet(p1, t, o),
    ensures
        app_quiet(p, t, o),
{
    lemma_kp(p, p1, 0);
    lemma_kp_kpu(p, p1, 0);
    match o {
        Outcome::Done(q) => {
            lemma_kpu_trans(p, p1, q);
        },
        Outcome::Reprocess(q, t2) => {
            lemma_kp_trans(p, p1, q, 0, 0);
        },
        Outcome::Using(m, q, t2) => {
            lemma_kp_trans(p, p1, q, 0, 0);
        },
    }
}

/// The "in head" `meta` start tag.
pub proof fn lemma_in_head_meta(env: EncFns, p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kp(p, in_head_meta(env, p, tt), 2),
{
    hide(insert_html_element);
    let p1 = pop(insert_html_element(p, tt).0);
    lemma_done_insert(p, Tok::Start(tt), tt, true, p1);
    let q = in_head_meta(env, p, tt);
    lemma_kp_fields(p, p1, q, 2);
}

/// The "in head" `script` start tag: an HTML element is inserted.
pub proof fn lemma_in_head_script(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kp(p, in_head_script(p, tt), 2),
{
    let q = insert_html_element(p, tt).0;
    assert(in_head_script(p, tt) == Parser {
        tokenizer: Some(TokenizerState::ScriptData),
        original_mode: q.mode,
        mode: Mode::Text,
        ..q
    });
    lemma_done_insert(p, Tok::Start(tt), tt, false, in_head_script(p, tt));
}

/// The "in head" `template` start tag: a template element and its
/// contents.
pub proof fn lemma_in_head_template_start(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kp(p, in_head_template_start(p, tt), 2),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    lemma_push_marker(p);
    let p1 = push_marker(p);
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    lemma_kp_fields(p, p1, p2, 0);
    lemma_kp(p, p2, 0);
    let ip = appropriate_place(p2, None).parent;
    lemma_create_element_for_token(p2, tt, Namespace::Html, ip);
    let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, ip);
    lemma_kp_weaken(p2, p3, elem_cost(Namespace::Html, tt.tag), 2);
    lemma_kp(p2, p3, 2);
    let loc = appropriate_place(p3, None);
    if !p3.stopped {
        lemma_fresh(p2, template.id);
    }
    lemma_push_elem(p3, template);
    let p4 = push(p3, template);
    lemma_kp(p3, p4, 0);
    lemma_insert_element_at(p4, template.id, Some(loc));
    lemma_kp_trans(p3, p4, insert_element_at(p4, template.id, Some(loc)), 0, 0);
    lemma_kp_trans(p2, p3, insert_element_at(p4, template.id, Some(loc)), 2, 0);
    lemma_kp_trans(p, p2, insert_element_at(p4, template.id, Some(loc)), 0, 2);
}

/// The "in head" `template` end tag.
pub proof fn lemma_in_head_template_end(p: Parser)
    requires
        st(p),
    ensures
        kp(p, in_head_template_end(p), 0),
        in_head_template_end(p).formatting.len() <= p.formatting.len(),
{
    if !open_has_html(p, Tag::Template) {
        lemma_kp_refl(p);
    } else {
        let p1 = generate_all_implied_end_tags_thoroughly(p);
        lemma_generate_all_implied_end_tags_thoroughly(p);
        let p2 = pop_until_popped(p1, Tag::Template);
        lemma_pop_until_popped(p1, Tag::Template);
        lemma_pops_trans(p, p1, p2);
        lemma_pops_kp(p, p2);
        let p3 = clear_to_last_marker(p2);
        lemma_clear_to_last_marker(p2);
        lemma_kp(p, p2, 0);
        lemma_fmt_prefix_kp(p2, p3);
        lemma_kp_trans(p, p2, p3, 0, 0);
        let p4 = Parser { template_modes: p3.template_modes.drop_last(), ..p3 };
        lemma_kp_fields(p, p3, p4, 0);
        lemma_kp_fields(p, p4, reset_insertion_mode(p4), 0);
    }
}

/// §13.2.6.4.4 "in head".
pub proof fn lemma_mode_in_head(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_head(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    hide(in_head_meta);
    hide(generic_text_parsing);
    hide(in_head_script);
    hide(in_head_template_start);
    hide(in_head_template_end);
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char(p, t->Char_0);
        lemma_done(p, t, insert_char(p, t->Char_0), 1);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
    } else if t is Doctype {
        lemma_done_same(p, t, p);
    } else if t is Start && t->Start_0.tag == Tag::Html {
        lemma_using_same(p, t, Mode::InBody);
    } else if t is Start && (t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag == Tag::Bgsound
        || t->Start_0.tag == Tag::Link) {
        lemma_done_insert(p, t, t->Start_0, true, pop(insert_html_element(p, t->Start_0).0));
    } else if t is Start && t->Start_0.tag == Tag::Meta {
        lemma_in_head_meta(env, p, t->Start_0);
        lemma_done(p, t, in_head_meta(env, p, t->Start_0), 2);
    } else if t is Start && (t->Start_0.tag == Tag::Title || (t->Start_0.tag == Tag::Noscript && p.scripting)
        || t->Start_0.tag == Tag::Noframes || t->Start_0.tag == Tag::Style) {
        let raw = t->Start_0.tag != Tag::Title;
        lemma_generic_text_parsing(p, t->Start_0, raw);
        lemma_kp_weaken(p, generic_text_parsing(p, t->Start_0, raw), elem_cost(Namespace::Html, t->Start_0.tag), 2);
        lemma_done(p, t, generic_text_parsing(p, t->Start_0, raw), 2);
    } else if t is Start && t->Start_0.tag == Tag::Noscript {
        let p1 = insert_html_element(p, t->Start_0).0;
        lemma_done_insert(p, t, t->Start_0, false, Parser { mode: Mode::InHeadNoscript, ..p1 });
    } else if t is Start && t->Start_0.tag == Tag::Script {
        lemma_in_head_script(p, t->Start_0);
        lemma_done(p, t, in_head_script(p, t->Start_0), 2);
    } else if t is End && t->End_0.tag == Tag::Head {
        lemma_pop(p);
        lemma_done_pops(p, t, pop(p), Parser { mode: Mode::AfterHead, ..pop(p) });
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br) {
        lemma_pop(p);
        lemma_edge_pops(p, t, pop(p), Parser { mode: Mode::AfterHead, ..pop(p) });
    } else if t is Start && t->Start_0.tag == Tag::Template {
        lemma_in_head_template_start(p, t->Start_0);
        lemma_done(p, t, in_head_template_start(p, t->Start_0), 2);
    } else if t is End && t->End_0.tag == Tag::Template {
        lemma_in_head_template_end(p);
        lemma_done(p, t, in_head_template_end(p), 0);
    } else if (t is Start && t->Start_0.tag == Tag::Head) || t is End {
        lemma_done_same(p, t, p);
    } else {
        lemma_pop(p);
        lemma_edge_pops(p, t, pop(p), Parser { mode: Mode::AfterHead, ..pop(p) });
    }
}

/// §13.2.6.4.5 "in head noscript".
pub proof fn lemma_mode_in_head_noscript(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_head_noscript(env, p, t)),
{
    lemma_pop(p);
    if t is Doctype {
        lemma_done_same(p, t, p);
    } else if t is Start && t->Start_0.tag == Tag::Html {
        lemma_using_same(p, t, Mode::InBody);
    } else if t is End && t->End_0.tag == Tag::Noscript {
        lemma_done_pops(p, t, pop(p), Parser { mode: Mode::InHead, ..pop(p) });
    } else if (t is Char && is_ascii_whitespace(t->Char_0)) || t is Comment || t is Pi || (t is Start && (t->Start_0.tag
        == Tag::Basefont || t->Start_0.tag == Tag::Bgsound || t->Start_0.tag == Tag::Link || t->Start_0.tag == Tag::Meta
        || t->Start_0.tag == Tag::Noframes || t->Start_0.tag == Tag::Style)) {
        lemma_using_same(p, t, Mode::InHead);
    } else if t is End && t->End_0.tag == Tag::Br {
        lemma_edge_pops(p, t, pop(p), Parser { mode: Mode::InHead, ..pop(p) });
    } else if (t is Start && (t->Start_0.tag == Tag::Head || t->Start_0.tag == Tag::Noscript)) || t is End {
        lemma_done_same(p, t, p);
    } else {
        lemma_edge_pops(p, t, pop(p), Parser { mode: Mode::InHead, ..pop(p) });
    }
}

/// §13.2.6.4.8 "text" (whose original insertion mode is not "in table
/// text", `termination::modes_ok`).
pub proof fn lemma_mode_text(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        p.original_mode != Mode::InTableText,
    ensures
        app_quiet(p, t, mode_text(env, p, t)),
{
    hide(insert_char);
    lemma_pop(p);
    if t is Char {
        lemma_insert_char(p, t->Char_0);
        lemma_done(p, t, insert_char(p, t->Char_0), 1);
    } else if t is Eof {
        lemma_edge_pops(p, t, pop(p), Parser { mode: pop(p).original_mode, ..pop(p) });
    } else if t is End && t->End_0.tag == Tag::Script {
        let p2 = Parser { mode: pop(p).original_mode, ..pop(p) };
        lemma_done_pops(p, t, pop(p), p2);
        lemma_kp_fields(p, p2, text_script_end(p), 0);
        lemma_done(p, t, text_script_end(p), 0);
    } else if t is End {
        lemma_done_pops(p, t, pop(p), Parser { mode: pop(p).original_mode, ..pop(p) });
    } else {
        lemma_done_same(p, t, p);
    }
}

/// A new element pushed onto `p`'s stack: its id is the arena's length.
pub open spec fn pushed_new(p: Parser, q: Parser) -> bool {
    q.stopped || (q.open.len() == p.open.len() + 1 && q.open.drop_last() == p.open && q.open.last().id
        == p.doc.nodes.len())
}

/// "Insert an HTML element" pushes a new element.
pub proof fn lemma_insert_html_pushed(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        pushed_new(p, insert_html_element(p, tt).0),
        insert_html_element(p, tt).0.stopped || pop(insert_html_element(p, tt).0).open == p.open,
{
    hide(insert_foreign_element);
    lemma_insert_html_element(p, tt);
    let q = insert_html_element(p, tt).0;
    if !q.stopped {
        assert(q.open.drop_last() =~= p.open);
    }
}

/// The "in head" `template` start tag pushes a new element.
pub proof fn lemma_template_start_pushed(p: Parser, tt: TagTok)
    requires
        st(p),
        !p.stopped,
    ensures
        pushed_new(p, in_head_template_start(p, tt)),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    lemma_push_marker(p);
    let p1 = push_marker(p);
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    lemma_kp_fields(p, p1, p2, 0);
    lemma_kp(p, p2, 0);
    let ip = appropriate_place(p2, None).parent;
    lemma_create_element_for_token(p2, tt, Namespace::Html, ip);
    let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, ip);
    lemma_kp(p2, p3, elem_cost(Namespace::Html, tt.tag));
    let loc = appropriate_place(p3, None);
    let p4 = push(p3, template);
    if !p3.stopped {
        lemma_fresh(p2, template.id);
    }
    lemma_push_elem(p3, template);
    lemma_kp(p3, p4, 0);
    lemma_insert_element_at(p4, template.id, Some(loc));
    let q = insert_element_at(p4, template.id, Some(loc));
    assert(in_head_template_start(p, tt) == q);
    if !q.stopped {
        assert(q.open == p4.open);
        assert(q.open.drop_last() =~= p.open);
    }
}

/// The "in head" `script` start tag pushes a new element.
pub proof fn lemma_script_pushed(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        pushed_new(p, in_head_script(p, tt)),
{
    lemma_insert_html_pushed(p, tt);
    assert(in_head_script(p, tt) == Parser {
        tokenizer: Some(TokenizerState::ScriptData),
        original_mode: insert_html_element(p, tt).0.mode,
        mode: Mode::Text,
        ..insert_html_element(p, tt).0
    });
}

/// The "in head" `meta` start tag keeps the stack.
pub proof fn lemma_meta_open(env: EncFns, p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        in_head_meta(env, p, tt).stopped || in_head_meta(env, p, tt).open == p.open,
{
    hide(insert_html_element);
    lemma_insert_html_pushed(p, tt);
}

/// The stack after the "in head" rules for the start tags of "after head"
/// case 8: kept, or one new element pushed (its id is the arena's length).
pub proof fn lemma_in_head_case8_open(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        !p.stopped,
        t is Start && after_head_in_head_tag(t->Start_0.tag),
    ensures
        mode_in_head(env, p, t) is Done,
        mode_in_head(env, p, t)->Done_0.open == p.open || pushed_new(p, mode_in_head(env, p, t)->Done_0),
{
    hide(insert_html_element);
    hide(in_head_meta);
    hide(generic_text_parsing);
    hide(in_head_script);
    hide(in_head_template_start);
    hide(in_head_template_end);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(pushed_new);
    crate::termination::helpers_early::lemma_in_head_start_done(env, p, t);
    let tt = t->Start_0;
    if tt.tag == Tag::Template {
        lemma_template_start_pushed(p, tt);
    } else if tt.tag == Tag::Script {
        lemma_script_pushed(p, tt);
    } else if tt.tag == Tag::Meta {
        lemma_meta_open(env, p, tt);
        reveal(pushed_new);
    } else if tt.tag == Tag::Title || tt.tag == Tag::Noframes || tt.tag == Tag::Style {
        lemma_insert_html_pushed(p, tt);
        reveal(pushed_new);
        reveal(generic_text_parsing);
    } else {
        lemma_insert_html_pushed(p, tt);
        reveal(pushed_new);
    }
}

/// "after head"'s rules for the "in head" start tags: the head element is
/// pushed, the "in head" rules run, and it is removed. The stack in
/// between may hold the head element twice; the one removed is the one
/// pushed (the last), so the stack's elements stay distinct ([`od`]).
pub proof fn lemma_after_head_using_in_head(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        !p.stopped,
        t is Start && after_head_in_head_tag(t->Start_0.tag),
    ensures
        app_quiet(p, t, after_head_using_in_head(env, p, t)),
{
    hide(mode_in_head);
    lemma_st(p);
    match p.head {
        None => {
            lemma_done_same(p, t, p);
        },
        Some(h) => {
            let he = head_elem(h);
            let p1 = push(p, he);
            assert forall|i: int| 0 <= i < p1.open.len() implies elem_in_doc(p1.doc, #[trigger] p1.open[i]) by {
                if i < p.open.len() {
                    assert(p1.open[i] == p.open[i]);
                }
            }
            lemma_st_lists(p, p1);
            lemma_dext_refl(p.doc);
            lemma_mode_in_head(env, p1, t);
            lemma_in_head_case8_open(env, p1, t);
            let p2 = mode_in_head(env, p1, t)->Done_0;
            lemma_kpu(p1, p2);
            assert(fx(p1) == fx(p));
            let n = p.open.len() as int;
            let f = |e: Elem| e.id == h;
            let i = open_index_of(p2, h);
            if p2.stopped {
                lemma_kpu_intro(p, p2);
            } else {
                lemma_last_index_where_range(p2.open, p2.open.len() as int, f);
                lemma_last_index_where_last(p2.open, p2.open.len() as int, f);
                assert(p2.open[n] == p1.open[n]);
                assert(f(p2.open[n]));
                if p2.open.len() == n + 2 {
                    assert(p2.open[n + 1] == p2.open.last());
                    assert(h < p.doc.nodes.len());
                }
                assert(i == n);
                let q = remove_open_at(p2, i);
                lemma_remove_open_at(p2, i);
                lemma_kp(p2, q, 0);
                lemma_dext_trans(p.doc, p2.doc, q.doc);
                if p2.open.len() == n + 1 {
                    assert(q.open =~= p.open);
                } else {
                    let x = p2.open.last();
                    assert(q.open =~= p.open.push(x));
                    lemma_fresh(p, x.id);
                    if od(p) {
                        lemma_distinct_push(p.open, x);
                    }
                }
                lemma_kpu_intro(p, q);
            }
        },
    }
}

/// §13.2.6.4.6 "after head" (of a running parser, whose head element
/// pointer names a `head` element).
pub proof fn lemma_mode_after_head(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        !p.stopped,
    ensures
        app_ok(Rules::Html(Mode::AfterHead), p, t, mode_after_head(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    hide(after_head_using_in_head);
    let r = Rules::Html(Mode::AfterHead);
    let o = mode_after_head(env, p, t);
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char(p, t->Char_0);
        lemma_done(p, t, insert_char(p, t->Char_0), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Doctype || (t is Start && t->Start_0.tag == Tag::Head) || (t is End && !(t->End_0.tag == Tag::Template
        || t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Br)) {
        lemma_done_same(p, t, p);
        lemma_quiet_ok(r, p, t, o);
    } else if (t is Start && t->Start_0.tag == Tag::Html) || (t is End && t->End_0.tag == Tag::Template) {
        lemma_using_same(p, t, if t is Start {
            Mode::InBody
        } else {
            Mode::InHead
        });
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && t->Start_0.tag == Tag::Body {
        let p1 = insert_html_element(p, t->Start_0).0;
        lemma_done_insert(p, t, t->Start_0, false, Parser { frameset_ok: false, mode: Mode::InBody, ..p1 });
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && t->Start_0.tag == Tag::Frameset {
        let p1 = insert_html_element(p, t->Start_0).0;
        lemma_done_insert(p, t, t->Start_0, false, Parser { mode: Mode::InFrameset, ..p1 });
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && after_head_in_head_tag(t->Start_0.tag) {
        lemma_after_head_using_in_head(env, p, t);
        lemma_quiet_ok(r, p, t, o);
    } else {
        let tt = start_tag_named(seq![0x62u32, 0x6f, 0x64, 0x79]);
        lemma_insert_html_element(p, tt);
        let p1 = insert_html_element(p, tt).0;
        assert(tag_of(seq![0x62u32, 0x6f, 0x64, 0x79]) == Tag::Body) by (compute);
        lemma_kp_fields(p, p1, Parser { frameset_ok: true, mode: Mode::InBody, ..p1 }, 1);
        lemma_growth_edge(r, p, t, Parser { frameset_ok: true, mode: Mode::InBody, ..p1 });
    }
}

// ---------------------------------------------------------------------
// "in body" (§13.2.6.4.7)

/// The bound of most "in body" rules: two per entry of the list (one
/// reconstruction without [`fx`]) and two (one element, or a template and
/// its contents).
pub open spec fn kpb(p: Parser, q: Parser) -> bool {
    kp(p, q, 2 * p.formatting.len() + 2)
}

/// A handled token within [`kpb`].
pub proof fn lemma_done_b(p: Parser, t: Tok, q: Parser)
    requires
        kpb(p, q),
    ensures
        app_quiet(p, t, Outcome::Done(q)),
{
    lemma_done(p, t, q, 2 * p.formatting.len() + 2);
}

/// A handled token within [`kpu`] and the count with [`fx`].
pub proof fn lemma_done_u(p: Parser, t: Tok, q: Parser)
    requires
        kpu(p, q),
        fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + done_max() + 2 * p.formatting.len(),
    ensures
        app_quiet(p, t, Outcome::Done(q)),
{
}

/// `X(p)` of [`kp`] with no new node and the same list length, then an HTML
/// element inserted (and popped if `pop_it`), then fields changed.
pub proof fn lemma_then_insert(p: Parser, p1: Parser, c: nat, tt: TagTok, pop_it: bool, r: Parser)
    requires
        st(p),
        kp(p, p1, c),
        c <= 2 * p.formatting.len(),
        p1.formatting.len() == p.formatting.len(),
        ({
            let q1 = insert_html_element(p1, tt).0;
            let q = if pop_it {
                pop(q1)
            } else {
                q1
            };
            &&& r.doc == q.doc
            &&& r.open == q.open
            &&& r.formatting == q.formatting
            &&& r.head == q.head
            &&& r.form == q.form
            &&& r.context == q.context
            &&& r.redirect == q.redirect
            &&& r.stopped == q.stopped
        }),
    ensures
        kpb(p, r),
{
    hide(insert_html_element);
    lemma_kp(p, p1, c);
    lemma_done_insert(p1, Tok::Eof, tt, pop_it, r);
    lemma_kp_trans(p, p1, r, c, 2);
    lemma_kp_weaken(p, r, c + 2, 2 * p.formatting.len() + 2);
}

/// Pops of `p`, as [`kp`] with no new node.
pub proof fn lemma_pops_kp0(p: Parser, q: Parser)
    requires
        st(p),
        pops(p, q),
    ensures
        kp(p, q, 0),
        q.formatting.len() == p.formatting.len(),
{
    lemma_pops_kp(p, q);
}

/// Reconstruct, as [`kp`] within two per entry.
pub proof fn lemma_reconstruct_kp(p: Parser)
    requires
        st(p),
    ensures
        kp(p, reconstruct_formatting(p), 2 * p.formatting.len()),
        reconstruct_formatting(p).formatting.len() == p.formatting.len(),
{
    lemma_reconstruct_formatting(p);
}

/// Pops then reconstruct.
pub proof fn lemma_pops_reconstruct(p: Parser, q: Parser)
    requires
        st(p),
        pops(p, q),
    ensures
        kp(p, reconstruct_formatting(q), 2 * p.formatting.len()),
        reconstruct_formatting(q).formatting.len() == p.formatting.len(),
{
    lemma_pops_kp0(p, q);
    lemma_kp(p, q, 0);
    lemma_reconstruct_kp(q);
    lemma_kp_trans(p, q, reconstruct_formatting(q), 0, 2 * p.formatting.len());
}

/// The "li" loop pops.
pub proof fn lemma_li_loop(p: Parser, i: int)
    ensures
        pops(p, li_loop(p, i)),
    decreases i + 1,
{
    if i >= 0 {
        let node = p.open[i];
        if is_html(node, Tag::Li) {
            let q = generate_implied_end_tags(p, Some(Tag::Li));
            lemma_generate_implied_end_tags(p, Some(Tag::Li));
            lemma_pop_until_popped(q, Tag::Li);
            lemma_pops_trans(p, q, pop_until_popped(q, Tag::Li));
        } else if !(is_special(node) && !is_html(node, Tag::Address) && !is_html(node, Tag::Div) && !is_html(node, Tag::P)) {
            lemma_li_loop(p, i - 1);
        }
    }
}

/// The "dd"/"dt" loop pops.
pub proof fn lemma_dd_dt_loop(p: Parser, i: int)
    ensures
        pops(p, dd_dt_loop(p, i)),
    decreases i + 1,
{
    if i >= 0 {
        let node = p.open[i];
        if is_html(node, Tag::Dd) {
            let q = generate_implied_end_tags(p, Some(Tag::Dd));
            lemma_generate_implied_end_tags(p, Some(Tag::Dd));
            lemma_pop_until_popped(q, Tag::Dd);
            lemma_pops_trans(p, q, pop_until_popped(q, Tag::Dd));
        } else if is_html(node, Tag::Dt) {
            let q = generate_implied_end_tags(p, Some(Tag::Dt));
            lemma_generate_implied_end_tags(p, Some(Tag::Dt));
            lemma_pop_until_popped(q, Tag::Dt);
            lemma_pops_trans(p, q, pop_until_popped(q, Tag::Dt));
        } else if !(is_special(node) && !is_html(node, Tag::Address) && !is_html(node, Tag::Div) && !is_html(node, Tag::P)) {
            lemma_dd_dt_loop(p, i - 1);
        }
    }
}

/// A stack that keeps a prefix of `p`'s, with no other change [`st`] reads.
pub proof fn lemma_prefix_kp(p: Parser, r: Parser)
    requires
        st(p),
        r.doc == p.doc,
        r.formatting == p.formatting,
        r.head == p.head,
        r.form == p.form,
        r.context == p.context,
        r.redirect == p.redirect,
        r.stopped == p.stopped,
        r.open.len() <= p.open.len(),
        forall|i: int| 0 <= i < r.open.len() ==> #[trigger] r.open[i] == p.open[i],
    ensures
        kp(p, r, 0),
{
    lemma_st(p);
    assert forall|i: int| 0 <= i < r.open.len() implies elem_in_doc(r.doc, #[trigger] r.open[i]) by {
        assert(r.open[i] == p.open[i]);
    }
    if od(p) && !p.stopped {
        lemma_distinct_prefix(p.open, r.open);
    }
    lemma_st_lists(p, r);
}

/// "in body"'s `li` start tag.
pub proof fn lemma_in_body_start_li(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_li(p, tt)),
{
    hide(insert_html_element);
    hide(li_loop);
    hide(close_p_if_in_button_scope);
    let q = frameset_not_ok(p);
    let q1 = li_loop(q, q.open.len() - 1);
    lemma_li_loop(q, q.open.len() - 1);
    lemma_close_p_if_in_button_scope(q1);
    let q2 = close_p_if_in_button_scope(q1);
    lemma_pops_trans(q, q1, q2);
    lemma_prefix_kp(p, q2);
    lemma_then_insert(p, q2, 0, tt, false, in_body_start_li(p, tt));
}

/// "in body"'s `dd` and `dt` start tags.
pub proof fn lemma_in_body_start_dd_dt(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_dd_dt(p, tt)),
{
    hide(insert_html_element);
    hide(dd_dt_loop);
    hide(close_p_if_in_button_scope);
    let q = frameset_not_ok(p);
    let q1 = dd_dt_loop(q, q.open.len() - 1);
    lemma_dd_dt_loop(q, q.open.len() - 1);
    lemma_close_p_if_in_button_scope(q1);
    let q2 = close_p_if_in_button_scope(q1);
    lemma_pops_trans(q, q1, q2);
    lemma_prefix_kp(p, q2);
    lemma_then_insert(p, q2, 0, tt, false, in_body_start_dd_dt(p, tt));
}

/// "in body"'s `form` start tag: the form element pointer names the new
/// element.
pub proof fn lemma_in_body_start_form(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_form(p, tt)),
{
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    if p.form is Some && !parsing_template_contents(p) {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * p.formatting.len() + 2);
    } else {
        lemma_close_p_if_in_button_scope(p);
        let q = close_p_if_in_button_scope(p);
        lemma_pops_kp0(p, q);
        lemma_kp(p, q, 0);
        lemma_insert_html_element(q, tt);
        let (q1, e) = insert_html_element(q, tt);
        lemma_then_insert(p, q, 0, tt, false, q1);
        if !q1.stopped && !parsing_template_contents(q) {
            lemma_kp(p, q1, 2 * p.formatting.len() + 2);
            lemma_kp(q, q1, elem_cost(Namespace::Html, tt.tag));
            let r = Parser { form: Some(e.id), ..q1 };
            lemma_st(q1);
            lemma_st_form(q1, r);
            lemma_kp_trans(p, q1, r, 2 * p.formatting.len() + 2, 0);
        }
    }
}

/// Setting the form element pointer to a node of the document.
pub proof fn lemma_st_form(p: Parser, q: Parser)
    requires
        st(p),
        q.doc == p.doc,
        q.open == p.open,
        q.formatting == p.formatting,
        q.head == p.head,
        q.context == p.context,
        q.redirect == p.redirect,
        q.stopped == p.stopped,
        opt_valid(q.doc, q.form),
    ensures
        kp(p, q, 0),
{
    reveal(st);
    reveal(kp);
}

/// "in body"'s `a` start tag: the adoption agency, then an `a` element
/// pushed onto the list.
pub proof fn lemma_in_body_start_a(p: Parser, tt: TagTok)
    requires
        st(p),
        tt.tag == Tag::A,
    ensures
        kpu(p, in_body_start_a(p, tt)),
        fx(p) ==> in_body_start_a(p, tt).doc.nodes.len() <= p.doc.nodes.len() + done_max() + 2 * p.formatting.len(),
{
    hide(in_body_adoption);
    hide(reconstruct_formatting);
    hide(insert_html_element);
    hide(push_formatting);
    let f = p.formatting;
    let from = after_last_marker(f, f.len() as int);
    lemma_after_last_marker(f, f.len() as int);
    let i = fmt_last_where(f, from, f.len() as int, |e: Elem| is_html(e, Tag::A));
    lemma_fmt_last_where(f, from, f.len() as int, |e: Elem| is_html(e, Tag::A));
    let q = if i >= 0 {
        let a = f[i]->Entry_elem;
        let q1 = in_body_adoption(p, tt);
        if q1.stopped {
            q1
        } else {
            let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a.id);
            let q2 = if k >= 0 {
                Parser { formatting: q1.formatting.remove(k), ..q1 }
            } else {
                q1
            };
            let j = open_index_of(q2, a.id);
            if j >= 0 {
                remove_open_at(q2, j)
            } else {
                q2
            }
        }
    } else {
        p
    };
    // q: kpu, list no longer, at most 32 new nodes with fx.
    if i >= 0 {
        let a = f[i]->Entry_elem;
        let q1 = in_body_adoption(p, tt);
        lemma_in_body_adoption(p, tt);
        lemma_kpu(p, q1);
        if !q1.stopped {
            let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a.id);
            lemma_fmt_index_of(q1.formatting, q1.formatting.len() as int, a.id);
            let q2 = if k >= 0 {
                Parser { formatting: q1.formatting.remove(k), ..q1 }
            } else {
                q1
            };
            if k >= 0 {
                lemma_fmt_remove(q1, k);
            } else {
                lemma_kp_refl(q1);
            }
            lemma_kp(q1, q2, 0);
            lemma_kp_kpu(q1, q2, 0);
            lemma_kpu_trans(p, q1, q2);
            let j = open_index_of(q2, a.id);
            lemma_last_index_where_range(q2.open, q2.open.len() as int, |e: Elem| e.id == a.id);
            if j >= 0 {
                lemma_remove_open_at(q2, j);
                lemma_kp(q2, remove_open_at(q2, j), 0);
                lemma_kp_kpu(q2, remove_open_at(q2, j), 0);
                lemma_kpu_trans(p, q2, remove_open_at(q2, j));
            }
        }
    } else {
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
    }
    lemma_kpu(p, q);
    assert(q.formatting.len() <= p.formatting.len());
    lemma_reconstruct_formatting(q);
    let qr = reconstruct_formatting(q);
    lemma_kp(q, qr, 2 * q.formatting.len());
    lemma_kp_kpu(q, qr, 2 * q.formatting.len());
    lemma_insert_html_element(qr, tt);
    let (q3, e) = insert_html_element(qr, tt);
    lemma_kp(qr, q3, elem_cost(Namespace::Html, tt.tag));
    lemma_kp_kpu(qr, q3, elem_cost(Namespace::Html, tt.tag));
    if !q3.stopped {
        lemma_fresh(qr, e.id);
    }
    lemma_push_formatting(q3, e, tt);
    let r = push_formatting(q3, e, tt);
    lemma_kp(q3, r, 0);
    lemma_kp_kpu(q3, r, 0);
    lemma_kpu_trans(p, q, qr);
    lemma_kpu_trans(p, qr, q3);
    lemma_kpu_trans(p, q3, r);
}

/// "in body"'s `nobr` start tag.
pub proof fn lemma_in_body_start_nobr(p: Parser, tt: TagTok)
    requires
        st(p),
        tt.tag == Tag::Nobr,
    ensures
        kpu(p, in_body_start_nobr(p, tt)),
        fx(p) ==> in_body_start_nobr(p, tt).doc.nodes.len() <= p.doc.nodes.len() + done_max() + 2 * p.formatting.len(),
{
    hide(in_body_adoption);
    hide(reconstruct_formatting);
    hide(insert_html_element);
    hide(push_formatting);
    let q = reconstruct_formatting(p);
    lemma_reconstruct_formatting(p);
    lemma_kp(p, q, 2 * p.formatting.len());
    lemma_kp_kpu(p, q, 2 * p.formatting.len());
    let q1 = if has_in_scope(q, Tag::Nobr, Scope::Default) {
        reconstruct_formatting(in_body_adoption(q, tt))
    } else {
        q
    };
    if has_in_scope(q, Tag::Nobr, Scope::Default) {
        let qa = in_body_adoption(q, tt);
        lemma_in_body_adoption(q, tt);
        lemma_kpu(q, qa);
        lemma_reconstruct_formatting(qa);
        lemma_kp(qa, q1, 2 * qa.formatting.len());
        lemma_kp_kpu(qa, q1, 2 * qa.formatting.len());
        lemma_kpu_trans(q, qa, q1);
        lemma_kpu_trans(p, q, q1);
    } else {
        lemma_kp_refl(q);
        lemma_kp_kpu(q, q, 0);
    }
    lemma_kpu(p, q1);
    lemma_insert_html_element(q1, tt);
    let (q2, e) = insert_html_element(q1, tt);
    lemma_kp(q1, q2, elem_cost(Namespace::Html, tt.tag));
    lemma_kp_kpu(q1, q2, elem_cost(Namespace::Html, tt.tag));
    if !q2.stopped {
        lemma_fresh(q1, e.id);
    }
    lemma_push_formatting(q2, e, tt);
    let r = push_formatting(q2, e, tt);
    lemma_kp(q2, r, 0);
    lemma_kp_kpu(q2, r, 0);
    lemma_kpu_trans(p, q1, q2);
    lemma_kpu_trans(p, q2, r);
}

/// "in body"'s formatting start tags other than `a` and `nobr`.
pub proof fn lemma_in_body_start_formatting(p: Parser, tt: TagTok)
    requires
        st(p),
        is_formatting_start_tag(tt.tag),
    ensures
        kpb(p, push_formatting(insert_html_element(reconstruct_formatting(p), tt).0, insert_html_element(reconstruct_formatting(p), tt).1, tt)),
{
    hide(reconstruct_formatting);
    hide(insert_html_element);
    hide(push_formatting);
    lemma_reconstruct_kp(p);
    let q = reconstruct_formatting(p);
    lemma_kp(p, q, 2 * p.formatting.len());
    lemma_insert_html_element(q, tt);
    let (q2, e) = insert_html_element(q, tt);
    lemma_then_insert(p, q, 2 * p.formatting.len(), tt, false, q2);
    lemma_kp(q, q2, elem_cost(Namespace::Html, tt.tag));
    if !q2.stopped {
        lemma_fresh(q, e.id);
    }
    lemma_push_formatting(q2, e, tt);
    lemma_kp_trans(p, q2, push_formatting(q2, e, tt), 2 * p.formatting.len() + 2, 0);
}

/// "in body"'s `frameset` start tag: the body element is removed from its
/// parent and the stack.
pub proof fn lemma_in_body_start_frameset(p: Parser, tt: TagTok)
    requires
        st(p),
        p.open.len() > 0,
    ensures
        kpb(p, in_body_start_frameset(p, tt)),
{
    hide(insert_html_element);
    hide(dom_remove);
    if p.open.len() == 1 || !is_html(p.open[1], Tag::Body) || !p.frameset_ok {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * p.formatting.len() + 2);
    } else {
        lemma_dom_remove(p, p.open[1].id);
        let q1 = dom_remove(p, p.open[1].id);
        lemma_kp(p, q1, 0);
        let q2 = Parser { open: q1.open.take(1), ..q1 };
        lemma_prefix_kp(q1, q2);
        lemma_kp_trans(p, q1, q2, 0, 0);
        let q3 = insert_html_element(q2, tt).0;
        lemma_then_insert(p, q2, 0, tt, false, Parser { mode: Mode::InFrameset, ..q3 });
    }
}

/// Insert an HTML element and pop it unless parsing stopped.
pub proof fn lemma_insert_and_pop(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kp(p, insert_and_pop(p, tt), 2),
        insert_and_pop(p, tt).formatting == p.formatting,
{
    hide(insert_html_element);
    lemma_insert_html_element(p, tt);
    let q = insert_html_element(p, tt).0;
    lemma_kp_weaken(p, q, elem_cost(Namespace::Html, tt.tag), 2);
    lemma_kp(p, q, 2);
    if !q.stopped {
        lemma_pop(q);
        lemma_pops_kp(q, pop(q));
        lemma_kp_trans(p, q, pop(q), 2, 0);
    }
}

/// `X(p)` of [`kp`] within two per entry and the same list length, then
/// [`insert_and_pop`], then fields changed.
pub proof fn lemma_then_insert_and_pop(p: Parser, p1: Parser, c: nat, tt: TagTok, r: Parser)
    requires
        st(p),
        kp(p, p1, c),
        c <= 2 * p.formatting.len(),
        ({
            let q = insert_and_pop(p1, tt);
            &&& r.doc == q.doc
            &&& r.open == q.open
            &&& r.formatting == q.formatting
            &&& r.head == q.head
            &&& r.form == q.form
            &&& r.context == q.context
            &&& r.redirect == q.redirect
            &&& r.stopped == q.stopped
        }),
    ensures
        kpb(p, r),
{
    hide(insert_and_pop);
    lemma_kp(p, p1, c);
    lemma_insert_and_pop(p1, tt);
    lemma_kp_trans(p, p1, insert_and_pop(p1, tt), c, 2);
    lemma_kp_fields(p, insert_and_pop(p1, tt), r, c + 2);
    lemma_kp_weaken(p, r, c + 2, 2 * p.formatting.len() + 2);
}

/// The generic text parsing algorithms after `X(p)`.
pub proof fn lemma_then_generic(p: Parser, p1: Parser, c: nat, tt: TagTok, raw: bool)
    requires
        st(p),
        kp(p, p1, c),
        c <= 2 * p.formatting.len(),
    ensures
        kpb(p, generic_text_parsing(p1, tt, raw)),
{
    hide(generic_text_parsing);
    lemma_kp(p, p1, c);
    lemma_generic_text_parsing(p1, tt, raw);
    lemma_kp_weaken(p1, generic_text_parsing(p1, tt, raw), elem_cost(Namespace::Html, tt.tag), 2);
    lemma_kp_trans(p, p1, generic_text_parsing(p1, tt, raw), c, 2);
    lemma_kp_weaken(p, generic_text_parsing(p1, tt, raw), c + 2, 2 * p.formatting.len() + 2);
}

/// "in body"'s `html` start tag (on a stack with the `html` element).
pub proof fn lemma_in_body_start_html(p: Parser, tt: TagTok)
    requires
        st(p),
        p.open.len() > 0,
    ensures
        kpb(p, in_body_start_html(p, tt)),
{
    if open_has_html(p, Tag::Template) {
        lemma_kp_refl(p);
    } else {
        lemma_st(p);
        assert(elem_in_doc(p.doc, p.open[0]));
        lemma_add_missing_attributes(p, p.open[0].id, tt.attrs, 0);
    }
    lemma_kp_weaken(p, in_body_start_html(p, tt), 0, 2 * p.formatting.len() + 2);
}

/// "in body"'s `body` start tag (on a stack with the `html` element).
pub proof fn lemma_in_body_start_body(p: Parser, tt: TagTok)
    requires
        st(p),
        p.open.len() > 0,
    ensures
        kpb(p, in_body_start_body(p, tt)),
{
    if p.open.len() == 1 || !is_html(p.open[1], Tag::Body) || open_has_html(p, Tag::Template) {
        lemma_kp_refl(p);
    } else {
        let q = frameset_not_ok(p);
        lemma_kp_refl(p);
        lemma_kp_fields(p, p, q, 0);
        lemma_st(p);
        assert(elem_in_doc(p.doc, p.open[1]));
        lemma_kp(p, q, 0);
        lemma_add_missing_attributes(q, q.open[1].id, tt.attrs, 0);
        lemma_kp_trans(p, q, in_body_start_body(p, tt), 0, 0);
    }
    lemma_kp_weaken(p, in_body_start_body(p, tt), 0, 2 * p.formatting.len() + 2);
}

/// "in body"'s heading start tags.
pub proof fn lemma_in_body_start_heading(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_heading(p, tt)),
{
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    lemma_close_p_if_in_button_scope(p);
    let q = close_p_if_in_button_scope(p);
    let q1 = if q.open.len() > 0 && is_heading(current_node(q)) {
        pop(q)
    } else {
        q
    };
    lemma_pop(q);
    lemma_pops_trans(p, q, pop(q));
    lemma_pops_kp0(p, q1);
    lemma_then_insert(p, q1, 0, tt, false, in_body_start_heading(p, tt));
}

/// "in body"'s `pre` and `listing` start tags.
pub proof fn lemma_in_body_start_pre(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_pre(p, tt)),
{
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    lemma_close_p_if_in_button_scope(p);
    let q = close_p_if_in_button_scope(p);
    lemma_pops_kp0(p, q);
    lemma_then_insert(p, q, 0, tt, false, in_body_start_pre(p, tt));
}

/// "in body"'s `button` start tag.
pub proof fn lemma_in_body_start_button(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_button(p, tt)),
{
    hide(insert_html_element);
    hide(reconstruct_formatting);
    let q = if has_in_scope(p, Tag::Button, Scope::Default) {
        pop_until_popped(generate_implied_end_tags(p, None), Tag::Button)
    } else {
        p
    };
    lemma_generate_implied_end_tags(p, None);
    lemma_pop_until_popped(generate_implied_end_tags(p, None), Tag::Button);
    lemma_pops_trans(p, generate_implied_end_tags(p, None), pop_until_popped(generate_implied_end_tags(p, None), Tag::Button));
    lemma_pops_reconstruct(p, q);
    lemma_then_insert(p, reconstruct_formatting(q), 2 * p.formatting.len(), tt, false, in_body_start_button(p, tt));
}

/// "in body"'s void start tags.
pub proof fn lemma_in_body_void_start_tag(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_void_start_tag(p, tt)),
{
    hide(insert_and_pop);
    hide(reconstruct_formatting);
    lemma_reconstruct_kp(p);
    lemma_then_insert_and_pop(p, reconstruct_formatting(p), 2 * p.formatting.len(), tt, in_body_void_start_tag(p, tt));
}

/// "in body"'s `input` start tag.
pub proof fn lemma_in_body_start_input(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_input(p, tt)),
{
    hide(insert_and_pop);
    hide(reconstruct_formatting);
    if p.context is Some && is_html(p.context->Some_0, Tag::Select) {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * p.formatting.len() + 2);
    } else {
        let q = if has_in_scope(p, Tag::Select, Scope::Default) {
            pop_until_popped(p, Tag::Select)
        } else {
            p
        };
        lemma_pop_until_popped(p, Tag::Select);
        lemma_pops_reconstruct(p, q);
        lemma_then_insert_and_pop(p, reconstruct_formatting(q), 2 * p.formatting.len(), tt, in_body_start_input(p, tt));
    }
}

/// "in body"'s `hr` start tag.
pub proof fn lemma_in_body_start_hr(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_hr(p, tt)),
{
    hide(insert_and_pop);
    hide(close_p_if_in_button_scope);
    lemma_close_p_if_in_button_scope(p);
    let q = close_p_if_in_button_scope(p);
    let q1 = if has_in_scope(q, Tag::Select, Scope::Default) {
        generate_implied_end_tags(q, None)
    } else {
        q
    };
    lemma_generate_implied_end_tags(q, None);
    lemma_pops_trans(p, q, generate_implied_end_tags(q, None));
    lemma_pops_kp0(p, q1);
    lemma_then_insert_and_pop(p, q1, 0, tt, in_body_start_hr(p, tt));
}

/// "in body"'s `textarea` start tag.
pub proof fn lemma_in_body_start_textarea(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_textarea(p, tt)),
{
    hide(insert_html_element);
    lemma_kp_refl(p);
    lemma_then_insert(p, p, 0, tt, false, in_body_start_textarea(p, tt));
}

/// "in body"'s `select` start tag.
pub proof fn lemma_in_body_start_select(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_select(p, tt)),
{
    hide(insert_html_element);
    hide(reconstruct_formatting);
    if p.context is Some && is_html(p.context->Some_0, Tag::Select) {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * p.formatting.len() + 2);
    } else if has_in_scope(p, Tag::Select, Scope::Default) {
        lemma_pop_until_popped(p, Tag::Select);
        lemma_pops_kp0(p, pop_until_popped(p, Tag::Select));
        lemma_kp_weaken(p, pop_until_popped(p, Tag::Select), 0, 2 * p.formatting.len() + 2);
    } else {
        lemma_reconstruct_kp(p);
        lemma_then_insert(p, reconstruct_formatting(p), 2 * p.formatting.len(), tt, false, in_body_start_select(p, tt));
    }
}

/// "in body"'s `option` start tag.
pub proof fn lemma_in_body_start_option(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_option(p, tt)),
{
    hide(insert_html_element);
    hide(reconstruct_formatting);
    let q = if has_in_scope(p, Tag::Select, Scope::Default) {
        generate_implied_end_tags(p, Some(Tag::Optgroup))
    } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
        pop(p)
    } else {
        p
    };
    lemma_generate_implied_end_tags(p, Some(Tag::Optgroup));
    lemma_pop(p);
    lemma_pops_reconstruct(p, q);
    lemma_then_insert(p, reconstruct_formatting(q), 2 * p.formatting.len(), tt, false, in_body_start_option(p, tt));
}

/// "in body"'s `optgroup` start tag.
pub proof fn lemma_in_body_start_optgroup(p: Parser, tt: TagTok)
    requires
        st(p),
    ensures
        kpb(p, in_body_start_optgroup(p, tt)),
{
    hide(insert_html_element);
    hide(reconstruct_formatting);
    let q = if has_in_scope(p, Tag::Select, Scope::Default) {
        generate_implied_end_tags(p, None)
    } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
        pop(p)
    } else {
        p
    };
    lemma_generate_implied_end_tags(p, None);
    lemma_pop(p);
    lemma_pops_reconstruct(p, q);
    lemma_then_insert(p, reconstruct_formatting(q), 2 * p.formatting.len(), tt, false, in_body_start_optgroup(p, tt));
}

/// A foreign element inserted after reconstructing, popped if
/// self-closing.
pub proof fn lemma_in_body_foreign(p: Parser, t2: TagTok, ns: Namespace, self_closing: bool)
    requires
        st(p),
        ns != Namespace::Html,
    ensures
        ({
            let q1 = insert_foreign_element(reconstruct_formatting(p), t2, ns).0;
            kpb(p, if self_closing && !q1.stopped {
                pop(q1)
            } else {
                q1
            })
        }),
{
    hide(insert_foreign_element);
    hide(reconstruct_formatting);
    lemma_reconstruct_kp(p);
    let q = reconstruct_formatting(p);
    lemma_kp(p, q, 2 * p.formatting.len());
    lemma_insert_foreign_element(q, t2, ns);
    let q1 = insert_foreign_element(q, t2, ns).0;
    lemma_kp_trans(p, q, q1, 2 * p.formatting.len(), 1);
    lemma_kp(p, q1, 2 * p.formatting.len() + 1);
    lemma_pop(q1);
    lemma_pops_kp(q1, pop(q1));
    lemma_kp_trans(p, q1, pop(q1), 2 * p.formatting.len() + 1, 0);
    lemma_kp_weaken(p, q1, 2 * p.formatting.len() + 1, 2 * p.formatting.len() + 2);
    lemma_kp_weaken(p, pop(q1), 2 * p.formatting.len() + 1, 2 * p.formatting.len() + 2);
}

/// The start tags [`lemma_in_body_start_tag_a`] covers: those up to `nobr`
/// in the order of the rules (the rest, [`lemma_in_body_start_tag_b`]).
pub open spec fn in_body_start_first(g: Tag) -> bool {
    g == Tag::Html || is_in_head_start_tag(g) || g == Tag::Body || g == Tag::Frameset || is_block_start_tag(g) || g
        == Tag::Plaintext || is_heading_tag(g) || g == Tag::Pre || g == Tag::Listing || g == Tag::Form || g == Tag::Li || g
        == Tag::Dd || g == Tag::Dt || g == Tag::Button || g == Tag::A || is_formatting_start_tag(g) || g == Tag::Nobr
}

/// "in body"'s start tags up to `nobr`.
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_start_tag_a(p: Parser, t: Tok, tt: TagTok)
    requires
        st(p),
        p.open.len() > 0,
        t == Tok::Start(tt),
        in_body_start_first(tt.tag),
    ensures
        app_quiet(p, t, in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(in_body_start_nobr);
    hide(push_marker);
    hide(close_p_element);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(insert_and_pop);
    hide(in_body_start_hr);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(insert_foreign_element);
    let g = tt.tag;
    if g == Tag::Html {
        lemma_in_body_start_html(p, tt);
        lemma_done_b(p, t, in_body_start_html(p, tt));
    } else if is_in_head_start_tag(g) {
        lemma_using_same(p, t, Mode::InHead);
    } else if g == Tag::Body {
        lemma_in_body_start_body(p, tt);
        lemma_done_b(p, t, in_body_start_body(p, tt));
    } else if g == Tag::Frameset {
        lemma_in_body_start_frameset(p, tt);
        lemma_done_b(p, t, in_body_start_frameset(p, tt));
    } else if is_block_start_tag(g) || g == Tag::Plaintext {
        lemma_close_p_if_in_button_scope(p);
        let q = close_p_if_in_button_scope(p);
        lemma_pops_kp0(p, q);
        let q1 = insert_html_element(q, tt).0;
        lemma_then_insert(p, q, 0, tt, false, q1);
        lemma_then_insert(p, q, 0, tt, false, Parser { tokenizer: Some(TokenizerState::Plaintext), ..q1 });
        lemma_done_b(p, t, q1);
        lemma_done_b(p, t, Parser { tokenizer: Some(TokenizerState::Plaintext), ..q1 });
    } else if is_heading_tag(g) {
        lemma_in_body_start_heading(p, tt);
        lemma_done_b(p, t, in_body_start_heading(p, tt));
    } else if g == Tag::Pre || g == Tag::Listing {
        lemma_in_body_start_pre(p, tt);
        lemma_done_b(p, t, in_body_start_pre(p, tt));
    } else if g == Tag::Form {
        lemma_in_body_start_form(p, tt);
        lemma_done_b(p, t, in_body_start_form(p, tt));
    } else if g == Tag::Li {
        lemma_in_body_start_li(p, tt);
        lemma_done_b(p, t, in_body_start_li(p, tt));
    } else if g == Tag::Dd || g == Tag::Dt {
        lemma_in_body_start_dd_dt(p, tt);
        lemma_done_b(p, t, in_body_start_dd_dt(p, tt));
    } else if g == Tag::Button {
        lemma_in_body_start_button(p, tt);
        lemma_done_b(p, t, in_body_start_button(p, tt));
    } else if g == Tag::A {
        lemma_in_body_start_a(p, tt);
        lemma_done_u(p, t, in_body_start_a(p, tt));
    } else if is_formatting_start_tag(g) {
        lemma_in_body_start_formatting(p, tt);
        let (q, e) = insert_html_element(reconstruct_formatting(p), tt);
        lemma_done_b(p, t, push_formatting(q, e, tt));
    } else if g == Tag::Nobr {
        lemma_in_body_start_nobr(p, tt);
        lemma_done_u(p, t, in_body_start_nobr(p, tt));
    }
}

/// "in body"'s start tags after `nobr`.
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_start_tag_b(p: Parser, t: Tok, tt: TagTok)
    requires
        st(p),
        p.open.len() > 0,
        t == Tok::Start(tt),
        !in_body_start_first(tt.tag),
    ensures
        app_quiet(p, t, in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(in_body_start_nobr);
    hide(push_marker);
    hide(close_p_element);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(insert_and_pop);
    hide(in_body_start_hr);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(insert_foreign_element);
    let g = tt.tag;
    if is_applet_like(g) {
        lemma_reconstruct_kp(p);
        let q0 = reconstruct_formatting(p);
        let q = insert_html_element(q0, tt).0;
        lemma_then_insert(p, q0, 2 * p.formatting.len(), tt, false, q);
        lemma_kp(p, q, 2 * p.formatting.len() + 2);
        lemma_push_marker(q);
        lemma_kp_trans(p, q, push_marker(q), 2 * p.formatting.len() + 2, 0);
        lemma_kp_fields(p, push_marker(q), frameset_not_ok(push_marker(q)), 2 * p.formatting.len() + 2);
        lemma_done_b(p, t, frameset_not_ok(push_marker(q)));
    } else if g == Tag::Table {
        let q = if !doc_is_quirks(p) && has_in_scope(p, Tag::P, Scope::Button) {
            close_p_element(p)
        } else {
            p
        };
        lemma_close_p_element(p);
        lemma_pops_kp0(p, q);
        let q1 = insert_html_element(q, tt).0;
        lemma_then_insert(p, q, 0, tt, false, Parser { frameset_ok: false, mode: Mode::InTable, ..q1 });
        lemma_done_b(p, t, Parser { frameset_ok: false, mode: Mode::InTable, ..q1 });
    } else if is_void_start_tag(g) {
        lemma_in_body_void_start_tag(p, tt);
        lemma_done_b(p, t, in_body_void_start_tag(p, tt));
    } else if g == Tag::Input {
        lemma_in_body_start_input(p, tt);
        lemma_done_b(p, t, in_body_start_input(p, tt));
    } else if g == Tag::Param || g == Tag::Source || g == Tag::Track {
        lemma_kp_refl(p);
        lemma_then_insert_and_pop(p, p, 0, tt, insert_and_pop(p, tt));
        lemma_done_b(p, t, insert_and_pop(p, tt));
    } else if g == Tag::Hr {
        lemma_in_body_start_hr(p, tt);
        lemma_done_b(p, t, in_body_start_hr(p, tt));
    } else if g == Tag::Image {
        lemma_kp_refl(p);
        lemma_quiet_edge(p, t, p, Tok::Start(TagTok { name: name_img(), tag: Tag::Img, ..tt }));
    } else if g == Tag::Textarea {
        lemma_in_body_start_textarea(p, tt);
        lemma_done_b(p, t, in_body_start_textarea(p, tt));
    } else if g == Tag::Xmp {
        lemma_close_p_if_in_button_scope(p);
        let q0 = close_p_if_in_button_scope(p);
        lemma_pops_reconstruct(p, q0);
        let q = frameset_not_ok(reconstruct_formatting(q0));
        lemma_kp_fields(p, reconstruct_formatting(q0), q, 2 * p.formatting.len());
        lemma_then_generic(p, q, 2 * p.formatting.len(), tt, true);
        lemma_done_b(p, t, generic_text_parsing(q, tt, true));
    } else if g == Tag::Iframe || g == Tag::Noembed || (g == Tag::Noscript && p.scripting) {
        let q = if g == Tag::Iframe {
            frameset_not_ok(p)
        } else {
            p
        };
        lemma_kp_refl(p);
        lemma_kp_fields(p, p, q, 0);
        lemma_then_generic(p, q, 0, tt, true);
        lemma_done_b(p, t, generic_text_parsing(q, tt, true));
    } else if g == Tag::Select {
        lemma_in_body_start_select(p, tt);
        lemma_done_b(p, t, in_body_start_select(p, tt));
    } else if g == Tag::Option {
        lemma_in_body_start_option(p, tt);
        lemma_done_b(p, t, in_body_start_option(p, tt));
    } else if g == Tag::Optgroup {
        lemma_in_body_start_optgroup(p, tt);
        lemma_done_b(p, t, in_body_start_optgroup(p, tt));
    } else if g == Tag::Rb || g == Tag::Rtc || g == Tag::Rp || g == Tag::Rt {
        let ex = if g == Tag::Rb || g == Tag::Rtc {
            None
        } else {
            Some(Tag::Rtc)
        };
        let q = if has_in_scope(p, Tag::Ruby, Scope::Default) {
            generate_implied_end_tags(p, ex)
        } else {
            p
        };
        lemma_generate_implied_end_tags(p, ex);
        lemma_pops_kp0(p, q);
        lemma_then_insert(p, q, 0, tt, false, insert_html_element(q, tt).0);
        lemma_done_b(p, t, insert_html_element(q, tt).0);
    } else if g == Tag::Math {
        let t2 = adjust_foreign_attributes(adjust_mathml_attributes(tt));
        lemma_in_body_foreign(p, t2, Namespace::MathMl, tt.self_closing);
        assert(in_body_start_math(p, tt) == ({
            let q1 = insert_foreign_element(reconstruct_formatting(p), t2, Namespace::MathMl).0;
            if tt.self_closing && !q1.stopped {
                pop(q1)
            } else {
                q1
            }
        })) by {
            reveal(in_body_start_math);
        }
        lemma_done_b(p, t, in_body_start_math(p, tt));
    } else if g == Tag::Svg {
        let t2 = adjust_foreign_attributes(adjust_svg_attributes(tt));
        lemma_in_body_foreign(p, t2, Namespace::Svg, tt.self_closing);
        assert(in_body_start_svg(p, tt) == ({
            let q1 = insert_foreign_element(reconstruct_formatting(p), t2, Namespace::Svg).0;
            if tt.self_closing && !q1.stopped {
                pop(q1)
            } else {
                q1
            }
        })) by {
            reveal(in_body_start_svg);
        }
        lemma_done_b(p, t, in_body_start_svg(p, tt));
    } else if is_ignored_start_tag(g) {
        lemma_done_same(p, t, p);
    } else {
        lemma_reconstruct_kp(p);
        lemma_then_insert(p, reconstruct_formatting(p), 2 * p.formatting.len(), tt, false, insert_html_element(reconstruct_formatting(p), tt).0);
        lemma_done_b(p, t, insert_html_element(reconstruct_formatting(p), tt).0);
    }
}


/// "in body"'s start tags (on a stack with the `html` element).
pub proof fn lemma_in_body_start_tag(p: Parser, t: Tok, tt: TagTok)
    requires
        st(p),
        p.open.len() > 0,
        t == Tok::Start(tt),
    ensures
        app_quiet(p, t, in_body_start_tag(p, t, tt)),
{
    if in_body_start_first(tt.tag) {
        lemma_in_body_start_tag_a(p, t, tt);
    } else {
        lemma_in_body_start_tag_b(p, t, tt);
    }
}

/// "in body"'s `form` end tag.
pub proof fn lemma_in_body_end_form(p: Parser)
    requires
        st(p),
    ensures
        kp(p, in_body_end_form(p), 0),
{
    if !parsing_template_contents(p) {
        let node = p.form;
        let q = Parser { form: None, ..p };
        lemma_st_form(p, q);
        match node {
            Some(n) if has_node_in_scope(q, n, Scope::Default) => {
                let q1 = generate_implied_end_tags(q, None);
                lemma_generate_implied_end_tags(q, None);
                lemma_kp(p, q, 0);
                lemma_pops_kp(q, q1);
                lemma_kp_trans(p, q, q1, 0, 0);
                let j = open_index_of(q1, n);
                lemma_last_index_where_range(q1.open, q1.open.len() as int, |e: Elem| e.id == n);
                if j >= 0 {
                    lemma_kp(p, q1, 0);
                    lemma_remove_open_at(q1, j);
                    lemma_kp_trans(p, q1, remove_open_at(q1, j), 0, 0);
                }
            },
            _ => {},
        }
    } else if !has_in_scope(p, Tag::Form, Scope::Default) {
        lemma_kp_refl(p);
    } else {
        let q = generate_implied_end_tags(p, None);
        lemma_generate_implied_end_tags(p, None);
        lemma_pop_until_popped(q, Tag::Form);
        lemma_pops_trans(p, q, pop_until_popped(q, Tag::Form));
        lemma_pops_kp(p, pop_until_popped(q, Tag::Form));
    }
}

/// "in body"'s end tags.
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_end_tag(p: Parser, t: Tok, tt: TagTok)
    requires
        st(p),
        t == Tok::End(tt),
    ensures
        app_quiet(p, t, in_body_end_tag(p, t, tt)),
{
    hide(in_body_end_same_name);
    hide(in_body_end_form);
    hide(insert_html_element);
    hide(close_p_element);
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(pop_until_named_popped);
    hide(pop_until_heading_popped);
    hide(in_body_any_other_end_tag);
    hide(in_body_adoption);
    hide(clear_to_last_marker);
    hide(in_body_void_start_tag);
    let g = tt.tag;
    if g == Tag::Template {
        lemma_using_same(p, t, Mode::InHead);
    } else if g == Tag::Body {
        lemma_done_same(p, t, p);
        lemma_done_same(p, t, Parser { mode: Mode::AfterBody, ..p });
    } else if g == Tag::Html {
        lemma_done_same(p, t, p);
        lemma_kp_refl(p);
        lemma_kp_fields(p, p, Parser { mode: Mode::AfterBody, ..p }, 0);
        lemma_quiet_edge(p, t, Parser { mode: Mode::AfterBody, ..p }, t);
    } else if is_block_end_tag(g) {
        if has_same_name_in_scope(p, tt) {
            let q = generate_implied_end_tags(p, None);
            lemma_generate_implied_end_tags(p, None);
            lemma_pop_until_named_popped(q, tt.name);
            lemma_pops_trans(p, q, pop_until_named_popped(q, tt.name));
            lemma_pops_kp(p, pop_until_named_popped(q, tt.name));
        } else {
            lemma_kp_refl(p);
        }
        reveal(in_body_end_same_name);
        lemma_done(p, t, in_body_end_same_name(p, tt), 0);
    } else if g == Tag::Form {
        lemma_in_body_end_form(p);
        lemma_done(p, t, in_body_end_form(p), 0);
    } else if g == Tag::P {
        let q = if !has_in_scope(p, Tag::P, Scope::Button) {
            insert_html_element(p, start_tag_named(name_p())).0
        } else {
            p
        };
        lemma_kp_refl(p);
        lemma_then_insert(p, p, 0, start_tag_named(name_p()), false, insert_html_element(p, start_tag_named(name_p())).0);
        lemma_kp_weaken(p, p, 0, 2 * p.formatting.len() + 2);
        lemma_kp(p, q, 2 * p.formatting.len() + 2);
        lemma_close_p_element(q);
        lemma_pops_kp(q, close_p_element(q));
        lemma_kp_trans(p, q, close_p_element(q), 2 * p.formatting.len() + 2, 0);
        lemma_done_b(p, t, close_p_element(q));
    } else if g == Tag::Li || g == Tag::Dd || g == Tag::Dt || is_heading_tag(g) {
        let ex = if is_heading_tag(g) {
            None
        } else {
            Some(g)
        };
        let q = generate_implied_end_tags(p, ex);
        lemma_generate_implied_end_tags(p, ex);
        lemma_pop_until_popped(q, Tag::Li);
        lemma_pop_until_named_popped(q, tt.name);
        lemma_pop_until_heading_popped(q);
        lemma_pops_trans(p, q, pop_until_popped(q, Tag::Li));
        lemma_pops_trans(p, q, pop_until_named_popped(q, tt.name));
        lemma_pops_trans(p, q, pop_until_heading_popped(q));
        lemma_pops_kp(p, pop_until_popped(q, Tag::Li));
        lemma_pops_kp(p, pop_until_named_popped(q, tt.name));
        lemma_pops_kp(p, pop_until_heading_popped(q));
        lemma_done(p, t, pop_until_popped(q, Tag::Li), 0);
        lemma_done(p, t, pop_until_named_popped(q, tt.name), 0);
        lemma_done(p, t, pop_until_heading_popped(q), 0);
        lemma_done_same(p, t, p);
    } else if tt.name == name_sarcasm() || !(is_formatting_end_tag(g) || is_applet_like(g) || g == Tag::Br) {
        lemma_any_other_end_tag_loop(p, tt, p.open.len() - 1);
        reveal(in_body_any_other_end_tag);
        lemma_pops_kp(p, in_body_any_other_end_tag(p, tt));
        lemma_done(p, t, in_body_any_other_end_tag(p, tt), 0);
    } else if is_formatting_end_tag(g) {
        lemma_in_body_adoption(p, tt);
        lemma_done_u(p, t, in_body_adoption(p, tt));
    } else if is_applet_like(g) {
        lemma_done_same(p, t, p);
        let q = generate_implied_end_tags(p, None);
        lemma_generate_implied_end_tags(p, None);
        lemma_pop_until_named_popped(q, tt.name);
        let q1 = pop_until_named_popped(q, tt.name);
        lemma_pops_trans(p, q, q1);
        lemma_pops_kp(p, q1);
        lemma_clear_to_last_marker(q1);
        lemma_kp(p, q1, 0);
        lemma_fmt_prefix_kp(q1, clear_to_last_marker(q1));
        lemma_kp_trans(p, q1, clear_to_last_marker(q1), 0, 0);
        lemma_done(p, t, clear_to_last_marker(q1), 0);
    } else {
        lemma_in_body_void_start_tag(p, TagTok { attrs: seq![], ..tt });
        lemma_done_b(p, t, in_body_void_start_tag(p, TagTok { attrs: seq![], ..tt }));
    }
}

/// §13.2.6.4.7 "in body" (on a stack with the `html` element).
pub proof fn lemma_mode_in_body(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        p.open.len() > 0,
    ensures
        app_quiet(p, t, mode_in_body(env, p, t)),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(insert_comment);
    hide(insert_pi);
    hide(reconstruct_formatting);
    hide(insert_char);
    match t {
        Tok::Char(c) => {
            if c == 0 {
                lemma_done_same(p, t, p);
            } else {
                lemma_reconstruct_kp(p);
                let q = reconstruct_formatting(p);
                lemma_kp(p, q, 2 * p.formatting.len());
                lemma_insert_char(q, c);
                lemma_kp_trans(p, q, insert_char(q, c), 2 * p.formatting.len(), 1);
                lemma_kp_fields(p, insert_char(q, c), frameset_not_ok(insert_char(q, c)), 2 * p.formatting.len() + 1);
                lemma_done(p, t, insert_char(q, c), 2 * p.formatting.len() + 1);
                lemma_done(p, t, frameset_not_ok(insert_char(q, c)), 2 * p.formatting.len() + 1);
            }
        },
        Tok::Comment(data) => {
            lemma_insert_comment(p, data, None);
            lemma_done(p, t, insert_comment(p, data, None), 1);
        },
        Tok::Pi(target, data) => {
            lemma_insert_pi(p, target, data, None);
            lemma_done(p, t, insert_pi(p, target, data, None), 1);
        },
        Tok::Doctype { .. } => {
            lemma_done_same(p, t, p);
        },
        Tok::Start(tt) => {
            lemma_in_body_start_tag(p, t, tt);
        },
        Tok::Eof => {
            lemma_using_same(p, t, Mode::InTemplate);
            lemma_stop_parsing(p);
            lemma_done(p, t, stop_parsing(p), 0);
        },
        Tok::End(tt) => {
            lemma_in_body_end_tag(p, t, tt);
        },
    }
}

// ---------------------------------------------------------------------
// The table modes

/// Composing a step of [`kp`] with no new node with a quiet rule
/// application (for a possibly different token `t1`).
pub proof fn lemma_quiet_compose2(p: Parser, p1: Parser, t: Tok, t1: Tok, o: Outcome)
    requires
        kp(p, p1, 0),
        p1.formatting.len() <= p.formatting.len(),
        flush(p1, t1) <= flush(p, t),
        app_quiet(p1, t1, o),
    ensures
        app_quiet(p, t, o),
{
    lemma_kp(p, p1, 0);
    lemma_kp_kpu(p, p1, 0);
    match o {
        Outcome::Done(q) => {
            lemma_kpu_trans(p, p1, q);
        },
        Outcome::Reprocess(q, t2) => {
            lemma_kp_trans(p, p1, q, 0, 0);
        },
        Outcome::Using(m, q, t2) => {
            lemma_kp_trans(p, p1, q, 0, 0);
        },
    }
}

/// Clearing the foster-parenting flag keeps a quiet application quiet.
pub proof fn lemma_without_foster(p: Parser, t: Tok, o: Outcome)
    requires
        app_quiet(p, t, o),
    ensures
        app_quiet(p, t, outcome_without_foster(o)),
{
    match o {
        Outcome::Done(q) => {
            lemma_kpu_fields(p, q, Parser { foster: false, ..q });
        },
        Outcome::Reprocess(q, t2) => {
            lemma_kp_fields(p, q, Parser { foster: false, ..q }, 0);
        },
        Outcome::Using(m, q, t2) => {
            lemma_kp_fields(p, q, Parser { foster: false, ..q }, 0);
        },
    }
}

/// "in table"'s anything else: the "in body" rules with foster parenting
/// (and the "in head" rules they send the token to).
pub proof fn lemma_in_table_anything_else(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        p.open.len() > 0,
    ensures
        app_quiet(p, t, in_table_anything_else(env, p, t)),
{
    hide(mode_in_body);
    hide(mode_in_head);
    let p1 = Parser { foster: true, ..p };
    lemma_kp_refl(p);
    lemma_kp_fields(p, p, p1, 0);
    lemma_kp(p, p1, 0);
    lemma_mode_in_body(env, p1, t);
    let o = mode_in_body(env, p1, t);
    lemma_quiet_compose2(p, p1, t, t, o);
    match o {
        Outcome::Using(Mode::InHead, q, t2) => {
            lemma_kp(p, q, 0);
            lemma_mode_in_head(env, q, t2);
            let o2 = mode_in_head(env, q, t2);
            lemma_quiet_compose2(p, q, t, t2, o2);
            lemma_without_foster(p, t, o2);
        },
        _ => {
            lemma_without_foster(p, t, o);
        },
    }
}

/// "in body"'s character rules: reconstruct, then a character.
pub proof fn lemma_in_body_char(p: Parser, c: u32)
    requires
        st(p),
    ensures
        ({
            let q = in_body_char(p, c);
            &&& kp(p, q, 2 * p.formatting.len() + 1)
            &&& fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + p.formatting.len() + 1
            &&& q.formatting.len() == p.formatting.len()
            &&& q.pending_table_text == p.pending_table_text
            &&& q.template_modes == p.template_modes
            &&& q.original_mode == p.original_mode
            &&& q.mode == p.mode
        }),
{
    hide(reconstruct_formatting);
    hide(insert_char);
    if c == 0 {
        lemma_kp_refl(p);
        lemma_kp_weaken(p, p, 0, 2 * p.formatting.len() + 1);
    } else {
        lemma_reconstruct_formatting(p);
        let q = reconstruct_formatting(p);
        lemma_kp(p, q, 2 * p.formatting.len());
        lemma_insert_char(q, c);
        lemma_kp(q, insert_char(q, c), 1);
        lemma_kp_trans(p, q, insert_char(q, c), 2 * p.formatting.len(), 1);
        lemma_kp_fields(p, insert_char(q, c), frameset_not_ok(insert_char(q, c)), 2 * p.formatting.len() + 1);
    }
}

/// The pending characters from index `i`, each with "in table"'s anything
/// else: at most one new element per entry of the list and one `Text` node
/// each, with [`fx`].
pub proof fn lemma_reprocess_pending(env: EncFns, p: Parser, s: Seq<u32>, i: int)
    requires
        st(p),
        0 <= i <= s.len(),
    ensures
        ({
            let q = reprocess_pending(env, p, s, i);
            &&& kpu(p, q)
            &&& fx(p) ==> q.doc.nodes.len() <= p.doc.nodes.len() + (s.len() - i) * (p.formatting.len() + 1)
            &&& q.formatting.len() == p.formatting.len()
            &&& q.pending_table_text == p.pending_table_text
            &&& q.template_modes == p.template_modes
            &&& q.original_mode == p.original_mode
        }),
    decreases s.len() - i,
{
    hide(in_body_char);
    if i >= s.len() {
        lemma_kp_refl(p);
        lemma_kp_kpu(p, p, 0);
    } else {
        let p1 = Parser { foster: true, ..p };
        assert(in_table_anything_else(env, p, Tok::Char(s[i])) == Outcome::Done(
            Parser { foster: false, ..in_body_char(p1, s[i]) },
        ));
        let x = in_body_char(p1, s[i]);
        let q1 = Parser { foster: false, ..x };
        lemma_kp_refl(p);
        lemma_kp_fields(p, p, p1, 0);
        lemma_kp(p, p1, 0);
        lemma_in_body_char(p1, s[i]);
        lemma_kp_trans(p, p1, x, 0, 2 * p.formatting.len() + 1);
        lemma_kp_fields(p, x, q1, 2 * p.formatting.len() + 1);
        lemma_kp(p, q1, 2 * p.formatting.len() + 1);
        lemma_kp_kpu(p, q1, 2 * p.formatting.len() + 1);
        lemma_reprocess_pending(env, q1, s, i + 1);
        let q = reprocess_pending(env, q1, s, i + 1);
        lemma_kpu_trans(p, q1, q);
        let (n, f) = ((s.len() - i) as int, p.formatting.len() as int);
        assert((n - 1) * (f + 1) + (f + 1) == n * (f + 1)) by (nonlinear_arith);
    }
}

/// §13.2.6.4.10 "in table text" (in that mode, whose original insertion
/// mode is not "in table text").
pub proof fn lemma_mode_in_table_text(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        p.mode == Mode::InTableText,
        p.original_mode != Mode::InTableText,
    ensures
        app_ok(Rules::Html(Mode::InTableText), p, t, mode_in_table_text(env, p, t)),
{
    hide(reprocess_pending);
    hide(insert_characters);
    let r = Rules::Html(Mode::InTableText);
    if t is Char {
        lemma_done_same(p, t, p);
        lemma_done_same(p, t, Parser { pending_table_text: p.pending_table_text.push(t->Char_0), ..p });
        lemma_quiet_ok(r, p, t, mode_in_table_text(env, p, t));
    } else {
        let pending = p.pending_table_text;
        let p1 = if has_non_whitespace(pending) {
            reprocess_pending(env, p, pending, 0)
        } else if pending.len() == 0 {
            p
        } else {
            insert_characters(p, pending)
        };
        if has_non_whitespace(pending) {
            lemma_reprocess_pending(env, p, pending, 0);
        } else if pending.len() == 0 {
            lemma_kp_refl(p);
            lemma_kp_kpu(p, p, 0);
        } else {
            lemma_insert_characters(p, pending);
            lemma_kp(p, p1, 1);
            lemma_kp_kpu(p, p1, 1);
            let (n, f) = (pending.len() as int, p.formatting.len() as int);
            assert(1 <= n * (f + 1)) by (nonlinear_arith)
                requires n >= 1, f >= 0;
        }
        let q = Parser { mode: p1.original_mode, ..p1 };
        lemma_kpu_fields(p, p1, q);
        crate::termination::lemma_components_bounded(Rules::Html(q.mode), t);
    }
}

/// Clearing the stack back to a context, as [`pops`].
pub proof fn lemma_clear_back(p: Parser)
    ensures
        pops(p, crate::spec::modes::in_table::clear_stack_back_to_table_context(p)),
        pops(p, crate::spec::modes::in_table_body::clear_stack_back_to_table_body_context(p)),
        pops(p, crate::spec::modes::in_row::clear_stack_back_to_table_row_context(p)),
{
    lemma_pop_while(p, |e: Elem| !(is_html(e, Tag::Table) || is_html(e, Tag::Template) || is_html(e, Tag::Html)));
    lemma_pop_while(
        p,
        |e: Elem|
            !(is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(e, Tag::Template)
                || is_html(e, Tag::Html)),
    );
    lemma_pop_while(p, |e: Elem| !(is_html(e, Tag::Tr) || is_html(e, Tag::Template) || is_html(e, Tag::Html)));
}

/// An implicit element (not a template) inserted after pops: one node.
pub proof fn lemma_then_insert1(p: Parser, p1: Parser, tt: TagTok, r: Parser)
    requires
        st(p),
        pops(p, p1),
        tt.tag != Tag::Template,
        ({
            let q = insert_html_element(p1, tt).0;
            &&& r == Parser { mode: r.mode, ..q }
        }),
    ensures
        kp(p, r, 1),
        r.formatting.len() == p.formatting.len(),
        r.template_modes == p.template_modes,
{
    hide(insert_html_element);
    lemma_pops_kp(p, p1);
    lemma_kp(p, p1, 0);
    lemma_insert_html_element(p1, tt);
    let q = insert_html_element(p1, tt).0;
    lemma_kp_trans(p, p1, q, 0, 1);
    lemma_kp_fields(p, q, r, 1);
}

/// "Reset the insertion mode appropriately" after pops never lands in "in
/// table text" (`termination::helpers_ranking::count_ok`).
pub proof fn lemma_reset_after_pops(p: Parser, q: Parser)
    requires
        crate::termination::helpers_ranking::count_ok(p),
        pops(p, q),
    ensures
        reset_insertion_mode(q).mode != Mode::InTableText,
{
    crate::termination::helpers_ranking::lemma_template_count_prefix(p, q);
    crate::termination::helpers_ranking::lemma_reset_from(q, q.open.len() - 1);
}

/// §13.2.6.4.9 "in table" (on a stack with the `html` element).
#[verifier::spinoff_prover]
pub proof fn lemma_mode_in_table(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        p.open.len() > 0,
        crate::termination::helpers_ranking::count_ok(p),
    ensures
        app_ok(Rules::Html(Mode::InTable), p, t, mode_in_table(env, p, t)),
{
    hide(in_table_anything_else);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    hide(pop_while);
    hide(push_marker);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(crate::spec::modes::in_table::clear_stack_back_to_table_context);
    let r = Rules::Html(Mode::InTable);
    let o = mode_in_table(env, p, t);
    let cur = current_node(p);
    let p1 = crate::spec::modes::in_table::clear_stack_back_to_table_context(p);
    lemma_clear_back(p);
    lemma_pops_kp0(p, p1);
    if t is Char && (is_html(cur, Tag::Table) || is_html(cur, Tag::Tbody) || is_html(cur, Tag::Template) || is_html(cur, Tag::Tfoot)
        || is_html(cur, Tag::Thead) || is_html(cur, Tag::Tr)) {
        lemma_kp_refl(p);
        let q = Parser { pending_table_text: seq![], original_mode: p.mode, mode: Mode::InTableText, ..p };
        lemma_kp_fields(p, p, q, 0);
        lemma_quiet_edge(p, t, q, t);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Doctype || (t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption || t->End_0.tag
        == Tag::Col || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Tbody
        || t->End_0.tag == Tag::Td || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Th || t->End_0.tag == Tag::Thead
        || t->End_0.tag == Tag::Tr)) {
        lemma_done_same(p, t, p);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && t->Start_0.tag == Tag::Caption {
        lemma_kp(p, p1, 0);
        lemma_push_marker(p1);
        lemma_kp_trans(p, p1, push_marker(p1), 0, 0);
        lemma_kp(p, push_marker(p1), 0);
        let p3 = insert_html_element(push_marker(p1), t->Start_0).0;
        lemma_done_insert(push_marker(p1), t, t->Start_0, false, Parser { mode: Mode::InCaption, ..p3 });
        lemma_kp_trans(p, push_marker(p1), Parser { mode: Mode::InCaption, ..p3 }, 0, 2);
        lemma_done(p, t, Parser { mode: Mode::InCaption, ..p3 }, 2);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && (t->Start_0.tag == Tag::Colgroup || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot
        || t->Start_0.tag == Tag::Thead) {
        let p2 = insert_html_element(p1, t->Start_0).0;
        let m = if t->Start_0.tag == Tag::Colgroup {
            Mode::InColumnGroup
        } else {
            Mode::InTableBody
        };
        lemma_then_insert(p, p1, 0, t->Start_0, false, Parser { mode: m, ..p2 });
        lemma_done_b(p, t, Parser { mode: m, ..p2 });
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && (t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Th
        || t->Start_0.tag == Tag::Tr) {
        let (tt, m) = if t->Start_0.tag == Tag::Col {
            (start_tag_named(crate::spec::modes::in_table::name_colgroup()), Mode::InColumnGroup)
        } else {
            (start_tag_named(crate::spec::modes::in_table::name_tbody()), Mode::InTableBody)
        };
        assert(tag_of(crate::spec::modes::in_table::name_colgroup()) == Tag::Colgroup) by (compute);
        assert(tag_of(crate::spec::modes::in_table::name_tbody()) == Tag::Tbody) by (compute);
        let p2 = insert_html_element(p1, tt).0;
        lemma_then_insert1(p, p1, tt, Parser { mode: m, ..p2 });
        lemma_growth_edge(r, p, t, Parser { mode: m, ..p2 });
    } else if t is Start && t->Start_0.tag == Tag::Table {
        if !has_in_scope(p, Tag::Table, Scope::Table) {
            lemma_done_same(p, t, p);
            lemma_quiet_ok(r, p, t, o);
        } else {
            let q1 = pop_until_popped(p, Tag::Table);
            lemma_pop_until_popped(p, Tag::Table);
            lemma_reset_after_pops(p, q1);
            reveal(reset_insertion_mode);
            lemma_edge_pops(p, t, q1, reset_insertion_mode(q1));
            lemma_quiet_ok(r, p, t, o);
        }
    } else if t is End && t->End_0.tag == Tag::Table {
        lemma_done_same(p, t, p);
        let q1 = pop_until_popped(p, Tag::Table);
        lemma_pop_until_popped(p, Tag::Table);
        reveal(reset_insertion_mode);
        lemma_done_pops(p, t, q1, reset_insertion_mode(q1));
        lemma_quiet_ok(r, p, t, o);
    } else if (t is Start && (t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Script || t->Start_0.tag == Tag::Template))
        || (t is End && t->End_0.tag == Tag::Template) || t is Eof {
        lemma_using_same(p, t, Mode::InHead);
        lemma_using_same(p, t, Mode::InBody);
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && (t->Start_0.tag == Tag::Input && crate::spec::modes::in_table::in_table_input_is_hidden(t->Start_0)) {
        let q = insert_html_element(p, t->Start_0).0;
        lemma_kp_refl(p);
        lemma_then_insert(p, p, 0, t->Start_0, false, q);
        lemma_then_insert(p, p, 0, t->Start_0, true, pop(q));
        lemma_done_b(p, t, q);
        lemma_done_b(p, t, pop(q));
        lemma_quiet_ok(r, p, t, o);
    } else if t is Start && t->Start_0.tag == Tag::Form {
        if p.form is Some && !parsing_template_contents(p) {
            lemma_done_same(p, t, p);
        } else {
            lemma_insert_html_element(p, t->Start_0);
            let (q1, e) = insert_html_element(p, t->Start_0);
            lemma_kp_weaken(p, q1, elem_cost(Namespace::Html, t->Start_0.tag), 2);
            lemma_kp(p, q1, 2);
            let q2 = if !parsing_template_contents(q1) && !q1.stopped {
                Parser { form: Some(e.id), ..q1 }
            } else {
                q1
            };
            lemma_st_form(q1, Parser { form: Some(e.id), ..q1 });
            lemma_kp_refl(q1);
            lemma_kp_trans(p, q1, q2, 2, 0);
            lemma_kp(p, q2, 2);
            lemma_pop(q2);
            lemma_pops_kp(q2, pop(q2));
            lemma_kp_trans(p, q2, pop(q2), 2, 0);
            lemma_done(p, t, q2, 2);
            lemma_done(p, t, pop(q2), 2);
        }
        lemma_quiet_ok(r, p, t, o);
    } else {
        reveal(in_table_anything_else);
        lemma_in_table_anything_else(env, p, t);
        lemma_quiet_ok(r, p, t, o);
    }
}

/// Pops, then clear the list up to the last marker, then fields: as
/// [`kp`] with no new node and no longer list.
pub proof fn lemma_pops_clear(p: Parser, q: Parser, r: Parser)
    requires
        st(p),
        pops(p, q),
        r == (Parser { mode: r.mode, ..clear_to_last_marker(q) }),
    ensures
        kp(p, r, 0),
        r.formatting.len() <= p.formatting.len(),
{
    lemma_pops_kp(p, q);
    lemma_kp(p, q, 0);
    lemma_clear_to_last_marker(q);
    lemma_fmt_prefix_kp(q, clear_to_last_marker(q));
    lemma_kp_trans(p, q, clear_to_last_marker(q), 0, 0);
    lemma_kp_fields(p, clear_to_last_marker(q), r, 0);
}

/// §13.2.6.4.11 "in caption".
pub proof fn lemma_mode_in_caption(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_caption(env, p, t)),
{
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    let p1 = generate_implied_end_tags(p, None);
    let p2 = pop_until_popped(p1, Tag::Caption);
    lemma_generate_implied_end_tags(p, None);
    lemma_pop_until_popped(p1, Tag::Caption);
    lemma_pops_trans(p, p1, p2);
    lemma_pops_clear(p, p2, Parser { mode: Mode::InTable, ..clear_to_last_marker(p2) });
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InBody);
    lemma_done(p, t, Parser { mode: Mode::InTable, ..clear_to_last_marker(p2) }, 0);
}

/// §13.2.6.4.12 "in column group".
pub proof fn lemma_mode_in_column_group(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_column_group(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InBody);
    lemma_using_same(p, t, Mode::InHead);
    lemma_pop(p);
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char(p, t->Char_0);
        lemma_done(p, t, insert_char(p, t->Char_0), 1);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
    } else if t is Start && t->Start_0.tag == Tag::Col {
        let q = insert_html_element(p, t->Start_0).0;
        lemma_done_insert(p, t, t->Start_0, false, q);
        lemma_done_insert(p, t, t->Start_0, true, pop(q));
    } else {
        lemma_done_pops(p, t, pop(p), Parser { mode: Mode::InTable, ..pop(p) });
        lemma_edge_pops(p, t, pop(p), Parser { mode: Mode::InTable, ..pop(p) });
    }
}

/// §13.2.6.4.13 "in table body".
pub proof fn lemma_mode_in_table_body(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_ok(Rules::Html(Mode::InTableBody), p, t, mode_in_table_body(env, p, t)),
{
    hide(insert_html_element);
    hide(pop_while);
    hide(crate::spec::modes::in_table_body::clear_stack_back_to_table_body_context);
    let r = Rules::Html(Mode::InTableBody);
    let o = mode_in_table_body(env, p, t);
    let p1 = crate::spec::modes::in_table_body::clear_stack_back_to_table_body_context(p);
    lemma_clear_back(p);
    lemma_pops_kp0(p, p1);
    lemma_pop(p1);
    lemma_pops_trans(p, p1, pop(p1));
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        let tt = start_tag_named(crate::spec::modes::in_table_body::name_tr());
        assert(tag_of(crate::spec::modes::in_table_body::name_tr()) == Tag::Tr) by (compute);
        let p2 = insert_html_element(p1, tt).0;
        lemma_then_insert1(p, p1, tt, Parser { mode: Mode::InRow, ..p2 });
        lemma_growth_edge(r, p, t, Parser { mode: Mode::InRow, ..p2 });
    } else {
        lemma_done_same(p, t, p);
        lemma_using_same(p, t, Mode::InTable);
        if t is Start && t->Start_0.tag == Tag::Tr {
            let p2 = insert_html_element(p1, t->Start_0).0;
            lemma_then_insert(p, p1, 0, t->Start_0, false, Parser { mode: Mode::InRow, ..p2 });
            lemma_done_b(p, t, Parser { mode: Mode::InRow, ..p2 });
        }
        lemma_done_pops(p, t, pop(p1), Parser { mode: Mode::InTable, ..pop(p1) });
        lemma_edge_pops(p, t, pop(p1), Parser { mode: Mode::InTable, ..pop(p1) });
        lemma_quiet_ok(r, p, t, o);
    }
}

/// §13.2.6.4.14 "in row".
pub proof fn lemma_mode_in_row(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_row(env, p, t)),
{
    hide(insert_html_element);
    hide(pop_while);
    hide(push_marker);
    hide(crate::spec::modes::in_row::clear_stack_back_to_table_row_context);
    let p1 = crate::spec::modes::in_row::clear_stack_back_to_table_row_context(p);
    lemma_clear_back(p);
    lemma_pops_kp0(p, p1);
    lemma_pop(p1);
    lemma_pops_trans(p, p1, pop(p1));
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InTable);
    lemma_done_pops(p, t, pop(p1), Parser { mode: Mode::InTableBody, ..pop(p1) });
    lemma_edge_pops(p, t, pop(p1), Parser { mode: Mode::InTableBody, ..pop(p1) });
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        let p2 = insert_html_element(p1, t->Start_0).0;
        let p3 = Parser { mode: Mode::InCell, ..p2 };
        lemma_then_insert(p, p1, 0, t->Start_0, false, p3);
        lemma_kp(p, p3, 2 * p.formatting.len() + 2);
        lemma_push_marker(p3);
        lemma_kp_trans(p, p3, push_marker(p3), 2 * p.formatting.len() + 2, 0);
        lemma_done_b(p, t, push_marker(p3));
    }
}

/// "Close the cell".
pub proof fn lemma_close_the_cell(p: Parser)
    requires
        st(p),
    ensures
        kp(p, close_the_cell(p), 0),
        close_the_cell(p).formatting.len() <= p.formatting.len(),
        close_the_cell(p).mode == Mode::InRow,
{
    let p1 = generate_implied_end_tags(p, None);
    lemma_generate_implied_end_tags(p, None);
    lemma_pop_until_cell_popped(p1);
    lemma_pops_trans(p, p1, pop_until_cell_popped(p1));
    lemma_pops_clear(p, pop_until_cell_popped(p1), close_the_cell(p));
}

/// §13.2.6.4.15 "in cell".
pub proof fn lemma_mode_in_cell(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_cell(env, p, t)),
{
    hide(close_the_cell);
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InBody);
    lemma_close_the_cell(p);
    lemma_quiet_edge(p, t, close_the_cell(p), t);
    if t is End && (t->End_0.tag == Tag::Td || t->End_0.tag == Tag::Th) {
        let p1 = generate_implied_end_tags(p, None);
        let p2 = pop_until_popped(p1, t->End_0.tag);
        lemma_generate_implied_end_tags(p, None);
        lemma_pop_until_popped(p1, t->End_0.tag);
        lemma_pops_trans(p, p1, p2);
        lemma_pops_clear(p, p2, Parser { mode: Mode::InRow, ..clear_to_last_marker(p2) });
        lemma_done(p, t, Parser { mode: Mode::InRow, ..clear_to_last_marker(p2) }, 0);
    }
}

/// §13.2.6.4.16 "in template" (with the count bound and a template
/// insertion mode).
pub proof fn lemma_mode_in_template(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
        crate::termination::helpers_ranking::count_ok(p),
        p.template_modes.len() > 0,
    ensures
        app_quiet(p, t, mode_in_template(env, p, t)),
{
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    hide(reset_insertion_mode);
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InBody);
    lemma_using_same(p, t, Mode::InHead);
    lemma_stop_parsing(p);
    lemma_done(p, t, stop_parsing(p), 0);
    lemma_kp_refl(p);
    if t is Start {
        let ms = seq![Mode::InTable, Mode::InColumnGroup, Mode::InTableBody, Mode::InRow, Mode::InBody];
        assert forall|k: int| 0 <= k < 5 implies flush(
            Parser { template_modes: p.template_modes.drop_last().push(#[trigger] ms[k]), mode: ms[k], ..p },
            t,
        ) == 0 by {}
        lemma_kp_fields(p, p, Parser { template_modes: p.template_modes.drop_last().push(ms[0]), mode: ms[0], ..p }, 0);
        lemma_kp_fields(p, p, Parser { template_modes: p.template_modes.drop_last().push(ms[1]), mode: ms[1], ..p }, 0);
        lemma_kp_fields(p, p, Parser { template_modes: p.template_modes.drop_last().push(ms[2]), mode: ms[2], ..p }, 0);
        lemma_kp_fields(p, p, Parser { template_modes: p.template_modes.drop_last().push(ms[3]), mode: ms[3], ..p }, 0);
        lemma_kp_fields(p, p, Parser { template_modes: p.template_modes.drop_last().push(ms[4]), mode: ms[4], ..p }, 0);
    } else if t is Eof && open_has_html(p, Tag::Template) {
        let j = crate::termination::helpers_ranking::lemma_open_has_html(p, Tag::Template);
        let p1 = pop_until_popped(p, Tag::Template);
        lemma_pop_until_popped(p, Tag::Template);
        crate::termination::helpers_ranking::lemma_pop_until_template(p, j);
        let p2 = clear_to_last_marker(p1);
        lemma_clear_to_last_marker(p1);
        let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(p3);
        assert(crate::termination::helpers_ranking::count_ok(p3)) by {
            assert forall|i: int| 0 <= i < p3.template_modes.len() implies crate::termination::template_mode_ok(
                #[trigger] p3.template_modes[i],
            ) by {
                assert(p3.template_modes[i] == p.template_modes[i]);
            }
        }
        crate::termination::helpers_ranking::lemma_reset_from(p3, p3.open.len() - 1);
        reveal(reset_insertion_mode);
        lemma_pops_clear(p, p1, Parser { mode: p2.mode, ..p2 });
        assert(Parser { mode: p2.mode, ..p2 } == p2);
        lemma_kp_fields(p, p2, p3, 0);
        lemma_kp_fields(p, p3, reset_insertion_mode(p3), 0);
        lemma_quiet_edge(p, t, reset_insertion_mode(p3), t);
    }
}

/// §13.2.6.4.17 "after body".
pub proof fn lemma_mode_after_body(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_after_body(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    let l = Some(Location { parent: p.open[0].id, child: None });
    lemma_done_same(p, t, p);
    lemma_done_same(p, t, Parser { mode: Mode::AfterAfterBody, ..p });
    lemma_using_same(p, t, Mode::InBody);
    lemma_stop_parsing(p);
    lemma_done(p, t, stop_parsing(p), 0);
    lemma_kp_refl(p);
    lemma_kp_fields(p, p, Parser { mode: Mode::InBody, ..p }, 0);
    lemma_quiet_edge(p, t, Parser { mode: Mode::InBody, ..p }, t);
    if t is Comment {
        lemma_insert_comment(p, t->Comment_0, l);
        lemma_done(p, t, insert_comment(p, t->Comment_0, l), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, l);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, l), 1);
    }
}

/// §13.2.6.4.18 "in frameset".
pub proof fn lemma_mode_in_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_in_frameset(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InBody);
    lemma_using_same(p, t, Mode::InHead);
    lemma_stop_parsing(p);
    lemma_done(p, t, stop_parsing(p), 0);
    lemma_pop(p);
    lemma_done_pops(p, t, pop(p), pop(p));
    lemma_done_pops(p, t, pop(p), Parser { mode: Mode::AfterFrameset, ..pop(p) });
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char(p, t->Char_0);
        lemma_done(p, t, insert_char(p, t->Char_0), 1);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
    } else if t is Start {
        let q = insert_html_element(p, t->Start_0).0;
        lemma_done_insert(p, t, t->Start_0, false, q);
        lemma_done_insert(p, t, t->Start_0, true, pop(q));
    }
}

/// §13.2.6.4.19 "after frameset".
pub proof fn lemma_mode_after_frameset(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_after_frameset(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    lemma_done_same(p, t, p);
    lemma_done_same(p, t, Parser { mode: Mode::AfterAfterFrameset, ..p });
    lemma_using_same(p, t, Mode::InBody);
    lemma_using_same(p, t, Mode::InHead);
    lemma_stop_parsing(p);
    lemma_done(p, t, stop_parsing(p), 0);
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char(p, t->Char_0);
        lemma_done(p, t, insert_char(p, t->Char_0), 1);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
    }
}

/// §13.2.6.4.20 "after after body" and §13.2.6.4.21 "after after
/// frameset".
pub proof fn lemma_mode_after_after(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, mode_after_after_body(env, p, t)),
        app_quiet(p, t, mode_after_after_frameset(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    lemma_done_same(p, t, p);
    lemma_using_same(p, t, Mode::InBody);
    lemma_using_same(p, t, Mode::InHead);
    lemma_stop_parsing(p);
    lemma_done(p, t, stop_parsing(p), 0);
    lemma_kp_refl(p);
    lemma_kp_fields(p, p, Parser { mode: Mode::InBody, ..p }, 0);
    lemma_quiet_edge(p, t, Parser { mode: Mode::InBody, ..p }, t);
    if t is Comment {
        lemma_insert_comment(p, t->Comment_0, Some(document_location()));
        lemma_done(p, t, insert_comment(p, t->Comment_0, Some(document_location())), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location()));
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, Some(document_location())), 1);
    }
}

/// Foreign content's end tag loop.
pub proof fn lemma_foreign_end_tag_loop(p: Parser, t: Tok, i: int)
    requires
        st(p),
    ensures
        app_quiet(p, t, foreign_end_tag_loop(p, t, i)),
    decreases i,
{
    if i <= 0 || i >= p.open.len() {
        lemma_done_same(p, t, p);
    } else if ascii_lowercase(p.open[i].name) == t->End_0.name {
        lemma_pop_until_node_popped(p, p.open[i].id);
        lemma_done_pops(p, t, pop_until_node_popped(p, p.open[i].id), pop_until_node_popped(p, p.open[i].id));
    } else if p.open[i - 1].ns != clazel_dom::spec::Namespace::Html {
        lemma_foreign_end_tag_loop(p, t, i - 1);
    } else {
        lemma_kp_refl(p);
        lemma_quiet_edge(p, t, p, t);
    }
}

/// §13.2.6.5 the rules for parsing tokens in foreign content.
pub proof fn lemma_foreign_content(env: EncFns, p: Parser, t: Tok)
    requires
        st(p),
    ensures
        app_quiet(p, t, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(pop_while);
    hide(foreign_end_tag_loop);
    lemma_done_same(p, t, p);
    lemma_pop(p);
    lemma_done_pops(p, t, pop(p), pop(p));
    if t is Char {
        let c = if t->Char_0 == 0 {
            0xFFFD
        } else {
            t->Char_0
        };
        lemma_insert_char(p, c);
        lemma_done(p, t, insert_char(p, c), 1);
        lemma_kp_fields(p, insert_char(p, c), Parser { frameset_ok: false, ..insert_char(p, c) }, 1);
        lemma_done(p, t, Parser { frameset_ok: false, ..insert_char(p, c) }, 1);
    } else if t is Comment {
        lemma_insert_comment(p, t->Comment_0, None);
        lemma_done(p, t, insert_comment(p, t->Comment_0, None), 1);
    } else if t is Pi {
        lemma_insert_pi(p, t->Pi_0, t->Pi_1, None);
        lemma_done(p, t, insert_pi(p, t->Pi_0, t->Pi_1, None), 1);
    } else if t is Doctype {
    } else if is_foreign_breakout(t) {
        let f = |e: Elem|
            !(is_mathml_text_integration_point(e) || is_html_integration_point(e) || e.ns == clazel_dom::spec::Namespace::Html);
        lemma_pop_while(p, f);
        lemma_edge_pops(p, t, pop_while(p, f), pop_while(p, f));
    } else if t is Start {
        let a = adjusted_current_node(p);
        let tt = adjust_foreign_start_tag(a, t->Start_0);
        lemma_insert_foreign_element(p, tt, a.ns);
        let p1 = insert_foreign_element(p, tt, a.ns).0;
        lemma_kp_weaken(p, p1, elem_cost(a.ns, tt.tag), 2);
        lemma_kp(p, p1, 2);
        lemma_pop(p1);
        lemma_pops_kp(p1, pop(p1));
        lemma_kp_trans(p, p1, pop(p1), 2, 0);
        lemma_done(p, t, p1, 2);
        lemma_done(p, t, pop(p1), 2);
    } else if t is End {
        lemma_foreign_end_tag_loop(p, t, p.open.len() - 1);
    }
}

// ---------------------------------------------------------------------
// Every rule application, the run, the step

/// The modes [`lemma_apply_early`] covers (the rest, [`lemma_apply_late`]).
pub open spec fn early_mode(m: Mode) -> bool {
    match m {
        Mode::Initial | Mode::BeforeHtml | Mode::BeforeHead | Mode::InHead | Mode::InHeadNoscript | Mode::AfterHead
        | Mode::InBody | Mode::Text | Mode::InTable | Mode::InTableText => true,
        _ => false,
    }
}

/// [`lemma_apply_rules`] for foreign content and the [`early_mode`]s.
#[verifier::spinoff_prover]
pub proof fn lemma_apply_early(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        st(p),
        !p.stopped,
        crate::termination::modes_ok(p),
        crate::termination::rules_ok(r, p),
        rooted_needs(r, p),
        crate::exec::modes::initial::tok_ok(t),
        r is Foreign || early_mode(r->Html_0),
    ensures
        app_ok(r, p, t, apply_rules(env, r, p, t)),
{
    hide(mode_initial);
    hide(mode_before_html);
    hide(mode_before_head);
    hide(mode_in_head);
    hide(mode_in_head_noscript);
    hide(mode_after_head);
    hide(mode_in_body);
    hide(mode_text);
    hide(mode_in_table);
    hide(mode_in_table_text);
    hide(mode_in_caption);
    hide(mode_in_column_group);
    hide(mode_in_table_body);
    hide(mode_in_row);
    hide(mode_in_cell);
    hide(mode_in_template);
    hide(mode_after_body);
    hide(mode_in_frameset);
    hide(mode_after_frameset);
    hide(mode_after_after_body);
    hide(mode_after_after_frameset);
    hide(foreign_content);
    let o = apply_rules(env, r, p, t);
    match r {
        Rules::Foreign => {
            lemma_foreign_content(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Rules::Html(m) => match m {
            Mode::Initial => {
                lemma_mode_initial(env, p, t);
                lemma_quiet_ok(r, p, t, o);
            },
            Mode::BeforeHtml => lemma_mode_before_html(env, p, t),
            Mode::BeforeHead => lemma_mode_before_head(env, p, t),
            Mode::InHead => {
                lemma_mode_in_head(env, p, t);
                lemma_quiet_ok(r, p, t, o);
            },
            Mode::InHeadNoscript => {
                lemma_mode_in_head_noscript(env, p, t);
                lemma_quiet_ok(r, p, t, o);
            },
            Mode::AfterHead => lemma_mode_after_head(env, p, t),
            Mode::InBody => {
                lemma_mode_in_body(env, p, t);
                lemma_quiet_ok(r, p, t, o);
            },
            Mode::Text => {
                lemma_mode_text(env, p, t);
                lemma_quiet_ok(r, p, t, o);
            },
            Mode::InTable => lemma_mode_in_table(env, p, t),
            Mode::InTableText => lemma_mode_in_table_text(env, p, t),
            _ => {},
        },
    }
}

/// [`lemma_apply_rules`] for the modes other than the [`early_mode`]s.
#[verifier::spinoff_prover]
pub proof fn lemma_apply_late(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        st(p),
        !p.stopped,
        crate::termination::modes_ok(p),
        crate::termination::rules_ok(r, p),
        rooted_needs(r, p),
        crate::exec::modes::initial::tok_ok(t),
        r is Html && !early_mode(r->Html_0),
    ensures
        app_ok(r, p, t, apply_rules(env, r, p, t)),
{
    hide(mode_initial);
    hide(mode_before_html);
    hide(mode_before_head);
    hide(mode_in_head);
    hide(mode_in_head_noscript);
    hide(mode_after_head);
    hide(mode_in_body);
    hide(mode_text);
    hide(mode_in_table);
    hide(mode_in_table_text);
    hide(mode_in_caption);
    hide(mode_in_column_group);
    hide(mode_in_table_body);
    hide(mode_in_row);
    hide(mode_in_cell);
    hide(mode_in_template);
    hide(mode_after_body);
    hide(mode_in_frameset);
    hide(mode_after_frameset);
    hide(mode_after_after_body);
    hide(mode_after_after_frameset);
    hide(foreign_content);
    let o = apply_rules(env, r, p, t);
    let m = r->Html_0;
    match m {
        Mode::InCaption => {
            lemma_mode_in_caption(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::InColumnGroup => {
            lemma_mode_in_column_group(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::InTableBody => lemma_mode_in_table_body(env, p, t),
        Mode::InRow => {
            lemma_mode_in_row(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::InCell => {
            lemma_mode_in_cell(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::InTemplate => {
            lemma_mode_in_template(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::AfterBody => {
            lemma_mode_after_body(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::InFrameset => {
            lemma_mode_in_frameset(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::AfterFrameset => {
            lemma_mode_after_frameset(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        Mode::AfterAfterBody | Mode::AfterAfterFrameset => {
            lemma_mode_after_after(env, p, t);
            lemma_quiet_ok(r, p, t, o);
        },
        _ => {},
    }
}

/// Every rule application of a running parser (with `termination::modes_ok`
/// and `termination::rules_ok`, `invariant::rooted_needs`, and a tagged
/// token) satisfies [`app_ok`].
pub proof fn lemma_apply_rules(env: EncFns, r: Rules, p: Parser, t: Tok)
    requires
        st(p),
        !p.stopped,
        crate::termination::modes_ok(p),
        crate::termination::rules_ok(r, p),
        rooted_needs(r, p),
        crate::exec::modes::initial::tok_ok(t),
    ensures
        app_ok(r, p, t, apply_rules(env, r, p, t)),
{
    if r is Foreign || early_mode(r->Html_0) {
        lemma_apply_early(env, r, p, t);
    } else {
        lemma_apply_late(env, r, p, t);
    }
}

/// The node budget of a rule application: the growth budget and six per
/// template insertion mode and for an `image` token (which pay for the
/// implicit elements the token can still create), [`flush`], and what
/// handling the token may create ([`done_max`] and two per entry of the
/// list).
pub open spec fn pot(r: Rules, p: Parser, t: Tok) -> nat {
    crate::termination::growth(r, t) + 6 * p.template_modes.len() + 6 * crate::termination::img(t) + flush(p, t) + 2
        * p.formatting.len() + done_max()
}

/// A ranked edge ([`crate::termination::decreases_to`]) that satisfies
/// [`edge_nodes`] spends its new nodes from the budget.
pub proof fn lemma_edge_pot(r: Rules, p: Parser, t: Tok, r2: Rules, q: Parser, t2: Tok)
    requires
        edge_nodes(r, p, t, r2, q, t2),
        crate::termination::decreases_to(r, p, t, r2, q, t2),
    ensures
        q.doc.nodes.len() + pot(r2, q, t2) <= p.doc.nodes.len() + pot(r, p, t),
{
    crate::termination::lemma_components_bounded(r, t);
    crate::termination::lemma_components_bounded(r2, t2);
}

/// The run of rule applications keeps [`st`] and, with [`fx`], creates at
/// most [`pot`] nodes.
pub proof fn lemma_run(env: EncFns, p: Parser, t: Tok, r: Rules, fuel: nat)
    requires
        st(p),
        !p.stopped,
        crate::termination::modes_ok(p),
        crate::termination::rules_ok(r, p),
        crate::exec::modes::initial::tok_ok(t),
        run_needs(env, p, t, r, fuel),
        run(env, p, t, r, fuel) is Some,
    ensures
        kpu(p, run(env, p, t, r, fuel)->Some_0),
        fx(p) ==> run(env, p, t, r, fuel)->Some_0.doc.nodes.len() <= p.doc.nodes.len() + pot(r, p, t),
    decreases fuel,
{
    hide(apply_rules);
    hide(pot);
    let o = apply_rules(env, r, p, t);
    lemma_apply_rules(env, r, p, t);
    crate::termination::lemma_rules_edges(env, r, p, t);
    crate::exec::step::lemma_rules_tok(env, r, p, t);
    let q = run(env, p, t, r, fuel)->Some_0;
    reveal(pot);
    match o {
        Outcome::Done(q1) => {},
        Outcome::Reprocess(q1, t2) => {
            if !q1.stopped {
                let r2 = Rules::Html(q1.mode);
                crate::exec::step::lemma_tok_next_ok(t, t2);
                lemma_kpu(p, q1);
                lemma_run(env, q1, t2, r2, (fuel - 1) as nat);
                lemma_kpu_trans(p, q1, q);
                if fx(p) {
                    lemma_edge_pot(r, p, t, r2, q1, t2);
                }
            }
        },
        Outcome::Using(m, q1, t2) => {
            if !q1.stopped {
                let r2 = Rules::Html(m);
                crate::exec::step::lemma_tok_next_ok(t, t2);
                lemma_kpu(p, q1);
                lemma_run(env, q1, t2, r2, (fuel - 1) as nat);
                lemma_kpu_trans(p, q1, q);
                if fx(p) {
                    lemma_edge_pot(r, p, t, r2, q1, t2);
                }
            }
        },
    }
}

/// [`st`] from its parts.
pub proof fn lemma_st_intro(p: Parser)
    requires
        dom::wf(p.doc),
        ids_in_doc(p),
        p.stopped || head_ok(p),
    ensures
        st(p),
{
    reveal(st);
}

/// One `dispatch` step keeps [`st`] and, with [`fx`], creates at most
/// [`pot`] of its first rule application nodes, and at most
/// `44 + 6 T + 2 F + P (F + 1)`.
pub proof fn lemma_dispatch(env: EncFns, p: Parser, token: Token)
    requires
        parser_wf(p),
        p.stopped || head_ok(p),
        dispatch_needs(env, p, token),
    ensures
        kpu(p, dispatch(env, p, token).0),
        fx(p) ==> dispatch(env, p, token).0.doc.nodes.len() <= p.doc.nodes.len() + 44 + 6 * p.template_modes.len() + 2
            * p.formatting.len() + p.pending_table_text.len() * (p.formatting.len() + 1),
{
    hide(run);
    hide(run_needs);
    hide(dispatcher);
    hide(classify);
    hide(tree_construction);
    hide(pot);
    let p0 = Parser { actions: seq![], tokenizer: None, ..p };
    lemma_st_intro(p);
    lemma_kp_refl(p);
    lemma_kp_fields(p, p, p0, 0);
    lemma_kp(p, p0, 0);
    lemma_kp_kpu(p, p0, 0);
    if p0.stopped {
        return;
    }
    let p1 = Parser { skip_lf: false, ..p0 };
    lemma_kp_fields(p, p0, p1, 0);
    lemma_kp(p, p1, 0);
    lemma_kp_kpu(p, p1, 0);
    if p0.skip_lf && token == (Token::Character { c: 0x0A }) {
        return;
    }
    let t = classify(token);
    crate::reachable::run::lemma_classify_ok(token);
    let r = dispatcher(p1, t);
    crate::termination::lemma_dispatcher_rules_ok(p1, t);
    crate::termination::theorem_dispatch_total(env, p1, t);
    assert(run_needs(env, p1, t, r, fuel_bound(p1)));
    lemma_run(env, p1, t, r, fuel_bound(p1));
    let q = run(env, p1, t, r, fuel_bound(p1))->Some_0;
    reveal(tree_construction);
    assert(dispatch(env, p, token).0 == q);
    lemma_kpu_trans(p, p1, q);
    reveal(pot);
    crate::termination::lemma_components_bounded(r, t);
    let (pp, ff) = (p.pending_table_text.len() as int, p.formatting.len() as int);
    assert(flush(p1, t) <= pp * (ff + 1)) by {
        assert(0 <= pp * (ff + 1)) by (nonlinear_arith)
            requires pp >= 0, ff >= 0;
    }
}

/// **The ids of the parse state stay in the document** (Phase 4 item 4.9):
/// for every parser satisfying `parser_wf` whose head element pointer, until
/// parsing stops, names an HTML `head` element (`invariant::head_ok`, part
/// of `parser_inv`), and every token whose step meets
/// `invariant::dispatch_needs` (every rule application has the stack the
/// executable rules need; `reachable::run::lemma_dispatch_reach` proves it
/// for every parser satisfying `invariant::reachable_inv`), the new state
/// keeps `ids_in_doc` (every id on the stack of open elements and in the
/// list of active formatting elements is an element of the document with
/// the record's namespace and local name; the head and form element
/// pointers, the context and the redirection map name nodes of it) and the
/// head element pointer's fact.
///
/// That the stack's bottom entry is the `html` element when the stack is
/// not empty is not stated here: it does not follow from `parser_wf` (a
/// form element pointer naming the `html` element makes "in body"'s `form`
/// end tag remove it), and `invariant::reachable_inv`, which
/// `reachable::run::lemma_dispatch_reach` proves every step keeps, states
/// it (`invariant::shape`).
pub proof fn theorem_open_elements_in_doc(env: EncFns, p: Parser, token: Token)
    requires
        parser_wf(p),
        p.stopped || head_ok(p),
        dispatch_needs(env, p, token),
    ensures
        ids_in_doc(dispatch(env, p, token).0),
        dispatch(env, p, token).0.stopped || head_ok(dispatch(env, p, token).0),
{
    lemma_dispatch(env, p, token);
    lemma_kpu(p, dispatch(env, p, token).0);
    lemma_st(dispatch(env, p, token).0);
}

/// **The document stays well formed** (Phase 4 item 4.9), under the
/// hypotheses of [`theorem_open_elements_in_doc`]: every DOM call of the
/// step meets `clazel-dom`'s preconditions, so `clazel_dom::spec::wf`
/// holds of the new document.
pub proof fn theorem_doc_wf(env: EncFns, p: Parser, token: Token)
    requires
        parser_wf(p),
        p.stopped || head_ok(p),
        dispatch_needs(env, p, token),
    ensures
        dom::wf(dispatch(env, p, token).0.doc),
{
    lemma_dispatch(env, p, token);
    lemma_kpu(p, dispatch(env, p, token).0);
    lemma_st(dispatch(env, p, token).0);
}

/// **The stack of open elements holds distinct elements** (Phase 4 item
/// 4.9), under the hypotheses of [`theorem_open_elements_in_doc`]: if,
/// until parsing stops, no element has two entries on the stack, the step
/// keeps that (`independent::equivalence_foreign::open_distinct`). Every
/// element pushed is one the step created, whose id is new, except the
/// `head` element "after head" pushes back for the "in head" rules; it then
/// removes the last entry for it, the one it pushed.
pub proof fn theorem_open_distinct(env: EncFns, p: Parser, token: Token)
    requires
        parser_wf(p),
        p.stopped || head_ok(p),
        dispatch_needs(env, p, token),
        !p.stopped ==> crate::independent::equivalence_foreign::open_distinct(p.open),
    ensures
        !dispatch(env, p, token).0.stopped ==> crate::independent::equivalence_foreign::open_distinct(
            dispatch(env, p, token).0.open,
        ),
{
    lemma_dispatch(env, p, token);
    lemma_kpu(p, dispatch(env, p, token).0);
}

} // verus!
