//! The host invariant (`host::host_inv`) through the rules that do not go
//! by `reachable::keeps`: the "initial" and "before html" insertion modes
//! (no stack yet), and case 8 of "after head", which pushes the `head`
//! element back for the "in head" rules.
//!
//! Case 8. With the `head` element pushed back, the stack need not be
//! ordered as the document (nothing here says that the `head` element is no
//! ancestor of an entry of the stack in the "after head" mode), so the "in
//! head" rules are not followed with `host::host_step`. What they do to the
//! document for the start tags of case 8 is create an element and insert
//! it, which relates no two older nodes and makes no new node an ancestor
//! of an older one ([`wdoc`]); and the stack after the `head` element is
//! removed again is the one before, with at most the new element pushed.

#[cfg(verus_only)]
use super::hi::*;
#[cfg(verus_only)]
use super::hostinv::*;
#[cfg(verus_only)]
use crate::host::*;
#[cfg(verus_only)]
use crate::reachable::doc::*;
#[cfg(verus_only)]
use crate::reachable::helpers::*;
#[cfg(verus_only)]
use crate::reachable::{good, keeps};
#[cfg(verus_only)]
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// A node created and inserted

/// [`create`], then [`dom_insert`] of the new node below a node of the
/// document as it was: both keep the invariant, the ids of the parse state
/// in the document and its well-formedness, and the new node is
/// `host::low`.
pub proof fn lemma_host_create_insert(p: Parser, k: NodeKind, parent: NodeId, child: Option<NodeId>)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        !p.stopped ==> dom::creatable(p.doc, k) && dom::valid(p.doc, parent),
    ensures
        ({
            let (p1, n) = create(p, k);
            let p2 = dom_insert(p1, n, parent, child);
            &&& host_inv(p1)
            &&& host_inv(p2)
            &&& ids_valid(p1)
            &&& ids_valid(p2)
            &&& dom::wf(p1.doc)
            &&& dom::wf(p2.doc)
            &&& !p1.stopped ==> {
                &&& p1 == Parser { doc: p1.doc, ..p }
                &&& p2 == Parser { doc: p2.doc, ..p }
                &&& n == p.doc.nodes.len()
                &&& low(p1.doc, n)
                &&& low(p2.doc, n)
            }
        }),
{
    hide(dom::insert);
    reveal(ids_valid);
    reveal(ids_below);
    lemma_host_create(p, k);
    let (p1, n) = create(p, k);
    let p2 = dom_insert(p1, n, parent, child);
    if !p1.stopped {
        clazel_dom::lemmas::theorem_create_node_wf(p.doc, k);
        lemma_host_inv(p1);
        lemma_low_keeps(p1, n, parent);
        lemma_host_dom_insert(p1, n, parent, child);
        if insert_valid(p1.doc, n, parent, child) {
            clazel_dom::lemmas::theorem_insert_wf(p1.doc, n, parent, child);
            lemma_low_insert(p1.doc, n, parent, child);
        }
    }
}

/// "Insert a comment" at a given location whose parent is a node of the
/// document.
pub proof fn lemma_host_insert_comment(p: Parser, data: Seq<u32>, loc: Location)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        dom::valid(p.doc, loc.parent),
    ensures
        host_inv(insert_comment(p, data, Some(loc))),
{
    reveal(ids_valid);
    let l = adjusted_location(p, Some(loc));
    lemma_host_create_insert(p, NodeKind::Comment { data }, l.parent, l.child);
}

/// "Insert a processing instruction" at a given location whose parent is a
/// node of the document.
pub proof fn lemma_host_insert_pi(p: Parser, target: Seq<u32>, data: Seq<u32>, loc: Location)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        dom::valid(p.doc, loc.parent),
    ensures
        host_inv(insert_pi(p, target, data, Some(loc))),
{
    reveal(ids_valid);
    let l = adjusted_location(p, Some(loc));
    lemma_host_create_insert(p, NodeKind::ProcessingInstruction { target, data }, l.parent, l.child);
}

/// "Set the Document to" a mode.
pub proof fn lemma_host_set_document_mode(p: Parser, mode: DocumentMode)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
    ensures
        host_inv(set_document_mode(p, mode)),
{
    if !p.stopped {
        lemma_host_inv(p);
        crate::exec::insert::lemma_wf_nonempty(p.doc);
        let paths = clazel_dom::lemmas::lemma_wf_witness(p.doc);
        clazel_dom::host_acyclic_lemmas::theorem_set_mode_host_acyclic(p.doc, mode);
        lemma_set_mode_up_same(p.doc, mode);
        lemma_host_up_same(p, dom::set_mode(p.doc, mode));
    }
}

/// The DOCTYPE of the "initial" mode.
pub proof fn lemma_host_initial_doctype(
    p: Parser,
    name: Option<Seq<u32>>,
    public_id: Option<Seq<u32>>,
    system_id: Option<Seq<u32>>,
    force_quirks: bool,
)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
    ensures
        host_inv(initial_doctype(p, name, public_id, system_id, force_quirks)),
{
    hide(create);
    hide(dom_insert);
    hide(set_document_mode);
    hide(doctype_is_quirks);
    hide(doctype_is_limited_quirks);
    let k = NodeKind::DocumentType { name: or_empty(name), public_id: or_empty(public_id), system_id: or_empty(system_id) };
    crate::exec::insert::lemma_wf_nonempty(p.doc);
    lemma_host_create_insert(p, k, 0, None);
    let (p1, doctype) = create(p, k);
    let p2 = if p1.stopped || has_doctype_child(p1.doc, 0) || has_element_child(p1.doc, 0) {
        p1
    } else {
        dom_insert(p1, doctype, 0, None)
    };
    lemma_host_set_document_mode(p2, DocumentMode::Quirks);
    lemma_host_set_document_mode(p2, DocumentMode::LimitedQuirks);
}

/// The `html` element "before html" creates, inserts in the Document and
/// pushes onto the empty stack (for a token that is no `template`).
pub proof fn lemma_host_before_html(p: Parser, tt: TagTok)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        !p.stopped,
        p.open.len() == 0,
        tt.tag != Tag::Template,
        p.form is Some ==> dom::valid(p.doc, p.form->Some_0),
    ensures
        ({
            let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
            let p2 = insert_element_at(p1, e.id, Some(document_location()));
            host_inv(Parser { mode: Mode::BeforeHead, ..push(p2, e) })
        }),
{
    hide(create);
    hide(dom_insert);
    reveal(ids_valid);
    reveal(entry_ok);
    let owner = if is_form_associated(Namespace::Html, tt.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None
        && (!is_listed(Namespace::Html, tt.tag) || !has_attr(tt, name_form())) && same_tree(p.doc, 0, p.form->Some_0) {
        p.form
    } else {
        None
    };
    let k = NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: tt.name,
        attributes: tt.attrs,
        template_contents: None,
        form_owner: owner,
    };
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, 0);
    assert(p1 == create(p, k).0 && e.id == create(p, k).1);
    let l = adjusted_location(p1, Some(document_location()));
    crate::exec::insert::lemma_wf_nonempty(p.doc);
    assert(dom::valid(p.doc, l.parent)) by {
        reveal(create);
    }
    lemma_host_create_insert(p, k, l.parent, l.child);
    let p2 = insert_element_at(p1, e.id, Some(document_location()));
    assert(p2 == p1 || p2 == dom_insert(p1, e.id, l.parent, l.child));
    if !p2.stopped {
        assert(p2.open.len() == 0);
        assert(low(p2.doc, e.id));
        assert(entry_ok(p2, 0, e));
    }
    lemma_host_push(p2, e);
}

/// The "in head" `template` start tag, from a parser whose current node is
/// no `template` element, without foster parenting: the `template` element
/// is created, pushed, and inserted in the current node (the place computed
/// before the push). Stated with the few hypotheses it needs (the kill
/// certificate of the mutation that computes the place after the push, and
/// so inserts the element in its own template contents, instantiates it:
/// `mutation_lemmas::ml_template_not_in_contents`).
pub proof fn lemma_host_template_start(p: Parser, tt: TagTok)
    requires
        host_inv(p),
        ids_valid(p),
        dom::wf(p.doc),
        !p.stopped,
        !p.foster,
        p.open.len() >= 1,
        !is_html(p.open[p.open.len() - 1], Tag::Template),
        tt.tag == Tag::Template,
    ensures
        host_inv(in_head_template_start(p, tt)),
{
    hide(dom::insert);
    reveal(ids_valid);
    reveal(ids_below);
    reveal(entry_ok);
    let p1 = push_marker(p);
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    let k = NodeKind::Element {
        namespace: Some(Namespace::Html),
        prefix: None,
        local_name: tt.name,
        attributes: tt.attrs,
        template_contents: None,
        form_owner: None,
    };
    assert(!is_form_associated(Namespace::Html, Tag::Template));
    let (pc, id) = create(p2, k);
    let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, appropriate_place(p2, None).parent);
    assert(template.id == id);
    lemma_host_create(p2, k);
    if pc.stopped {
        assert(p3 == pc);
        assert(in_head_template_start(p, tt) == pc);
    } else if !dom::can_create(pc.doc, 1) {
        lemma_host_stopped(pc, stop_parsing(pc));
        assert(p3 == stop_parsing(pc));
        assert(in_head_template_start(p, tt) == p3);
    } else {
        clazel_dom::lemmas::theorem_create_node_wf(p2.doc, k);
        lemma_create_old_same(p2.doc, k);
        lemma_ctc_step(p2.doc, pc, id);
        assert(clazel_dom::contract::create_template_contents_requires(pc.doc, id));
        clazel_dom::lemmas::theorem_create_template_contents_wf(pc.doc, id);
        assert(p3 == Parser { doc: dom::create_template_contents(pc.doc, id).0, ..pc });
        let loc = appropriate_place(p3, None);
        let cur = p.open[p.open.len() - 1];
        assert(p3.open == p.open);
        assert(loc == Location { parent: cur.id, child: None });
        lemma_host_inv(p3);
        lemma_low_entry_ok(p3, template);
        lemma_host_push(p3, template);
        let p4 = push(p3, template);
        let l = adjusted_location(p4, Some(loc));
        assert(dom::valid(p.doc, l.parent));
        let n = p3.open.len() as int;
        assert forall|i: int| 0 <= i < p4.open.len() - 1 implies (#[trigger] p4.open[i]).id < id by {
            assert(p4.open[i] == p3.open[i]);
        }
        assert(p4.open[n] == template);
        lemma_low_keeps(p4, id, l.parent);
        assert forall|i: int| 0 <= i < p4.open.len() implies dom::valid(p4.doc, (#[trigger] p4.open[i]).id) by {
            if i < n {
                assert(p4.open[i] == p3.open[i]);
            }
        }
        lemma_host_dom_insert(p4, id, l.parent, l.child);
        let q = in_head_template_start(p, tt);
        assert(q == insert_element_at(p4, id, Some(loc)));
        assert(q == p4 || q == dom_insert(p4, id, l.parent, l.child));
    }
}

// ---------------------------------------------------------------------
// Case 8 of "after head"

/// The document `d2` comes from `d` by changes that keep
/// `clazel_dom::spec::host_acyclic`, make no node of `d` a host-including
/// inclusive ancestor of a node of `d` that it was not, and make no new
/// node one of a node of `d`: creating nodes, and inserting a node just
/// created below an older one.
#[verifier::opaque]
pub open spec fn wdoc(d: Document, d2: Document) -> bool {
    &&& d.nodes.len() <= d2.nodes.len()
    &&& dom::host_acyclic(d) ==> {
        &&& dom::host_acyclic(d2)
        &&& forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] dom::valid(d, a) && dom::valid(d, x) && hi(d2, a, x) ==> hi(d, a, x)
        &&& forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] a >= d.nodes.len() && dom::valid(d, x) ==> !hi(d2, a, x)
    }
}

/// [`wdoc`] is reflexive.
pub proof fn lemma_wdoc_refl(d: Document)
    ensures
        wdoc(d, d),
{
    reveal(wdoc);
    if dom::host_acyclic(d) {
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d, a, x)] a >= d.nodes.len() && dom::valid(d, x) implies !hi(d, a, x) by {
            if hi(d, a, x) {
                lemma_hi_valid(d, a, x);
            }
        }
    }
}

/// A change that keeps every step up (`hi::up_same`) and
/// `clazel_dom::spec::host_acyclic` is a [`wdoc`].
pub proof fn lemma_up_same_wdoc(d: Document, d2: Document)
    requires
        up_same(d, d2),
        dom::host_acyclic(d) ==> dom::host_acyclic(d2),
    ensures
        wdoc(d, d2),
{
    reveal(wdoc);
    if dom::host_acyclic(d) {
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] dom::valid(d, a) && dom::valid(d, x) && hi(d2, a, x) implies hi(
            d,
            a,
            x,
        ) by {
            lemma_hi_same(d, d2, a, x);
        }
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] a >= d.nodes.len() && dom::valid(d, x) implies !hi(d2, a, x) by {
            lemma_new_not_hi(d, d2, a, x);
        }
    }
}

/// A node `n` created after `d` (a [`wdoc`] `d1` of it), `host::low` in
/// `d1`, inserted below a node of `d`: the result is a [`wdoc`] of `d`.
pub proof fn lemma_wdoc_insert(d: Document, d1: Document, n: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        wdoc(d, d1),
        dom::insert_requires(d1, n, parent, child),
        n >= d.nodes.len(),
        dom::valid(d, parent),
        dom::host_acyclic(d1) ==> low(d1, n),
    ensures
        wdoc(d, dom::insert(d1, n, parent, child)),
{
    hide(dom::insert);
    reveal(wdoc);
    let d2 = dom::insert(d1, n, parent, child);
    clazel_dom::lemmas::theorem_insert_wf(d1, n, parent, child);
    if dom::host_acyclic(d) {
        let g = Set::<NodeId>::empty().insert(n);
        assert(!hi(d1, n, parent));
        assert(clazel_dom::host_acyclic_contract::insert_acyclic_requires(d1, n, parent, child));
        clazel_dom::host_acyclic_lemmas::theorem_insert_host_acyclic(d1, n, parent, child);
        lemma_insert_grafted(d1, n, parent, child);
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] dom::valid(d, a) && dom::valid(d, x) && hi(d2, a, x) implies hi(
            d,
            a,
            x,
        ) by {
            let m = lemma_hi_graft(d1, d2, g, parent, a, x);
            if m is Some {
                assert(m->Some_0 == n);
                assert(!hi(d1, n, x));
            }
            assert(hi(d1, a, x));
        }
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] a >= d.nodes.len() && dom::valid(d, x) implies !hi(d2, a, x) by {
            if hi(d2, a, x) {
                let m = lemma_hi_graft(d1, d2, g, parent, a, x);
                if m is Some {
                    assert(m->Some_0 == n);
                    assert(!hi(d1, n, x));
                }
                assert(hi(d1, a, x));
            }
        }
    }
}

/// [`wdoc`] is transitive.
pub proof fn lemma_wdoc_trans(d: Document, d1: Document, d2: Document)
    requires
        wdoc(d, d1),
        wdoc(d1, d2),
    ensures
        wdoc(d, d2),
{
    reveal(wdoc);
    if dom::host_acyclic(d) {
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] dom::valid(d, a) && dom::valid(d, x) && hi(d2, a, x) implies hi(
            d,
            a,
            x,
        ) by {
            assert(hi(d1, a, x));
        }
        assert forall|a: NodeId, x: NodeId| #![trigger hi(d2, a, x)] a >= d.nodes.len() && dom::valid(d, x) implies !hi(d2, a, x) by {
            if hi(d2, a, x) {
                if a < d1.nodes.len() {
                    assert(hi(d1, a, x));
                }
            }
        }
    }
}

/// "Create an element for a token" leaves a [`wdoc`] of the document,
/// whether or not it stops, and keeps the redirection map.
pub proof fn lemma_ceft_wdoc(p: Parser, t: TagTok, ns: Namespace, ip: NodeId)
    requires
        dom::wf(p.doc),
        p.form is Some ==> dom::valid(p.doc, p.form->Some_0),
    ensures
        wdoc(p.doc, create_element_for_token(p, t, ns, ip).0.doc),
        create_element_for_token(p, t, ns, ip).0.redirect == p.redirect,
{
    let owner = if is_form_associated(ns, t.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, t.tag) || !has_attr(t, name_form())) && same_tree(p.doc, ip, p.form->Some_0) {
        p.form
    } else {
        None
    };
    let k = NodeKind::Element {
        namespace: Some(ns),
        prefix: None,
        local_name: t.name,
        attributes: t.attrs,
        template_contents: None,
        form_owner: owner,
    };
    lemma_wdoc_refl(p.doc);
    if !p.stopped && dom::can_create(p.doc, 1) {
        let (d1, id) = dom::create_node(p.doc, k);
        clazel_dom::lemmas::theorem_create_node_wf(p.doc, k);
        lemma_create_up_same(p.doc, k);
        if dom::host_acyclic(p.doc) {
            clazel_dom::host_acyclic_lemmas::theorem_create_node_host_acyclic(p.doc, k);
        }
        lemma_up_same_wdoc(p.doc, d1);
        if ns == Namespace::Html && t.tag == Tag::Template && dom::can_create(d1, 1) {
            let d2 = dom::create_template_contents(d1, id).0;
            lemma_ctc_up_same(d1, id);
            if dom::host_acyclic(d1) {
                clazel_dom::host_acyclic_lemmas::theorem_create_template_contents_host_acyclic(d1, id);
            }
            lemma_up_same_trans(p.doc, d1, d2);
            lemma_up_same_wdoc(p.doc, d2);
        }
    }
}

/// "Insert an element at the adjusted insertion location" for the element
/// `n` just created (parser `p1`, from a parser whose document is `d0`),
/// at a place whose parent is a node of `d0`: the document stays a
/// [`wdoc`] of `d0`.
pub proof fn lemma_insert_at_wdoc(d0: Document, p1: Parser, n: NodeId, loc: Option<Location>)
    requires
        wdoc(d0, p1.doc),
        dom::wf(p1.doc),
        n >= d0.nodes.len(),
        dom::valid(d0, adjusted_location(p1, loc).parent),
        dom::host_acyclic(p1.doc) ==> low(p1.doc, n),
    ensures
        wdoc(d0, insert_element_at(p1, n, loc).doc),
        insert_element_at(p1, n, loc).redirect == p1.redirect,
        insert_element_at(p1, n, loc).open == p1.open,
        insert_element_at(p1, n, loc).stopped == p1.stopped,
{
    hide(dom::insert);
    let l = adjusted_location(p1, loc);
    if insert_element_at(p1, n, loc) != p1 {
        assert(insert_element_at(p1, n, loc) == dom_insert(p1, n, l.parent, l.child));
        if insert_valid(p1.doc, n, l.parent, l.child) {
            lemma_wdoc_insert(d0, p1.doc, n, l.parent, l.child);
        }
    }
}

/// "Insert an HTML element" (for a token other than `template`) leaves a
/// [`wdoc`] of the document, and keeps the redirection map; the element it
/// pushes is a new node.
pub proof fn lemma_insert_html_wdoc(p: Parser, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        tok_tagged(tt),
        crate::independent::equivalence_body::attrs_plain(tt.attrs),
        tt.tag != Tag::Template,
    ensures
        wdoc(p.doc, insert_html_element(p, tt).0.doc),
        insert_html_element(p, tt).0.redirect == p.redirect,
        !insert_html_element(p, tt).0.stopped ==> insert_html_element(p, tt).0.open == p.open.push(insert_html_element(p, tt).1)
            && insert_html_element(p, tt).1.id >= p.doc.nodes.len(),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    lemma_dinv(p);
    let ip = appropriate_place(p, None).parent;
    lemma_ceft_wdoc(p, tt, Namespace::Html, ip);
    lemma_ceft_keeps(p, tt, Namespace::Html, ip);
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, ip);
    if !p1.stopped {
        lemma_place_same(p, p1, None);
        lemma_keeps_good(p, p1);
        lemma_dinv(p1);
        lemma_insert_at_wdoc(p.doc, p1, e.id, None);
    } else {
        reveal(insert_element_at);
    }
}

/// A running parser that [`keeps`] made is [`good`].
pub proof fn lemma_keeps_good(p: Parser, q: Parser)
    requires
        keeps(p, q),
        !q.stopped,
    ensures
        good(q),
{
}

/// The "in head" `template` start tag leaves a [`wdoc`] of the document,
/// and keeps the redirection map; the `template` element it pushes is a
/// new node.
pub proof fn lemma_template_start_wdoc(p: Parser, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        tok_tagged(tt),
        crate::independent::equivalence_body::attrs_plain(tt.attrs),
        tt.tag == Tag::Template,
    ensures
        wdoc(p.doc, in_head_template_start(p, tt).doc),
        in_head_template_start(p, tt).redirect == p.redirect,
        !in_head_template_start(p, tt).stopped ==> in_head_template_start(p, tt).open.len() == p.open.len() + 1
            && in_head_template_start(p, tt).open.drop_last() == p.open && in_head_template_start(p, tt).open.last().id
            >= p.doc.nodes.len(),
{
    hide(create_element_for_token);
    hide(insert_element_at);
    let p1 = push_marker(p);
    lemma_push_marker_keeps(p);
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    assert(good(p2));
    lemma_dinv(p2);
    let ip = appropriate_place(p2, None).parent;
    lemma_ceft_wdoc(p2, tt, Namespace::Html, ip);
    lemma_ceft_keeps(p2, tt, Namespace::Html, ip);
    let (p3, template) = create_element_for_token(p2, tt, Namespace::Html, ip);
    let loc = appropriate_place(p3, None);
    let p4 = push(p3, template);
    if !p3.stopped {
        lemma_template_start_host(p2, p3, template);
        lemma_keeps_good(p2, p3);
        lemma_dinv(p3);
        lemma_insert_at_wdoc(p2.doc, p4, template.id, Some(loc));
        assert(p4.open.drop_last() == p.open);
    } else {
        reveal(insert_element_at);
    }
}

/// What the "in head" rules do for the start tags of "after head"'s case
/// 8, whatever the order of the stack: the document they leave is a
/// [`wdoc`] of the one before, the redirection map is kept, and an
/// element they leave on the stack is a new node.
pub proof fn lemma_in_head_case8_wdoc(env: EncFns, p: Parser, t: Tok)
    requires
        good(p),
        !p.stopped,
        crate::exec::modes::initial::tok_ok(t),
        crate::invariant::tok_plain(t),
        t is Start && after_head_in_head_tag(t->Start_0.tag),
    ensures
        match mode_in_head(env, p, t) {
            Outcome::Done(q) => wdoc(p.doc, q.doc) && q.redirect == p.redirect && (!q.stopped && q.open.len() == p.open.len() + 1
                ==> q.open.last().id >= p.doc.nodes.len()),
            _ => true,
        },
{
    hide(insert_html_element);
    hide(in_head_template_start);
    let tt = t->Start_0;
    if tt.tag == Tag::Template {
        lemma_template_start_wdoc(p, tt);
    } else {
        lemma_insert_html_wdoc(p, tt);
        let (p1, e) = insert_html_element(p, tt);
        if tt.tag == Tag::Script {
            assert(in_head_script(p, tt) == Parser {
                tokenizer: Some(TokenizerState::ScriptData),
                original_mode: p1.mode,
                mode: Mode::Text,
                ..p1
            }) by {
                reveal(insert_html_element);
            }
        }
        if !p1.stopped {
            assert(p1.open.last() == e);
        }
    }
}

/// Case 8 of "after head", the end: from a parser `p` with the invariant,
/// the "in head" rules left the document a [`wdoc`] of `p`'s and the stack
/// `p`'s with the `head` element (id `h`) pushed and at most one new
/// element after it; with the `head` element removed again the invariant
/// holds. (A stopped parser needs only its document.)
pub proof fn lemma_case8_host(p: Parser, p2: Parser, h: NodeId, hd: Elem)
    requires
        host_inv(p),
        ids_valid(p),
        !p.stopped,
        dom::valid(p.doc, h),
        hd.id == h,
        wdoc(p.doc, p2.doc),
        p2.redirect == p.redirect,
        !p2.stopped ==> p2.open == p.open.push(hd) || (p2.open.len() == p.open.len() + 2 && p2.open.drop_last() == p.open.push(hd)
            && p2.open.last().id >= p.doc.nodes.len()),
    ensures
        ({
            let i = open_index_of(p2, h);
            host_inv(
                if p2.stopped || i < 0 {
                    p2
                } else {
                    remove_open_at(p2, i)
                },
            )
        }),
{
    reveal(wdoc);
    reveal(ids_valid);
    lemma_host_inv(p);
    let d = p.doc;
    let d2 = p2.doc;
    let i = open_index_of(p2, h);
    if p2.stopped {
        lemma_host_inv_intro(p2);
    } else {
        let n = p.open.len() as int;
        let f = |e: Elem| e.id == h;
        assert(p2.open[n] == hd) by {
            if p2.open != p.open.push(hd) {
                assert(p2.open.drop_last()[n] == hd);
                assert(p2.open[n] == p2.open.drop_last()[n]);
            }
        }
        crate::exec::stack::lemma_last_index_where_found(p2.open, p2.open.len() as int, f, n);
        crate::exec::stack::lemma_last_index_where(p2.open, p2.open.len() as int, f);
        assert(i == n) by {
            if i > n {
                assert(p2.open[i] == p2.open.last());
            }
        }
        let q = remove_open_at(p2, i);
        assert forall|j: int| 0 <= j < n implies #[trigger] q.open[j] == p.open[j] by {
            if p2.open == p.open.push(hd) {
                assert(p2.open[j] == p.open[j]);
            } else {
                assert(p2.open[j] == p2.open.drop_last()[j]);
            }
        }
        assert forall|a: int, b: int| #![trigger q.open[b], q.open[a]] 0 <= a < b < q.open.len() implies !hi(
            q.doc,
            q.open[b].id,
            q.open[a].id,
        ) by {
            assert(q.open[a] == p.open[a]);
            if b < n {
                assert(q.open[b] == p.open[b]);
                assert(!hi(d, p.open[b].id, p.open[a].id));
            } else {
                assert(q.open[b] == p2.open.last());
            }
        }
        if let Some((r, fr)) = p.redirect {
            assert forall|j: int| 0 <= j < q.open.len() implies !hi(q.doc, (#[trigger] q.open[j]).id, fr) by {
                if j < n {
                    assert(q.open[j] == p.open[j]);
                    assert(!hi(d, p.open[j].id, fr));
                } else {
                    assert(q.open[j] == p2.open.last());
                }
            }
        }
        lemma_host_inv_intro(q);
    }
}

} // verus!
