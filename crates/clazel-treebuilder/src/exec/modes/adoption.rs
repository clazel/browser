//! HTML §13.2.6.4.7 the "adoption agency algorithm" over [`ParserBuf`]
//! (`spec/modes/adoption.rs`), proven equal to [`adoption_agency`] and to
//! keep [`parser_inv`].
//!
//! The spec's recursive loops are loops here: the outer loop
//! ([`aa_outer`]) runs at most 8 rounds ([`aa_outer_step`]), the inner
//! loop ([`aa_inner`]) walks node's index in the stack of open elements
//! down from furthestBlock's ([`aa_inner_step`]).
//!
//! What the steps need of the parse state beyond [`parser_inv`]: the stack
//! is rooted at the `html` element ([`stack_rooted`], for "the appropriate
//! place for inserting a node" in step 4.17), and the token is a tagged
//! formatting tag, so that formattingElement is never the `html` element
//! (step 4.9's commonAncestor exists) nor furthestBlock. The inner loop
//! only changes entries above formattingElement's, so the stack stays
//! rooted, commonAncestor stays where it is, and formattingElement and
//! furthestBlock stay on the stack and in the list ([`finish_pre`]).

use super::super::formatting::*;
#[cfg(verus_only)]
use super::super::frame::*;
use super::super::insert::*;
use super::super::stack::*;
use super::super::types::*;
#[cfg(verus_only)]
use super::in_body_start_lemmas::lemma_doc_extends_refl;
#[allow(unused_imports)]
use super::spec::*;
use clazel_dom::exec::ExecKind;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Outcomes and the bookmark

/// How the adoption agency algorithm ended ([`AdoptionOutcome`]), the
/// parser being the one it mutated in place.
pub enum ExecAdoptionOutcome {
    /// It returned.
    Done,
    /// Step 4.3: act as the "any other end tag" entry describes.
    AnyOtherEndTag,
}

/// The spec outcome of an exec outcome whose parser is `p`.
pub open spec fn adoption_outcome_view(o: ExecAdoptionOutcome, p: Parser) -> AdoptionOutcome {
    match o {
        ExecAdoptionOutcome::Done => AdoptionOutcome::Done(p),
        ExecAdoptionOutcome::AnyOtherEndTag => AdoptionOutcome::AnyOtherEndTag(p),
    }
}

/// Step 4.10's bookmark ([`Bookmark`]).
pub enum ExecBookmark {
    /// At formattingElement's position.
    FormattingElement,
    /// Immediately after the element with this id.
    After(usize),
}

impl View for ExecBookmark {
    type V = Bookmark;

    open spec fn view(&self) -> Bookmark {
        match self {
            ExecBookmark::FormattingElement => Bookmark::FormattingElement,
            ExecBookmark::After(b) => Bookmark::After(*b),
        }
    }
}

/// [`doc_extends`], hidden: its quantifiers and those of `wf` match each
/// other, so the loops' contexts carry it hidden.
#[verifier::opaque]
pub open spec fn dext(d0: Document, d1: Document) -> bool {
    doc_extends(d0, d1)
}

/// [`dext`] is transitive, also from [`doc_extends`] facts.
proof fn lemma_dext_trans(d0: Document, d1: Document, d2: Document)
    requires
        doc_extends(d0, d1) || dext(d0, d1),
        doc_extends(d1, d2) || dext(d1, d2),
    ensures
        dext(d0, d2),
{
    reveal(dext);
    lemma_doc_extends_trans(d0, d1, d2);
}

/// A well-formed document [`dext`]ends itself.
proof fn lemma_dext_refl(d: Document)
    requires
        dom::wf(d),
    ensures
        dext(d, d),
{
    reveal(dext);
    lemma_doc_extends_refl(d);
}

/// [`dext`] is [`doc_extends`].
proof fn lemma_dext_is(d0: Document, d1: Document)
    ensures
        dext(d0, d1) == doc_extends(d0, d1),
{
    reveal(dext);
}

// ---------------------------------------------------------------------
// Facts of records and sequences

/// Two records of the same node agree on namespace, name and tag.
proof fn lemma_same_node(doc: Document, a: Elem, b: Elem)
    requires
        elem_in_doc(doc, a),
        elem_in_doc(doc, b),
        elem_tagged(a),
        elem_tagged(b),
        a.id == b.id,
    ensures
        a.ns == b.ns,
        a.name == b.name,
        a.tag == b.tag,
{
}

/// A record's node is a `template` element exactly when the record is an
/// HTML `template`.
proof fn lemma_elem_template(doc: Document, e: Elem)
    requires
        elem_in_doc(doc, e),
        elem_tagged(e),
    ensures
        node_is_template(doc, e.id) == is_html(e, Tag::Template),
{
}

/// Replacing a record with an [`elem_ok`] one keeps [`open_ok`].
proof fn lemma_open_update(doc: Document, o: Seq<Elem>, i: int, e: Elem)
    requires
        open_ok(doc, o),
        elem_ok(doc, e),
        0 <= i < o.len(),
    ensures
        open_ok(doc, o.update(i, e)),
{
    assert forall|j: int| 0 <= j < o.update(i, e).len() implies elem_ok(doc, #[trigger] o.update(i, e)[j]) by {
        if j != i {
            assert(o.update(i, e)[j] == o[j]);
        }
    }
}

/// Inserting an [`elem_ok`] record keeps [`open_ok`].
proof fn lemma_open_insert(doc: Document, o: Seq<Elem>, i: int, e: Elem)
    requires
        open_ok(doc, o),
        elem_ok(doc, e),
        0 <= i <= o.len(),
    ensures
        open_ok(doc, o.insert(i, e)),
{
    o.insert_ensures(i, e);
    assert forall|j: int| 0 <= j < o.insert(i, e).len() implies elem_ok(doc, #[trigger] o.insert(i, e)[j]) by {
        if j < i {
            assert(o.insert(i, e)[j] == o[j]);
        } else if j > i {
            assert(o.insert(i, e)[(j - 1) + 1] == o[j - 1]);
        }
    }
}

/// Inserting an [`fmt_ok`] entry keeps [`fmts_ok`].
proof fn lemma_fmts_insert(doc: Document, f: Seq<Fmt>, i: int, x: Fmt)
    requires
        fmts_ok(doc, f),
        fmt_ok(doc, x),
        0 <= i <= f.len(),
    ensures
        fmts_ok(doc, f.insert(i, x)),
{
    f.insert_ensures(i, x);
    assert forall|j: int| 0 <= j < f.insert(i, x).len() implies fmt_ok(doc, #[trigger] f.insert(i, x)[j]) by {
        if j < i {
            assert(f.insert(i, x)[j] == f[j]);
        } else if j > i {
            assert(f.insert(i, x)[(j - 1) + 1] == f[j - 1]);
        }
    }
}

/// Replacing a record with one that is no `template` adds no `template`.
pub proof fn lemma_templates_in_update(o: Seq<Elem>, i: int, e: Elem, k: int)
    requires
        0 <= i < o.len(),
        k <= o.len(),
        !is_html(e, Tag::Template),
    ensures
        crate::termination::templates_in(o.update(i, e), k) <= crate::termination::templates_in(o, k),
    decreases k,
{
    if k > 0 {
        lemma_templates_in_update(o, i, e, k - 1);
        if k - 1 != i {
            assert(o.update(i, e)[k - 1] == o[k - 1]);
        }
    }
}

/// The entry at index `j` of `o.insert(i, e)`.
proof fn lemma_insert_at(o: Seq<Elem>, i: int, e: Elem, j: int)
    requires
        0 <= i <= o.len(),
        0 <= j <= o.len(),
    ensures
        o.insert(i, e)[j] == if j < i {
            o[j]
        } else if j == i {
            e
        } else {
            o[j - 1]
        },
{
    o.insert_ensures(i, e);
    if j > i {
        assert(o.insert(i, e)[(j - 1) + 1] == o[j - 1]);
    }
}

/// Inserting a record that is no `template` adds no `template`, below the
/// insertion point and above it.
pub proof fn lemma_templates_in_insert(o: Seq<Elem>, i: int, e: Elem, k: int)
    requires
        0 <= i <= o.len(),
        0 <= k <= o.len(),
        !is_html(e, Tag::Template),
    ensures
        k <= i ==> crate::termination::templates_in(o.insert(i, e), k) == crate::termination::templates_in(o, k),
        k >= i ==> crate::termination::templates_in(o.insert(i, e), k + 1) == crate::termination::templates_in(o, k),
    decreases k,
{
    let s = o.insert(i, e);
    if k > 0 {
        lemma_templates_in_insert(o, i, e, k - 1);
    }
    if k > 0 && k <= i {
        lemma_insert_at(o, i, e, k - 1);
    }
    if k <= i {
        assert(crate::termination::templates_in(s, k) == crate::termination::templates_in(o, k));
    }
    if k >= i {
        lemma_insert_at(o, i, e, k);
        if k == i {
            assert(crate::termination::templates_in(s, k) == crate::termination::templates_in(o, k));
        } else {
            assert(crate::termination::templates_in(s, k) == crate::termination::templates_in(o, k - 1));
        }
        assert(crate::termination::templates_in(s, k + 1) == crate::termination::templates_in(o, k));
    }
}

/// The parser with stack `o` and list `f` keeps [`parser_inv`] when both
/// are ok and the stack has no more `template` elements.
proof fn lemma_inv_open_fmt(p: Parser, o: Seq<Elem>, f: Seq<Fmt>)
    requires
        parser_inv(p),
        open_ok(p.doc, o),
        fmts_ok(p.doc, f),
        crate::termination::helpers_ranking::tcount(o) <= crate::termination::helpers_ranking::tcount(p.open),
    ensures
        parser_inv(Parser { open: o, formatting: f, ..p }),
{
    lemma_inv_iff(p);
    lemma_inv_iff(Parser { open: o, formatting: f, ..p });
}

/// [`fmt_last_where`] is -1 or an element entry within `from..i` that
/// satisfies `pred`.
proof fn lemma_fmt_last_where(f: Seq<Fmt>, from: int, i: int, pred: spec_fn(Elem) -> bool)
    requires
        i <= f.len(),
    ensures
        fmt_last_where(f, from, i, pred) == -1 || (from <= fmt_last_where(f, from, i, pred) < i && f[fmt_last_where(
            f,
            from,
            i,
            pred,
        )] is Entry && pred(f[fmt_last_where(f, from, i, pred)]->Entry_elem)),
    decreases i - from,
{
    if i > from && !(f[i - 1] is Entry && pred(f[i - 1]->Entry_elem)) {
        lemma_fmt_last_where(f, from, i - 1, pred);
    }
}

/// [`first_special_from`] is -1 or a special entry from index `j` on.
pub proof fn lemma_first_special_from(open: Seq<Elem>, j: int)
    requires
        j >= 0,
    ensures
        first_special_from(open, j) == -1 || (j <= first_special_from(open, j) < open.len() && is_special(
            open[first_special_from(open, j)],
        )),
    decreases open.len() - j,
{
    if j < open.len() && !is_special(open[j]) {
        lemma_first_special_from(open, j + 1);
    }
}

/// [`fmt_index_of`] is -1 or an element entry of that id below `i`.
pub proof fn lemma_fmt_index_of(f: Seq<Fmt>, i: int, id: NodeId)
    requires
        i <= f.len(),
    ensures
        fmt_index_of(f, i, id) == -1 || (0 <= fmt_index_of(f, i, id) < i && f[fmt_index_of(f, i, id)] is Entry && f[fmt_index_of(
            f,
            i,
            id,
        )]->Entry_elem.id == id),
    decreases i,
{
    if i > 0 && !(f[i - 1] is Entry && f[i - 1]->Entry_elem.id == id) {
        lemma_fmt_index_of(f, i - 1, id);
    }
}

/// [`fmt_index_of`] finds an entry of that id if there is one.
pub proof fn lemma_fmt_index_of_found(f: Seq<Fmt>, i: int, id: NodeId, k: int)
    requires
        0 <= k < i <= f.len(),
        f[k] is Entry && f[k]->Entry_elem.id == id,
    ensures
        fmt_index_of(f, i, id) >= 0,
    decreases i,
{
    if !(f[i - 1] is Entry && f[i - 1]->Entry_elem.id == id) {
        lemma_fmt_index_of_found(f, i - 1, id, k);
    }
}

/// Popping until a record satisfying `f` has been popped leaves the stack
/// below the last such record.
proof fn lemma_pop_until_where_at(p: Parser, f: spec_fn(Elem) -> bool)
    requires
        last_index_where(p.open, p.open.len() as int, f) >= 0,
    ensures
        pop_until_where(p, f) == (Parser {
            open: p.open.subrange(0, last_index_where(p.open, p.open.len() as int, f)),
            ..p
        }),
    decreases p.open.len(),
{
    let n = p.open.len() as int;
    assert(n > 0);
    if f(current_node(p)) {
        assert(p.open.drop_last() =~= p.open.subrange(0, n - 1));
    } else {
        let q = pop(p);
        assert(q.open == p.open.drop_last());
        lemma_last_index_where(p.open, n, f);
        assert(last_index_where(p.open, n, f) == last_index_where(p.open, n - 1, f));
        assert forall|j: int| 0 <= j < n - 1 implies q.open[j] == p.open[j] by {}
        lemma_last_index_where_same(q.open, p.open, n - 1, f);
        lemma_pop_until_where_at(q, f);
        let k = last_index_where(p.open, n, f);
        assert(q.open.subrange(0, k) =~= p.open.subrange(0, k));
    }
}

/// [`last_index_where`] reads only the first `i` records.
proof fn lemma_last_index_where_same(a: Seq<Elem>, b: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        i <= a.len(),
        i <= b.len(),
        forall|j: int| 0 <= j < i ==> a[j] == b[j],
    ensures
        last_index_where(a, i, f) == last_index_where(b, i, f),
    decreases i,
{
    if i > 0 {
        lemma_last_index_where_same(a, b, i - 1, f);
    }
}

// ---------------------------------------------------------------------
// Moving the children

/// Moving the children of `from` to `to` extends the document when `to` is
/// no `template` without template contents.
proof fn lemma_reparent_extends(doc: Document, from: NodeId, to: NodeId)
    requires
        dom::reparent_children_requires(doc, from, to),
        node_is_template(doc, to) ==> has_template_contents(doc, to),
    ensures
        doc_extends(doc, dom::reparent_children(doc, from, to)),
{
    clazel_dom::lemmas::theorem_reparent_children_wf(doc, from, to);
    let d = dom::reparent_children(doc, from, to);
    assert forall|i: int| 0 <= i < doc.nodes.len() implies kind_kept(doc.nodes[i].kind, #[trigger] d.nodes[i].kind) by {
        assert(d.nodes[i].kind == doc.nodes[i].kind);
    }
    assert forall|n: NodeId|
        dom::valid(d, n) && #[trigger] node_is_template(d, n) && d.nodes[n as int].children.len() > 0 implies has_template_contents(d, n)
        || (n < doc.nodes.len() && doc.nodes[n as int].children.len() > 0) by {
        assert(d.nodes[n as int].kind == doc.nodes[n as int].kind);
        assert(node_is_template(doc, n));
        if n == to {
            assert(has_template_contents(doc, n));
        } else if n != from {
            let c = d.nodes[n as int].children[0];
            let paths = clazel_dom::lemmas::lemma_wf_witness(d);
            assert(dom::wf_with(d, paths));
            assert(d.nodes[c as int].parent == Some(n));
            assert(c < doc.nodes.len());
            if dom::children(doc, from).contains(c) {
                let j = choose|j: int| 0 <= j < dom::children(doc, from).len() && dom::children(doc, from)[j] == c;
                assert(dom::parent(d, dom::children(doc, from)[j]) == Some(to));
            } else {
                assert(d.nodes[c as int].parent == doc.nodes[c as int].parent);
                let paths0 = clazel_dom::lemmas::lemma_wf_witness(doc);
                assert(dom::wf_with(doc, paths0));
                assert(doc.nodes[c as int].parent is Some);
                assert(doc.nodes[n as int].children.contains(c));
            }
        }
    }
}

/// [`dom_reparent_children`]: "take all of the child nodes of `from` and
/// append them to `to`" when the DOM accepts it. `to` must not be a
/// `template` without template contents.
pub fn dom_reparent_children_exec(p: &mut ParserBuf, from: usize, to: usize)
    requires
        parser_inv(old(p)@),
        node_is_template(old(p)@.doc, to) ==> has_template_contents(old(p)@.doc, to),
    ensures
        final(p)@ == dom_reparent_children(old(p)@, from, to),
        parser_inv(final(p)@),
        final(p)@ == (Parser { doc: final(p)@.doc, ..old(p)@ }),
        doc_extends(old(p)@.doc, final(p)@.doc),
{
    proof {
        lemma_inv_iff(old(p)@);
        lemma_doc_extends_refl(old(p)@.doc);
    }
    if p.stopped {
        return ;
    }
    let len = p.arena.len();
    if from >= len || to >= len || from == to {
        return ;
    }
    let ok_from = matches!(
        p.arena.kind(from),
        ExecKind::Document { .. } | ExecKind::Element { .. } | ExecKind::DocumentFragment { .. }
    );
    let ok_to = matches!(
        p.arena.kind(to),
        ExecKind::Document { .. } | ExecKind::Element { .. } | ExecKind::DocumentFragment { .. }
    );
    proof {
        lemma_inv_iff(old(p)@);
    }
    if !ok_from || !ok_to || p.arena.is_inclusive_ancestor(from, to) {
        return ;
    }
    proof {
        lemma_reparent_extends(old(p)@.doc, from, to);
    }
    p.arena.reparent_children(from, to);
    proof {
        lemma_inv_doc(old(p)@, p@.doc);
    }
}

// ---------------------------------------------------------------------
// The searches of step 4

/// [`fmt_last_where`] over `from..f.len()` for the name `name`.
fn fmt_last_named_exec(f: &[ExecFmt], from: usize, name: &[u32], Ghost(pred): Ghost<spec_fn(Elem) -> bool>) -> (r: Option<usize>)
    requires
        from <= f@.len(),
        forall|e: Elem| #[trigger] pred(e) == (e.name == name@),
    ensures
        match r {
            Some(k) => k < f@.len() && k as int == fmt_last_where(fmts_view(f@), from as int, f@.len() as int, pred),
            None => fmt_last_where(fmts_view(f@), from as int, f@.len() as int, pred) == -1,
        },
{
    let ghost v = fmts_view(f@);
    let mut i = f.len();
    while i > from
        invariant
            from <= i <= f@.len(),
            v == fmts_view(f@),
            forall|e: Elem| #[trigger] pred(e) == (e.name == name@),
            fmt_last_where(v, from as int, f@.len() as int, pred) == fmt_last_where(v, from as int, i as int, pred),
        decreases i,
    {
        let x = match f.get(i.saturating_sub(1)) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(x@ == v[i - 1]);
        }
        match x {
            ExecFmt::Entry { elem, .. } if super::super::names::u32s_eq(elem.name.as_slice(), name) => {
                return Some(i.saturating_sub(1));
            },
            _ => {},
        }
        i = i.saturating_sub(1);
    }
    None
}

/// [`first_special_from`].
fn first_special_from_exec(open: &[ExecElem], j: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < open@.len() && k as int == first_special_from(elems_view(open@), j as int),
            None => first_special_from(elems_view(open@), j as int) == -1,
        },
{
    let ghost o = elems_view(open@);
    let mut i = j;
    while i < open.len()
        invariant
            j <= i,
            o == elems_view(open@),
            first_special_from(o, j as int) == first_special_from(o, i as int),
        decreases open@.len() - i,
    {
        let e = match open.get(i) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(e@ == o[i as int]);
        }
        if is_special_exec(e) {
            return Some(i);
        }
        // Never saturates: i < open.len().
        i = i.saturating_add(1);
    }
    None
}

// ---------------------------------------------------------------------
// The inner loop

/// The element of id `id` is on the stack at index `from` or above.
pub open spec fn on_stack_from(open: Seq<Elem>, from: int, id: NodeId) -> bool {
    exists|j: int| from <= j < open.len() && (#[trigger] open[j]).id == id
}

/// The element of id `id` has an entry in the list.
pub open spec fn in_list(f: Seq<Fmt>, id: NodeId) -> bool {
    exists|j: int| 0 <= j < f.len() && (#[trigger] f[j]) is Entry && f[j]->Entry_elem.id == id
}

/// What steps 4.17 to 4.29 need: formattingElement `fe` at index `fe_idx
/// >= 1` of a rooted stack, commonAncestor `ca` immediately above it,
/// furthestBlock (id `fb_id`) below it, and formattingElement still in the
/// list.
pub open spec fn finish_pre(p: Parser, fe: Elem, ca: Elem, fb_id: NodeId, fe_idx: int) -> bool {
    &&& parser_inv(p)
    &&& !p.stopped
    &&& stack_rooted(p)
    &&& 1 <= fe_idx < p.open.len()
    &&& p.open[fe_idx].id == fe.id
    &&& p.open[fe_idx - 1] == ca
    &&& on_stack_from(p.open, fe_idx + 1, fb_id)
    &&& in_list(p.formatting, fe.id)
    &&& fe.id != fb_id
}

/// The inner loop's invariant, with node at index `node_idx`.
pub open spec fn inner_inv(p: Parser, fe: Elem, ca: Elem, fb_id: NodeId, fe_idx: int, node_idx: int) -> bool {
    &&& finish_pre(p, fe, ca, fb_id, fe_idx)
    &&& fe_idx < node_idx <= p.open.len()
    &&& on_stack_from(p.open, node_idx, fb_id)
}

/// [`aa_inner`], hidden so that the loops' contexts stay small.
#[verifier::opaque]
pub open spec fn ai(p: Parser, fe: Elem, ca: Elem, node_idx: int, last: Elem, counter: nat, bm: Bookmark) -> (
    Parser,
    Elem,
    Bookmark,
) {
    aa_inner(p, fe, ca, node_idx, last, counter, bm)
}

/// Step 4.16.4 with innerLoopCounter `counter` (already incremented).
#[verifier::opaque]
pub open spec fn inner_drop(p: Parser, node_id: NodeId, counter: nat) -> Parser {
    if counter > 3 && in_formatting(p, node_id) {
        Parser { formatting: p.formatting.remove(fmt_index_of(p.formatting, p.formatting.len() as int, node_id)), ..p }
    } else {
        p
    }
}

/// Steps 4.16.6 to 4.16.11 for node (id `node_id`) at index `i`: the
/// parser, lastNode and the bookmark after them (the parser stopped if the
/// creation stopped it).
#[verifier::opaque]
pub open spec fn inner_replace(p1: Parser, ca: Elem, i: int, node_id: NodeId, last: Elem, bm: Bookmark) -> (
    Parser,
    Elem,
    Bookmark,
) {
    let k = fmt_index_of(p1.formatting, p1.formatting.len() as int, node_id);
    let token = p1.formatting[k]->Entry_token;
    let (p2, new_element) = create_element_for_token(p1, token, Namespace::Html, ca.id);
    if p2.stopped {
        (p2, last, bm)
    } else {
        let p3 = Parser {
            formatting: p2.formatting.update(k, Fmt::Entry { elem: new_element, token }),
            open: p2.open.update(i, new_element),
            ..p2
        };
        let b = match bm {
            Bookmark::FormattingElement => Bookmark::After(new_element.id),
            Bookmark::After(b) => Bookmark::After(b),
        };
        (dom_insert(p3, last.id, new_element.id, None), new_element, b)
    }
}

/// One round of [`aa_inner`], in terms of the hidden parts.
pub proof fn lemma_ai_unfold(p: Parser, fe: Elem, ca: Elem, node_idx: int, last: Elem, counter: nat, bm: Bookmark)
    requires
        !p.stopped,
        node_idx > 0,
    ensures
        ai(p, fe, ca, node_idx, last, counter, bm) == ({
            let c = counter + 1;
            let i = node_idx - 1;
            let node_id = p.open[i].id;
            if node_id == fe.id {
                (p, last, bm)
            } else {
                let p1 = inner_drop(p, node_id, c);
                if !in_formatting(p1, node_id) {
                    ai(remove_open_at(p1, i), fe, ca, i, last, c, bm)
                } else {
                    let r = inner_replace(p1, ca, i, node_id, last, bm);
                    if r.0.stopped {
                        r
                    } else {
                        ai(r.0, fe, ca, i, r.1, c, r.2)
                    }
                }
            }
        }),
{
    reveal(ai);
    reveal(inner_drop);
    reveal(inner_replace);
}

/// Step 4.16.4 ([`inner_drop`]).
fn aa_inner_drop(p: &mut ParserBuf, node_id: usize, counter: usize, Ghost(fe_id): Ghost<NodeId>)
    requires
        parser_inv(old(p)@),
        in_list(old(p)@.formatting, fe_id),
        node_id != fe_id,
    ensures
        final(p)@ == inner_drop(old(p)@, node_id, counter as nat),
        parser_inv(final(p)@),
        in_list(final(p)@.formatting, fe_id),
        final(p)@.open == old(p)@.open,
        final(p)@.stopped == old(p)@.stopped,
        final(p)@.doc == old(p)@.doc,
{
    reveal(inner_drop);
    let ghost p0 = p@;
    let found = if counter > 3 {
        fmt_index_of_exec(p.formatting.as_slice(), p.formatting.len(), node_id)
    } else {
        None
    };
    if let Some(k) = found {
        let ghost v = p.formatting@;
        let _ = p.formatting.remove(k);
        proof {
            assert(fmts_view(p.formatting@) =~= fmts_view(v).remove(k as int));
            lemma_inv_iff(p0);
            lemma_fmt_index_of(p0.formatting, p0.formatting.len() as int, node_id);
            lemma_fmts_remove(p0.doc, p0.formatting, k as int);
            lemma_inv_iff(p@);
            let j = choose|j: int|
                0 <= j < p0.formatting.len() && (#[trigger] p0.formatting[j]) is Entry && p0.formatting[j]->Entry_elem.id
                    == fe_id;
            assert(j != k);
            if j < k {
                assert(p@.formatting[j] == p0.formatting[j]);
            } else {
                assert(p@.formatting[j - 1] == p0.formatting[j]);
            }
        }
    }
}

/// Steps 4.16.6 to 4.16.11 ([`inner_replace`]) for node at index `i`, its
/// entry being at index `k` of the list.
fn aa_inner_replace(
    p: &mut ParserBuf,
    ca: &ExecElem,
    i: usize,
    k: usize,
    Ghost(node_id): Ghost<NodeId>,
    lb: (ExecElem, ExecBookmark),
    Ghost(fe_id): Ghost<NodeId>,
) -> (r: (ExecElem, ExecBookmark))
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        i < old(p)@.open.len(),
        k as int == fmt_index_of(old(p)@.formatting, old(p)@.formatting.len() as int, node_id),
        k < old(p)@.formatting.len(),
        elem_ok(old(p)@.doc, ca@),
        in_list(old(p)@.formatting, fe_id),
        node_id != fe_id,
    ensures
        (final(p)@, r.0@, r.1@) == inner_replace(old(p)@, ca@, i as int, node_id, lb.0@, lb.1@),
        parser_inv(final(p)@),
        !final(p)@.stopped ==> final(p)@.open == old(p)@.open.update(i as int, r.0@),
        in_list(final(p)@.formatting, fe_id),
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(tag_of);
    hide(dom::wf);
    reveal(inner_replace);
    let (last, bm) = lb;
    let ghost p1 = p@;
    proof {
        lemma_inv_iff(p1);
        lemma_fmt_index_of(p1.formatting, p1.formatting.len() as int, node_id);
        assert(fmt_ok(p1.doc, p1.formatting[k as int]));
    }
    let token = match p.formatting.get(k) {
        Some(ExecFmt::Entry { token, .. }) => copy_tagtok(token),
        _ => vstd::pervasive::unreached(),
    };
    // 4.16.6 "Create an element for the token for which the element node
    // was created, in the HTML namespace, with commonAncestor as the
    // intended parent"
    let ne = create_element_for_token_exec(p, &token, Namespace::Html, ca.id);
    proof {
        lemma_dext_is(p1.doc, p@.doc);
    }
    if p.stopped {
        return (last, bm);
    }
    let ghost p2 = p@;
    let ghost x = Fmt::Entry { elem: ne@, token: token@ };
    proof {
        lemma_inv_iff(p2);
        lemma_elem_template(p2.doc, ne@);
        assert(fmt_ok(p2.doc, x));
    }
    let ne_id = ne.id;
    // "replace the entry for node in the list of active formatting elements
    // with an entry for the new element, replace the entry for node in the
    // stack of open elements with an entry for the new element"
    let ghost vf = p.formatting@;
    let ghost vo = p.open@;
    p.formatting.set(k, ExecFmt::Entry { elem: copy_elem(&ne), token });
    p.open.set(i, copy_elem(&ne));
    proof {
        assert(fmts_view(p.formatting@) =~= fmts_view(vf).update(k as int, x));
        assert(elems_view(p.open@) =~= elems_view(vo).update(i as int, ne@));
        lemma_fmts_update(p2.doc, p2.formatting, k as int, x);
        lemma_open_update(p2.doc, p2.open, i as int, ne@);
        lemma_templates_in_update(p2.open, i as int, ne@, p2.open.len() as int);
        lemma_inv_open_fmt(p2, p@.open, p@.formatting);
        assert(p@ == (Parser { open: p@.open, formatting: p@.formatting, ..p2 }));
        let jf = choose|jf: int|
            0 <= jf < p1.formatting.len() && (#[trigger] p1.formatting[jf]) is Entry && p1.formatting[jf]->Entry_elem.id == fe_id;
        assert(jf != k);
        assert(p@.formatting[jf] == p1.formatting[jf]);
    }
    // 4.16.7 "If bookmarkMoved is false, then move the aforementioned
    // bookmark to be immediately after the new node …"
    let bm2 = match bm {
        ExecBookmark::FormattingElement => ExecBookmark::After(ne_id),
        ExecBookmark::After(b) => ExecBookmark::After(b),
    };
    // 4.16.11 "Keep": "append lastNode to node. Set lastNode to node."
    let ghost p3 = p@;
    proof {
        lemma_inv_iff(p3);
        lemma_elem_template(p3.doc, ne@);
    }
    dom_insert_exec(p, last.id, ne_id, None);
    proof {
        lemma_dext_trans(p1.doc, p3.doc, p@.doc);
    }
    (ne, bm2)
}

/// The inner loop's fixed records: formattingElement and commonAncestor.
struct InnerCtx<'a> {
    fe: &'a ExecElem,
    ca: &'a ExecElem,
}

/// One round of step 4.16 with node at index `node_idx`, lastNode `last`
/// and innerLoopCounter `counter`: `(true, lastNode, bookmark)` to go on
/// with node at index `node_idx - 1`, `(false, …)` when the loop is done.
fn aa_inner_step(
    p: &mut ParserBuf,
    cx: &InnerCtx,
    Ghost(fb_id): Ghost<NodeId>,
    Ghost(fe_idx): Ghost<int>,
    node_idx: usize,
    lb: (ExecElem, ExecBookmark),
    counter: usize,
) -> (r: (bool, ExecElem, ExecBookmark))
    requires
        inner_inv(old(p)@, cx.fe@, cx.ca@, fb_id, fe_idx, node_idx as int),
        counter < usize::MAX,
    ensures
        r.0 ==> inner_inv(final(p)@, cx.fe@, cx.ca@, fb_id, fe_idx, node_idx - 1) && ai(
            final(p)@,
            cx.fe@,
            cx.ca@,
            node_idx - 1,
            r.1@,
            (counter + 1) as nat,
            r.2@,
        ) == ai(old(p)@, cx.fe@, cx.ca@, node_idx as int, lb.0@, counter as nat, lb.1@),
        !r.0 ==> (final(p)@, r.1@, r.2@) == ai(old(p)@, cx.fe@, cx.ca@, node_idx as int, lb.0@, counter as nat, lb.1@)
            && parser_inv(final(p)@) && (final(p)@.stopped || finish_pre(final(p)@, cx.fe@, cx.ca@, fb_id, fe_idx)),
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(tag_of);
    hide(dom::wf);
    let fe = cx.fe;
    let ca = cx.ca;
    let (last, bm) = lb;
    let ghost p0 = p@;
    proof {
        lemma_ai_unfold(p0, fe@, ca@, node_idx as int, last@, counter as nat, bm@);
        lemma_inv_iff(p0);
        lemma_dext_refl(p0.doc);
    }
    // 4.16.1 "Increment innerLoopCounter by 1."
    let counter = counter.saturating_add(1);
    // 4.16.2 "Let node be the element immediately above node in the stack of
    // open elements …"
    let i = node_idx.saturating_sub(1);
    let node_id = match p.open.get(i) {
        Some(e) => e.id,
        None => vstd::pervasive::unreached(),
    };
    // 4.16.3 "If node is formattingElement, then break."
    if node_id == fe.id {
        proof {
            let j = choose|j: int| node_idx <= j < p0.open.len() && (#[trigger] p0.open[j]).id == fb_id;
            assert(fe_idx + 1 <= j);
        }
        return (false, last, bm);
    }
    assert(i > fe_idx);
    // 4.16.4
    aa_inner_drop(p, node_id, counter, Ghost(fe@.id));
    let ghost p1 = p@;
    match fmt_index_of_exec(p.formatting.as_slice(), p.formatting.len(), node_id) {
        None => {
            // 4.16.5 "If node is not in the list of active formatting
            // elements, then remove node from the stack of open elements and
            // continue."
            remove_open_at_exec(p, i);
            proof {
                p1.open.remove_ensures(i as int);
                let j = choose|j: int| node_idx <= j < p1.open.len() && (#[trigger] p1.open[j]).id == fb_id;
                assert(p@.open[j - 1] == p1.open[j]);
                assert(p@.open[fe_idx] == p1.open[fe_idx]);
                assert(p@.open[fe_idx - 1] == p1.open[fe_idx - 1]);
                assert(p@.open[0] == p1.open[0]);
            }
            (true, last, bm)
        },
        Some(k) => {
            proof {
                lemma_inv_iff(p1);
                assert(elem_ok(p1.doc, p1.open[fe_idx - 1]));
            }
            // 4.16.6 to 4.16.11
            let (ne, bm2) = aa_inner_replace(p, ca, i, k, Ghost(node_id), (last, bm), Ghost(fe@.id));
            if p.stopped {
                return (false, ne, bm2);
            }
            proof {
                let j = choose|j: int| node_idx <= j < p1.open.len() && (#[trigger] p1.open[j]).id == fb_id;
                assert(p@.open[j] == p1.open[j]);
                assert(p@.open[fe_idx] == p1.open[fe_idx]);
                assert(p@.open[fe_idx - 1] == p1.open[fe_idx - 1]);
                assert(p@.open[0] == p1.open[0]);
            }
            (true, ne, bm2)
        },
    }
}

/// A parser satisfying [`inner_inv`] has a document that extends itself.
proof fn lemma_inner_refl(p: Parser, fe: Elem, ca: Elem, fb_id: NodeId, fe_idx: int, node_idx: int)
    requires
        inner_inv(p, fe, ca, fb_id, fe_idx, node_idx),
    ensures
        dext(p.doc, p.doc),
{
    lemma_dext_refl(p.doc);
}

/// Step 4.16, the inner loop, from furthestBlock at index `fb_idx`.
fn aa_inner_exec(p: &mut ParserBuf, fe: &ExecElem, ca: &ExecElem, fb: &ExecElem, fb_idx: usize, Ghost(fe_idx): Ghost<int>) -> (r: (
    ExecElem,
    ExecBookmark,
))
    requires
        inner_inv(old(p)@, fe@, ca@, fb@.id, fe_idx, fb_idx as int),
    ensures
        (final(p)@, r.0@, r.1@) == ai(old(p)@, fe@, ca@, fb_idx as int, fb@, 0, Bookmark::FormattingElement),
        parser_inv(final(p)@),
        final(p)@.stopped || finish_pre(final(p)@, fe@, ca@, fb@.id, fe_idx),
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(parser_inv);
    hide(dom::wf);
    let ghost p0 = p@;
    proof {
        lemma_inner_refl(p0, fe@, ca@, fb@.id, fe_idx, fb_idx as int);
    }
    let ghost target = ai(p@, fe@, ca@, fb_idx as int, fb@, 0, Bookmark::FormattingElement);
    let cx = InnerCtx { fe, ca };
    let mut node_idx = fb_idx;
    let mut last = copy_elem(fb);
    let mut counter: usize = 0;
    let mut bm = ExecBookmark::FormattingElement;
    loop
        invariant
            inner_inv(p@, fe@, ca@, fb@.id, fe_idx, node_idx as int),
            counter + node_idx == fb_idx,
            ai(p@, fe@, ca@, node_idx as int, last@, counter as nat, bm@) == target,
            dext(p0.doc, p@.doc),
            p0 == old(p)@,
            cx.fe@ == fe@,
            cx.ca@ == ca@,
            target == ai(old(p)@, fe@, ca@, fb_idx as int, fb@, 0, Bookmark::FormattingElement),
        decreases node_idx,
    {
        let ghost pc = p@;
        let (cont, l2, b2) = aa_inner_step(p, &cx, Ghost(fb@.id), Ghost(fe_idx), node_idx, (last, bm), counter);
        proof {
            lemma_dext_trans(p0.doc, pc.doc, p@.doc);
        }
        if !cont {
            return (l2, b2);
        }
        last = l2;
        bm = b2;
        // Never saturate: fe_idx < node_idx - 1, counter + node_idx == fb_idx.
        node_idx = node_idx.saturating_sub(1);
        counter = counter.saturating_add(1);
    }
}

// ---------------------------------------------------------------------
// Steps 4.17 to 4.29

/// Steps 4.17 to 4.21 of [`aa_finish`]: put lastNode at the appropriate
/// place for commonAncestor.
#[verifier::opaque]
pub open spec fn place_last(p: Parser, ca: Elem, last_id: NodeId) -> Parser {
    let l = adjusted_location(p, Some(appropriate_place(p, Some(ca))));
    let target = l.parent;
    let ref_node = l.child;
    let p1 = dom_remove(p, last_id);
    let d = p1.doc;
    if dom::valid(d, last_id) && d.nodes[last_id as int].parent is None && !dom::is_inclusive_ancestor(d, last_id, target)
        && !(d.nodes[target as int].kind is Document && has_element_child(d, target)) && match ref_node {
        None => true,
        Some(r) => d.nodes[r as int].parent == Some(target),
    } {
        dom_insert(p1, last_id, target, ref_node)
    } else {
        p1
    }
}

/// Steps 4.22 to 4.24 of [`aa_finish`]: the parser and newElement.
#[verifier::opaque]
pub open spec fn finish_mid(p2: Parser, fe: Elem, fb_id: NodeId, bm: Bookmark) -> (Parser, Elem) {
    let fi = fmt_index_of(p2.formatting, p2.formatting.len() as int, fe.id);
    let token = p2.formatting[fi]->Entry_token;
    let (p3, new_element) = create_element_for_token(p2, token, Namespace::Html, fb_id);
    if p3.stopped {
        (p3, new_element)
    } else {
        let entry = Fmt::Entry { elem: new_element, token };
        let f1 = p3.formatting.remove(fi);
        let f2 = match bm {
            Bookmark::FormattingElement => f1.insert(fi, entry),
            Bookmark::After(b) => f1.insert(fmt_index_of(f1, f1.len() as int, b) + 1, entry),
        };
        let o1 = p3.open.remove(open_index_of(p3, fe.id));
        let o2 = o1.insert(last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb_id) + 1, new_element);
        (Parser { formatting: f2, open: o2, ..p3 }, new_element)
    }
}

/// Steps 4.27 to 4.29 of [`aa_finish`].
#[verifier::opaque]
pub open spec fn finish_end(p4: Parser, fb_id: NodeId, ne_id: NodeId) -> Parser {
    let p5 = dom_reparent_children(p4, fb_id, ne_id);
    let l2 = adjusted_location(p5, Some(Location { parent: fb_id, child: None }));
    dom_insert(p5, ne_id, l2.parent, l2.child)
}

/// [`aa_finish`], hidden.
#[verifier::opaque]
pub open spec fn af(p: Parser, fe: Elem, fb: Elem, ca: Elem, last: Elem, bm: Bookmark) -> Parser {
    aa_finish(p, fe, fb, ca, last, bm)
}

/// [`aa_finish`] in terms of its hidden parts.
pub proof fn lemma_af_unfold(p: Parser, fe: Elem, fb: Elem, ca: Elem, last: Elem, bm: Bookmark)
    ensures
        af(p, fe, fb, ca, last, bm) == if p.stopped {
            p
        } else {
            let r = finish_mid(place_last(p, ca, last.id), fe, fb.id, bm);
            if r.0.stopped {
                r.0
            } else {
                finish_end(r.0, fb.id, r.1.id)
            }
        },
{
    reveal(af);
    reveal(place_last);
    reveal(finish_mid);
    reveal(finish_end);
}

/// Steps 4.17 to 4.21 ([`place_last`]).
fn aa_place_last_node(p: &mut ParserBuf, ca: &ExecElem, last_id: usize)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        elem_ok(old(p)@.doc, ca@),
    ensures
        final(p)@ == place_last(old(p)@, ca@, last_id),
        parser_inv(final(p)@),
        final(p)@ == (Parser { doc: final(p)@.doc, ..old(p)@ }),
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(tag_of);
    hide(parser_inv);
    reveal(place_last);
    let ghost p0 = p@;
    // 4.17 "Let insertionLocation be the appropriate place for inserting a
    // node given commonAncestor."
    let loc = appropriate_place_exec(p, Some(ca));
    // 4.18 "Let (target, refNode) be the adjusted insertion location given
    // insertionLocation."
    let l = adjusted_location_exec(p, Some(loc));
    let target = l.parent;
    let ref_node = l.child;
    // 4.20 "If lastNode is non-null and lastNode's parent is non-null, then
    // remove lastNode."
    dom_remove_exec(p, last_id);
    let ghost p1 = p@;
    proof {
        lemma_inv_iff(p0);
        if p1.doc != p0.doc {
            lemma_remove_extends(p0.doc, last_id);
            lemma_loc_ok_extends(p0.doc, p1.doc, l);
        } else {
            lemma_dext_refl(p0.doc);
        }
        lemma_dext_is(p0.doc, p1.doc);
        assert(loc_ok(p1.doc, l));
        lemma_inv_iff(p1);
    }
    // 4.21 "If all of the following are true: … then: … Insert lastNode into
    // target before refNode."
    let len = p.arena.len();
    let ok = last_id < len && p.arena.parent(last_id).is_none() && !p.arena.is_inclusive_ancestor(last_id, target) && !(
    matches!(p.arena.kind(target), ExecKind::Document { .. }) && has_element_child_exec(&p.arena, target)) && match ref_node {
        None => true,
        Some(r) => p.arena.parent(r) == Some(target),
    };
    if ok {
        dom_insert_exec(p, last_id, target, ref_node);
        proof {
            lemma_dext_trans(p0.doc, p1.doc, p@.doc);
        }
    }
}

/// Step 4.23's list: formattingElement's entry `fi` removed and `entry`
/// inserted at the bookmark.
pub open spec fn mid_list(f: Seq<Fmt>, fi: int, entry: Fmt, bm: Bookmark) -> Seq<Fmt> {
    let f1 = f.remove(fi);
    match bm {
        Bookmark::FormattingElement => f1.insert(fi, entry),
        Bookmark::After(b) => f1.insert(fmt_index_of(f1, f1.len() as int, b) + 1, entry),
    }
}

/// Step 4.24's stack: formattingElement (id `fe_id`) removed and `ne`
/// inserted immediately below furthestBlock (id `fb_id`).
pub open spec fn mid_stack(p3: Parser, fe_id: NodeId, fb_id: NodeId, ne: Elem) -> Seq<Elem> {
    let o1 = p3.open.remove(open_index_of(p3, fe_id));
    o1.insert(last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb_id) + 1, ne)
}

/// Step 4.23 ([`mid_list`]).
fn aa_mid_list(p: &mut ParserBuf, fi: usize, x: ExecFmt, bm: ExecBookmark)
    requires
        parser_inv(old(p)@),
        fi < old(p)@.formatting.len(),
        fmt_ok(old(p)@.doc, x@),
    ensures
        final(p)@ == (Parser { formatting: mid_list(old(p)@.formatting, fi as int, x@, bm@), ..old(p)@ }),
        parser_inv(final(p)@),
{
    let ghost p3 = p@;
    let ghost xv = x@;
    proof {
        lemma_inv_iff(p3);
    }
    let ghost vf = p.formatting@;
    let _ = p.formatting.remove(fi);
    let ghost vf1 = p.formatting@;
    proof {
        assert(fmts_view(vf1) =~= fmts_view(vf).remove(fi as int));
        lemma_fmts_remove(p3.doc, p3.formatting, fi as int);
    }
    let at = match bm {
        ExecBookmark::FormattingElement => fi,
        ExecBookmark::After(b) => match fmt_index_of_exec(p.formatting.as_slice(), p.formatting.len(), b) {
            // Never saturates: j < len.
            Some(j) => j.saturating_add(1),
            None => 0,
        },
    };
    p.formatting.insert(at, x);
    proof {
        assert(fmts_view(p.formatting@) =~= fmts_view(vf1).insert(at as int, xv));
        lemma_fmts_insert(p3.doc, fmts_view(vf1), at as int, xv);
        lemma_inv_iff(p@);
    }
}

/// Step 4.24 ([`mid_stack`]).
fn aa_mid_stack(p: &mut ParserBuf, fe_id: usize, fb_id: usize, ne: ExecElem, Ghost(fe_idx): Ghost<int>)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        1 <= fe_idx < old(p)@.open.len(),
        old(p)@.open[fe_idx].id == fe_id,
        on_stack_from(old(p)@.open, fe_idx + 1, fb_id),
        fe_id != fb_id,
        elem_ok(old(p)@.doc, ne@),
        !is_html(ne@, Tag::Template),
    ensures
        final(p)@ == (Parser { open: mid_stack(old(p)@, fe_id, fb_id, ne@), ..old(p)@ }),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        on_stack_from(final(p)@.open, 0, fb_id),
{
    hide(parser_inv);
    hide(dom::wf);
    hide(head_ok);
    let ghost p3 = p@;
    let ghost ne_v = ne@;
    proof {
        lemma_inv_iff(p3);
    }
    proof {
        lemma_last_index_where(p3.open, p3.open.len() as int, |e: Elem| e.id == fe_id);
        lemma_last_index_where_found(p3.open, p3.open.len() as int, |e: Elem| e.id == fe_id, fe_idx);
    }
    let ri = match open_index_of_exec(p, fe_id) {
        Some(ri) => ri,
        None => vstd::pervasive::unreached(),
    };
    let ghost fbf = |e: Elem| e.id == fb_id;
    let ghost vo = p.open@;
    let _ = p.open.remove(ri);
    let ghost o1 = elems_view(p.open@);
    proof {
        assert(o1 =~= elems_view(vo).remove(ri as int));
        p3.open.remove_ensures(ri as int);
        lemma_open_remove(p3.doc, p3.open, ri as int);
        crate::exec::stack::lemma_tcount_remove(p3.open, ri as int);
        let jb = choose|jb: int| fe_idx + 1 <= jb < p3.open.len() && (#[trigger] p3.open[jb]).id == fb_id;
        assert(jb != ri);
        if jb < ri {
            assert(o1[jb] == p3.open[jb]);
            lemma_last_index_where_found(o1, o1.len() as int, fbf, jb);
        } else {
            assert(o1[jb - 1] == p3.open[jb]);
            lemma_last_index_where_found(o1, o1.len() as int, fbf, jb - 1);
        }
        assert(o1[0] == p3.open[0]);
        lemma_last_index_where(o1, o1.len() as int, fbf);
    }
    let bi = match last_index_where_exec(p.open.as_slice(), p.open.len(), &ElemPred::Id(fb_id), Ghost(fbf)) {
        Some(bi) => bi,
        None => vstd::pervasive::unreached(),
    };
    // Never saturates: bi < len.
    let at2 = bi.saturating_add(1);
    p.open.insert(at2, ne);
    let ghost o2 = elems_view(p.open@);
    proof {
        assert(o2 =~= o1.insert(at2 as int, ne_v));
        o1.insert_ensures(at2 as int, ne_v);
        lemma_open_insert(p3.doc, o1, at2 as int, ne_v);
        lemma_templates_in_insert(o1, at2 as int, ne_v, o1.len() as int);
        lemma_inv_open_fmt(p3, o2, p3.formatting);
        assert(p@ == (Parser { open: o2, formatting: p3.formatting, ..p3 }));
        assert(o2[0] == o1[0]);
        assert(o2[bi as int] == o1[bi as int]);
        assert(o2[bi as int].id == fb_id);
    }
}

/// Steps 4.22 to 4.24 ([`finish_mid`]): newElement.
fn aa_finish_mid(p: &mut ParserBuf, fe: &ExecElem, fb_id: usize, bm: ExecBookmark, Ghost(ca): Ghost<Elem>, Ghost(fe_idx): Ghost<int>) -> (r:
    ExecElem)
    requires
        finish_pre(old(p)@, fe@, ca, fb_id, fe_idx),
    ensures
        (final(p)@, r@) == finish_mid(old(p)@, fe@, fb_id, bm@),
        parser_inv(final(p)@),
        dext(old(p)@.doc, final(p)@.doc),
        !final(p)@.stopped ==> stack_rooted(final(p)@) && on_stack_from(final(p)@.open, 0, fb_id) && elem_ok(
            final(p)@.doc,
            r@,
        ) && !is_html(r@, Tag::Template),
{
    hide(tag_of);
    hide(dom::wf);
    reveal(finish_mid);
    let ghost p2 = p@;
    proof {
        lemma_inv_iff(p2);
        let jf = choose|jf: int|
            0 <= jf < p2.formatting.len() && (#[trigger] p2.formatting[jf]) is Entry && p2.formatting[jf]->Entry_elem.id == fe.id;
        lemma_fmt_index_of_found(p2.formatting, p2.formatting.len() as int, fe.id, jf);
        lemma_fmt_index_of(p2.formatting, p2.formatting.len() as int, fe.id);
        let jb = choose|jb: int| fe_idx + 1 <= jb < p2.open.len() && (#[trigger] p2.open[jb]).id == fb_id;
        assert(elem_ok(p2.doc, p2.open[jb]));
    }
    // 4.22 "Let newElement be the result of creating an element for the
    // token for which formattingElement was created, in the HTML namespace,
    // with furthestBlock as the intended parent."
    let fi = match fmt_index_of_exec(p.formatting.as_slice(), p.formatting.len(), fe.id) {
        Some(fi) => fi,
        None => vstd::pervasive::unreached(),
    };
    proof {
        assert(fmt_ok(p2.doc, p2.formatting[fi as int]));
    }
    let token = match p.formatting.get(fi) {
        Some(ExecFmt::Entry { token, .. }) => copy_tagtok(token),
        _ => vstd::pervasive::unreached(),
    };
    let ne = create_element_for_token_exec(p, &token, Namespace::Html, fb_id);
    proof {
        lemma_dext_is(p2.doc, p@.doc);
    }
    if p.stopped {
        return ne;
    }
    let ghost p3 = p@;
    let ghost x = Fmt::Entry { elem: ne@, token: token@ };
    proof {
        lemma_inv_iff(p3);
        lemma_elem_template(p3.doc, ne@);
        assert(fmt_ok(p3.doc, x));
    }
    // 4.23 "Remove formattingElement from the list of active formatting
    // elements, and insert newElement into the list of active formatting
    // elements at the position of the aforementioned bookmark."
    aa_mid_list(p, fi, ExecFmt::Entry { elem: copy_elem(&ne), token }, bm);
    // 4.24 "Remove formattingElement from the stack of open elements, and
    // insert newElement into the stack of open elements immediately below
    // the position of furthestBlock in that stack."
    let r = copy_elem(&ne);
    aa_mid_stack(p, fe.id, fb_id, ne, Ghost(fe_idx));
    r
}


/// Steps 4.27 to 4.29 ([`finish_end`]).
fn aa_finish_end(p: &mut ParserBuf, fb_id: usize, ne: &ExecElem)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        on_stack_from(old(p)@.open, 0, fb_id),
        elem_ok(old(p)@.doc, ne@),
        !is_html(ne@, Tag::Template),
    ensures
        final(p)@ == finish_end(old(p)@, fb_id, ne@.id),
        parser_inv(final(p)@),
        final(p)@.open == old(p)@.open,
        final(p)@.stopped == old(p)@.stopped,
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(tag_of);
    hide(dom::wf);
    reveal(finish_end);
    let ghost p4 = p@;
    proof {
        lemma_inv_iff(p4);
        lemma_elem_template(p4.doc, ne@);
    }
    // 4.27.1 "Take all of the child nodes of furthestBlock and append them
    // to newElement."
    dom_reparent_children_exec(p, fb_id, ne.id);
    let ghost p5 = p@;
    proof {
        lemma_inv_iff(p5);
        let jb = choose|jb: int| 0 <= jb < p5.open.len() && (#[trigger] p5.open[jb]).id == fb_id;
        assert(elem_ok(p5.doc, p5.open[jb]));
        lemma_elem_template(p5.doc, p5.open[jb]);
    }
    // 4.27.2 "Let (newElementParent, newElementRefNode) be the adjusted
    // insertion location given (furthestBlock, null)."
    let l2 = adjusted_location_exec(p, Some(Location { parent: fb_id, child: None }));
    // 4.27.3 "Insert newElement into newElementParent before
    // newElementRefNode." (4.28, 4.29: nothing to do, the sanitizer is
    // null.)
    dom_insert_exec(p, ne.id, l2.parent, l2.child);
    proof {
        lemma_dext_trans(p4.doc, p5.doc, p@.doc);
    }
}

/// Steps 4.17 to 4.29 ([`aa_finish`]).
fn aa_finish_exec(
    p: &mut ParserBuf,
    fe: &ExecElem,
    fb: &ExecElem,
    ca: &ExecElem,
    last: &ExecElem,
    bm: ExecBookmark,
    Ghost(fe_idx): Ghost<int>,
)
    requires
        finish_pre(old(p)@, fe@, ca@, fb@.id, fe_idx),
    ensures
        final(p)@ == af(old(p)@, fe@, fb@, ca@, last@, bm@),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(tag_of);
    hide(dom::wf);
    let ghost p0 = p@;
    proof {
        lemma_af_unfold(p0, fe@, fb@, ca@, last@, bm@);
        lemma_inv_iff(p0);
        assert(elem_ok(p0.doc, p0.open[fe_idx - 1]));
    }
    // 4.17 to 4.21
    aa_place_last_node(p, ca, last.id);
    let ghost p2 = p@;
    // 4.22 to 4.24
    let ne = aa_finish_mid(p, fe, fb.id, bm, Ghost(ca@), Ghost(fe_idx));
    let ghost p4 = p@;
    proof {
        lemma_dext_trans(p0.doc, p2.doc, p4.doc);
    }
    if p.stopped {
        return ;
    }
    // 4.27 to 4.29
    aa_finish_end(p, fb.id, &ne);
    proof {
        lemma_dext_trans(p0.doc, p4.doc, p@.doc);
    }
}

// ---------------------------------------------------------------------
// The outer loop

/// What the algorithm needs of its token: tagged, and not `html` (so that
/// formattingElement is never the `html` element at the root of the
/// stack, and step 4.9's commonAncestor exists).
pub open spec fn aa_tok_ok(tt: TagTok) -> bool {
    tok_tagged(tt) && tt.tag != Tag::Html
}

/// [`aa_outer`], hidden.
#[verifier::opaque]
pub open spec fn ao(p: Parser, tt: TagTok, counter: nat) -> AdoptionOutcome {
    aa_outer(p, tt, counter)
}

/// One round of [`aa_outer`] in terms of the hidden inner loop and
/// finish.
pub proof fn lemma_ao_unfold(p: Parser, tt: TagTok, counter: nat)
    requires
        !p.stopped,
        counter < 8,
    ensures
        ao(p, tt, counter) == ({
            let f = p.formatting;
            let fi = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| e.name == tt.name);
            if fi < 0 {
                AdoptionOutcome::AnyOtherEndTag(p)
            } else {
                let fe = f[fi]->Entry_elem;
                let fe_idx = open_index_of(p, fe.id);
                if fe_idx < 0 {
                    AdoptionOutcome::Done(Parser { formatting: f.remove(fi), ..p })
                } else if !has_node_in_scope(p, fe.id, Scope::Default) {
                    AdoptionOutcome::Done(p)
                } else {
                    let fb_idx = first_special_from(p.open, fe_idx + 1);
                    if fb_idx < 0 {
                        let q = pop_until_node_popped(p, fe.id);
                        AdoptionOutcome::Done(Parser { formatting: q.formatting.remove(fi), ..q })
                    } else {
                        let fb = p.open[fb_idx];
                        let ca = p.open[fe_idx - 1];
                        let r = ai(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
                        ao(af(r.0, fe, fb, ca, r.1, r.2), tt, counter + 1)
                    }
                }
            }
        }),
{
    reveal(ao);
    reveal(ai);
    reveal(af);
}

/// The algorithm is step 2 or [`ao`] from 0.
pub proof fn lemma_aa_start(p: Parser, tt: TagTok)
    ensures
        adoption_agency(p, tt) == if p.open.len() > 0 && current_node(p).ns == Namespace::Html && current_node(p).name
            == tt.name && !in_formatting(p, current_node(p).id) {
            AdoptionOutcome::Done(pop(p))
        } else {
            ao(p, tt, 0)
        },
{
    reveal(ao);
}

/// One round of step 4 with outerLoopCounter `counter`: `Some` of the
/// outcome when the algorithm returns, `None` to go on with `counter + 1`.
fn aa_outer_step(p: &mut ParserBuf, tt: &ExecTagTok, counter: usize) -> (r: Option<ExecAdoptionOutcome>)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        aa_tok_ok(tt@),
    ensures
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        dext(old(p)@.doc, final(p)@.doc),
        match r {
            Some(o) => adoption_outcome_view(o, final(p)@) == ao(old(p)@, tt@, counter as nat),
            None => counter < 8 && ao(final(p)@, tt@, (counter + 1) as nat) == ao(old(p)@, tt@, counter as nat),
        },
{
    hide(tag_of);
    hide(parser_inv);
    hide(dom::wf);
    let ghost p0 = p@;
    proof {
        lemma_inv_iff(p0);
        lemma_dext_refl(p0.doc);
    }
    // 4.1 "If outerLoopCounter is greater than or equal to 8, then return."
    if p.stopped || counter >= 8 {
        proof {
            reveal(ao);
        }
        return Some(ExecAdoptionOutcome::Done);
    }
    proof {
        lemma_ao_unfold(p0, tt@, counter as nat);
    }
    // 4.3 "Let formattingElement be the last element in the list of active
    // formatting elements that: is between the end of the list and the last
    // marker in the list, if any, or the start of the list otherwise, and has
    // the tag name subject."
    let from = after_last_marker_exec(p.formatting.as_slice());
    let ghost pred = |e: Elem| e.name == tt@.name;
    let fi = match fmt_last_named_exec(p.formatting.as_slice(), from, tt.name.as_slice(), Ghost(pred)) {
        Some(fi) => fi,
        None => {
            // "If there is no such element, then act as described in the
            // "any other end tag" entry above and return."
            return Some(ExecAdoptionOutcome::AnyOtherEndTag);
        },
    };
    proof {
        lemma_fmt_last_where(p0.formatting, from as int, p0.formatting.len() as int, pred);
        assert(fmt_ok(p0.doc, p0.formatting[fi as int]));
    }
    let fe = match p.formatting.get(fi) {
        Some(ExecFmt::Entry { elem, .. }) => copy_elem(elem),
        _ => vstd::pervasive::unreached(),
    };
    let fe_idx = match open_index_of_exec(p, fe.id) {
        Some(k) => k,
        None => {
            // 4.4 "If formattingElement is not in the stack of open elements,
            // then this is a parse error; remove the element from the list,
            // and return."
            let ghost v = p.formatting@;
            let _ = p.formatting.remove(fi);
            proof {
                assert(fmts_view(p.formatting@) =~= fmts_view(v).remove(fi as int));
                lemma_fmts_remove(p0.doc, p0.formatting, fi as int);
                lemma_inv_iff(p@);
            }
            return Some(ExecAdoptionOutcome::Done);
        },
    };
    proof {
        lemma_last_index_where(p0.open, p0.open.len() as int, |e: Elem| e.id == fe@.id);
        assert(elem_ok(p0.doc, p0.open[fe_idx as int]));
        lemma_same_node(p0.doc, fe@, p0.open[fe_idx as int]);
        if fe_idx == 0 {
            assert(is_html(p0.open[0], Tag::Html));
        }
    }
    // 4.5 "If formattingElement is in the stack of open elements, but the
    // element is not in scope, then this is a parse error; return."
    if !has_node_in_scope_exec(p, fe.id, &Scope::Default) {
        return Some(ExecAdoptionOutcome::Done);
    }
    // 4.7 "Let furthestBlock be the topmost node in the stack of open
    // elements that is lower in the stack than formattingElement, and is an
    // element in the special category."
    // Never saturates: fe_idx < len.
    let n_open = p.open.len();
    let start = if fe_idx < n_open {
        fe_idx.saturating_add(1)
    } else {
        n_open
    };
    proof {
        assert(p.open@.len() == p0.open.len());
        assert(fe_idx < n_open);
        assert(start == fe_idx + 1);
        assert(elems_view(p.open@) == p0.open);
    }
    let fb_idx = match first_special_from_exec(p.open.as_slice(), start) {
        Some(k) => k,
        None => {
            // 4.8 "pop all the nodes from the bottom of the stack of open
            // elements, from the current node up to and including
            // formattingElement, then remove formattingElement from the list
            // of active formatting elements, and finally return."
            proof {
                lemma_pop_until_node_popped(p0, fe@.id);
                lemma_pop_until_where_at(p0, |e: Elem| e.id == fe@.id);
            }
            pop_until_node_popped_exec(p, fe.id);
            let ghost q = p@;
            let ghost v = p.formatting@;
            let _ = p.formatting.remove(fi);
            proof {
                assert(q.formatting == p0.formatting);
                assert(fmts_view(p.formatting@) =~= fmts_view(v).remove(fi as int));
                lemma_inv_iff(q);
                lemma_fmts_remove(q.doc, q.formatting, fi as int);
                lemma_inv_iff(p@);
                assert(p@.open[0] == p0.open[0]);
            }
            return Some(ExecAdoptionOutcome::Done);
        },
    };
    proof {
        lemma_first_special_from(p0.open, fe_idx + 1);
        assert(fe_idx < fb_idx < p0.open.len());
        let f = |e: Elem| e.id == fe@.id;
        lemma_last_index_where(p0.open, p0.open.len() as int, f);
        assert(fe_idx as int == last_index_where(p0.open, p0.open.len() as int, f));
        assert(!f(p0.open[fb_idx as int]));
    }
    let fb = match p.open.get(fb_idx) {
        Some(e) => copy_elem(e),
        None => vstd::pervasive::unreached(),
    };
    // 4.9 "Let commonAncestor be the element immediately above
    // formattingElement in the stack of open elements." (Never saturates:
    // fe_idx >= 1.)
    let ca = match p.open.get(fe_idx.saturating_sub(1)) {
        Some(e) => copy_elem(e),
        None => vstd::pervasive::unreached(),
    };
    proof {
        assert(in_list(p0.formatting, fe@.id)) by {
            assert(p0.formatting[fi as int] is Entry);
        }
        assert(on_stack_from(p0.open, fb_idx as int, fb@.id)) by {
            assert(p0.open[fb_idx as int].id == fb@.id);
        }
    }
    // 4.10 to 4.29
    aa_outer_tail(p, &fe, &fb, &ca, fb_idx, Ghost(fe_idx as int));
    None
}

/// Steps 4.10 to 4.29, once formattingElement (at index `fe_idx`),
/// furthestBlock (at index `fb_idx`) and commonAncestor are known.
fn aa_outer_tail(p: &mut ParserBuf, fe: &ExecElem, fb: &ExecElem, ca: &ExecElem, fb_idx: usize, Ghost(fe_idx): Ghost<int>)
    requires
        inner_inv(old(p)@, fe@, ca@, fb@.id, fe_idx, fb_idx as int),
    ensures
        ({
            let r = ai(old(p)@, fe@, ca@, fb_idx as int, fb@, 0, Bookmark::FormattingElement);
            final(p)@ == af(r.0, fe@, fb@, ca@, r.1, r.2)
        }),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        dext(old(p)@.doc, final(p)@.doc),
{
    let ghost p0 = p@;
    // 4.10 to 4.16
    let (last, bm) = aa_inner_exec(p, fe, ca, fb, fb_idx, Ghost(fe_idx));
    let ghost p1 = p@;
    // 4.17 to 4.29
    if p.stopped {
        proof {
            reveal(af);
        }
        return ;
    }
    aa_finish_exec(p, fe, fb, ca, &last, bm, Ghost(fe_idx));
    proof {
        lemma_dext_trans(p0.doc, p1.doc, p@.doc);
    }
}

/// Step 2: "If the current node is an HTML element whose tag name is
/// subject, and the current node is not in the list of active formatting
/// elements, then pop the current node off the stack of open elements and
/// return." `true` if it popped.
fn aa_pop_current(p: &mut ParserBuf, tt: &ExecTagTok) -> (r: bool)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        aa_tok_ok(tt@),
    ensures
        r == (old(p)@.open.len() > 0 && current_node(old(p)@).ns == Namespace::Html && current_node(old(p)@).name == tt@.name
            && !in_formatting(old(p)@, current_node(old(p)@).id)),
        r ==> final(p)@ == pop(old(p)@),
        !r ==> final(p)@ == old(p)@,
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        dext(old(p)@.doc, final(p)@.doc),
{
    let ghost p0 = p@;
    proof {
        lemma_inv_iff(p0);
        lemma_dext_refl(p0.doc);
    }
    if p.open.is_empty() {
        return false;
    }
    let cur = current_node_exec(p);
    let hit = is_html_ns(cur) && super::super::names::u32s_eq(cur.name.as_slice(), tt.name.as_slice()) && !in_formatting_exec(
        p,
        cur.id,
    );
    if hit {
        proof {
            let n = p0.open.len() - 1;
            assert(elem_ok(p0.doc, p0.open[n]));
            if !p0.stopped && n == 0 {
                assert(is_html(p0.open[0], Tag::Html));
            }
            lemma_pop_inv(p0);
        }
        pop_exec(p);
        proof {
            assert(p0.stopped || p@.open[0] == p0.open[0]);
        }
    }
    hit
}

/// Steps 3 and 4: the outer loop from outerLoopCounter 0 ([`ao`]).
fn aa_outer_exec(p: &mut ParserBuf, tt: &ExecTagTok) -> (r: ExecAdoptionOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        aa_tok_ok(tt@),
        dext(old(p)@.doc, old(p)@.doc),
    ensures
        adoption_outcome_view(r, final(p)@) == ao(old(p)@, tt@, 0),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        dext(old(p)@.doc, final(p)@.doc),
{
    hide(parser_inv);
    hide(dom::wf);
    let ghost p0 = p@;
    // 3. "Let outerLoopCounter be 0." 4. "While true:"
    let mut counter: usize = 0;
    loop
        invariant
            parser_inv(p@),
            p@.stopped || stack_rooted(p@),
            aa_tok_ok(tt@),
            counter <= 8,
            dext(p0.doc, p@.doc),
            ao(p@, tt@, counter as nat) == ao(p0, tt@, 0),
            p0 == old(p)@,
        decreases 8 - counter,
    {
        let ghost pc = p@;
        let step = aa_outer_step(p, tt, counter);
        proof {
            lemma_dext_trans(p0.doc, pc.doc, p@.doc);
        }
        if let Some(o) = step {
            return o;
        }
        // 4.2 "Increment outerLoopCounter by 1." (Never saturates: counter <
        // 8.)
        counter = counter.saturating_add(1);
    }
}

/// HTML §13.2.6.4.7 the adoption agency algorithm for the token `tt`
/// ([`adoption_agency`]).
pub fn adoption_agency_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: &ExecTagTok) -> (r: ExecAdoptionOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        aa_tok_ok(tt@),
    ensures
        adoption_outcome_view(r, final(p)@) == adoption_agency(old(p)@, tt@),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        doc_extends(old(p)@.doc, final(p)@.doc),
{
    let _ = env;
    proof {
        lemma_aa_start(p@, tt@);
    }
    // 1. "Let subject be token's tag name." 2.
    if aa_pop_current(p, tt) {
        proof {
            lemma_dext_is(old(p)@.doc, p@.doc);
        }
        return ExecAdoptionOutcome::Done;
    }
    // 3., 4.
    let ghost p1 = p@;
    let r = aa_outer_exec(p, tt);
    proof {
        lemma_dext_trans(old(p)@.doc, p1.doc, p@.doc);
        lemma_dext_is(old(p)@.doc, p@.doc);
    }
    r
}

} // verus!
