//! The adoption agency algorithm [`keeps`] a live parser (see [`super`]):
//! formattingElement is never the `html` element (its id is fresh,
//! [`root_ids`]), so it sits at an index `>= 1`, and every step changes
//! only entries above it.

#[cfg(verus_only)]
use super::helpers::*;
#[cfg(verus_only)]
use super::lists::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::exec::modes::adoption::{
    af, ai, ao, finish_end, finish_mid, inner_drop, inner_replace, place_last,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The predicate "has id `id`".
pub open spec fn id_is(id: NodeId) -> spec_fn(Elem) -> bool {
    |e: Elem| e.id == id
}

/// Some entry of `o` from index `from` on has id `id`.
pub open spec fn on_stack_from(o: Seq<Elem>, from: int, id: NodeId) -> bool {
    exists|j: int| from <= j < o.len() && (#[trigger] o[j]).id == id
}

/// Replace entry `i >= 1` of the stack with a tagged element that is not a
/// `template`.
pub proof fn lemma_open_update_keeps(p: Parser, i: int, e: Elem)
    requires
        live(p),
        !p.stopped ==> 1 <= i < p.open.len(),
        elem_tagged(e),
        !is_html(e, Tag::Template),
    ensures
        keeps(p, Parser { open: p.open.update(i, e), ..p }),
{
    let q = Parser { open: p.open.update(i, e), ..p };
    if !p.stopped {
        assert(q.open[0] == p.open[0]);
        assert forall|j: int| 0 <= j < q.open.len() implies elem_tagged(#[trigger] q.open[j]) by {
            if j != i {
                assert(q.open[j] == p.open[j]);
            }
        }
        crate::exec::modes::adoption::lemma_templates_in_update(p.open, i, e, p.open.len() as int);
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(q);
    }
}

/// Insert a tagged element that is not a `template` at index `i >= 1` of
/// the stack.
pub proof fn lemma_open_insert_keeps(p: Parser, i: int, e: Elem)
    requires
        live(p),
        !p.stopped ==> 1 <= i <= p.open.len(),
        elem_tagged(e),
        !is_html(e, Tag::Template),
    ensures
        keeps(p, Parser { open: p.open.insert(i, e), ..p }),
{
    let q = Parser { open: p.open.insert(i, e), ..p };
    if !p.stopped {
        assert(q.open[0] == p.open[0]);
        assert forall|j: int| 0 <= j < q.open.len() implies elem_tagged(#[trigger] q.open[j]) by {
            if j < i {
                assert(q.open[j] == p.open[j]);
            } else if j > i {
                assert(q.open[j] == p.open[j - 1]);
            }
        }
        crate::exec::modes::adoption::lemma_templates_in_insert(p.open, i, e, p.open.len() as int);
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(q);
    }
}

/// [`last_index_where`] is the last index satisfying `f`.
pub proof fn lemma_liw_last(o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, j: int)
    requires
        0 <= i <= o.len(),
        last_index_where(o, i, f) < j < i,
    ensures
        !f(o[j]),
    decreases i,
{
    if !f(o[i - 1]) && j < i - 1 {
        lemma_liw_last(o, i - 1, f, j);
    }
}

/// The DOM's "take all of the child nodes … and append them" keeps the
/// arena's size.
pub proof fn lemma_reparent_len(d: Document, from: NodeId, to: NodeId, n: nat)
    ensures
        dom::reparent_children_n(d, from, to, n).nodes.len() == d.nodes.len(),
    decreases n,
{
    if !(n == 0 || d.nodes[from as int].children.len() == 0) {
        let c = d.nodes[from as int].children[0];
        lemma_insert_len(d, c, to, None);
        lemma_reparent_len(dom::append(d, to, c), from, to, (n - 1) as nat);
    }
}

/// An entry with id `id` survives removing another entry.
pub proof fn lemma_in_formatting_remove(f: Seq<Fmt>, k: int, id: NodeId)
    requires
        fmt_index_of(f, f.len() as int, id) >= 0,
        0 <= k < f.len(),
        !(f[k] is Entry && f[k]->Entry_elem.id == id),
    ensures
        fmt_index_of(f.remove(k), f.len() - 1, id) >= 0,
{
    crate::exec::modes::adoption::lemma_fmt_index_of(f, f.len() as int, id);
    let j = fmt_index_of(f, f.len() as int, id);
    let g = f.remove(k);
    if j < k {
        assert(g[j] == f[j]);
        crate::exec::modes::adoption::lemma_fmt_index_of_found(g, g.len() as int, id, j);
    } else {
        assert(g[j - 1] == f[j]);
        crate::exec::modes::adoption::lemma_fmt_index_of_found(g, g.len() as int, id, j - 1);
    }
}

/// An entry with id `id` survives replacing another entry.
pub proof fn lemma_in_formatting_update(f: Seq<Fmt>, k: int, x: Fmt, id: NodeId)
    requires
        fmt_index_of(f, f.len() as int, id) >= 0,
        0 <= k < f.len(),
        !(f[k] is Entry && f[k]->Entry_elem.id == id),
    ensures
        fmt_index_of(f.update(k, x), f.len() as int, id) >= 0,
{
    crate::exec::modes::adoption::lemma_fmt_index_of(f, f.len() as int, id);
    let j = fmt_index_of(f, f.len() as int, id);
    let g = f.update(k, x);
    assert(g[j] == f[j]);
    crate::exec::modes::adoption::lemma_fmt_index_of_found(g, g.len() as int, id, j);
}

/// What the inner loop keeps: formattingElement at `fe_idx >= 1`,
/// furthestBlock on the stack from `node_idx` on, formattingElement in the
/// list.
pub open spec fn inner_pre(p: Parser, fe: Elem, fb_id: NodeId, fe_idx: int, node_idx: int) -> bool {
    &&& 1 <= fe_idx < node_idx <= p.open.len()
    &&& p.open[fe_idx].id == fe.id
    &&& on_stack_from(p.open, node_idx, fb_id)
    &&& fmt_index_of(p.formatting, p.formatting.len() as int, fe.id) >= 0
}

/// Step 4.16.4.
pub proof fn lemma_inner_drop_keeps(p: Parser, node_id: NodeId, c: nat, fe_id: NodeId)
    requires
        live(p),
        !p.stopped ==> fmt_index_of(p.formatting, p.formatting.len() as int, fe_id) >= 0 && node_id != fe_id,
    ensures
        keeps(p, inner_drop(p, node_id, c)),
        inner_drop(p, node_id, c) == (Parser { formatting: inner_drop(p, node_id, c).formatting, ..p }),
        !p.stopped ==> fmt_index_of(
            inner_drop(p, node_id, c).formatting,
            inner_drop(p, node_id, c).formatting.len() as int,
            fe_id,
        ) >= 0,
{
    reveal(inner_drop);
    if c > 3 && in_formatting(p, node_id) {
        let k = fmt_index_of(p.formatting, p.formatting.len() as int, node_id);
        crate::exec::modes::adoption::lemma_fmt_index_of(p.formatting, p.formatting.len() as int, node_id);
        lemma_fmt_remove_keeps(p, k);
        if !p.stopped {
            lemma_in_formatting_remove(p.formatting, k, fe_id);
        }
    } else {
        lemma_keeps_refl(p);
    }
}

/// Steps 4.16.6 to 4.16.11.
pub proof fn lemma_inner_replace_keeps(
    p1: Parser,
    ca: Elem,
    i: int,
    node_id: NodeId,
    last: Elem,
    bm: Bookmark,
    fe: Elem,
    fe_idx: int,
    fb_id: NodeId,
)
    requires
        live(p1),
        !p1.stopped ==> {
            &&& fmt_index_of(p1.formatting, p1.formatting.len() as int, node_id) >= 0
            &&& node_id != fe.id
            &&& fe_idx < i
            &&& inner_pre(p1, fe, fb_id, fe_idx, i + 1)
        },
    ensures
        keeps(p1, inner_replace(p1, ca, i, node_id, last, bm).0),
        !inner_replace(p1, ca, i, node_id, last, bm).0.stopped ==> inner_pre(
            inner_replace(p1, ca, i, node_id, last, bm).0,
            fe,
            fb_id,
            fe_idx,
            i,
        ),
{
    hide(create_element_for_token);
    hide(dom_insert);
    reveal(inner_replace);
    let k = fmt_index_of(p1.formatting, p1.formatting.len() as int, node_id);
    let token = p1.formatting[k]->Entry_token;
    lemma_ceft_keeps(p1, token, Namespace::Html, ca.id);
    let (p2, new_element) = create_element_for_token(p1, token, Namespace::Html, ca.id);
    if p1.stopped || p2.stopped {
        return;
    }
    crate::exec::modes::adoption::lemma_fmt_index_of(p1.formatting, p1.formatting.len() as int, node_id);
    lemma_fmt_entries_fresh(p1, k);
    let x = Fmt::Entry { elem: new_element, token };
    let pa = Parser { formatting: p2.formatting.update(k, x), ..p2 };
    assert(fmt_fresh(p2, x));
    lemma_fmt_update_keeps(p2, k, x);
    lemma_open_update_keeps(pa, i, new_element);
    let p3 = Parser { formatting: p2.formatting.update(k, x), open: p2.open.update(i, new_element), ..p2 };
    assert(p3 == Parser { open: pa.open.update(i, new_element), ..pa });
    lemma_keeps_trans(p2, pa, p3);
    lemma_keeps_trans(p1, p2, p3);
    lemma_in_formatting_update(p2.formatting, k, x, fe.id);
    let p4 = dom_insert(p3, last.id, new_element.id, None);
    lemma_dom_insert_keeps(p3, last.id, new_element.id, None);
    lemma_keeps_trans(p1, p3, p4);
    let jb = choose|jb: int| i + 1 <= jb < p1.open.len() && (#[trigger] p1.open[jb]).id == fb_id;
    assert(p4.open[fe_idx] == p1.open[fe_idx]);
    assert(p4.open[jb] == p1.open[jb]);
    assert(inner_pre(p4, fe, fb_id, fe_idx, i));
}

/// Step 4.16, the inner loop.
pub proof fn lemma_ai_keeps(
    p: Parser,
    fe: Elem,
    ca: Elem,
    node_idx: int,
    last: Elem,
    counter: nat,
    bm: Bookmark,
    fe_idx: int,
    fb_id: NodeId,
)
    requires
        live(p),
        !p.stopped ==> inner_pre(p, fe, fb_id, fe_idx, node_idx),
    ensures
        keeps(p, ai(p, fe, ca, node_idx, last, counter, bm).0),
        !ai(p, fe, ca, node_idx, last, counter, bm).0.stopped ==> inner_pre(
            ai(p, fe, ca, node_idx, last, counter, bm).0,
            fe,
            fb_id,
            fe_idx,
            fe_idx + 1,
        ),
    decreases node_idx,
{
    hide(keeps);
    if p.stopped {
        reveal(ai);
        lemma_keeps_refl(p);
        return;
    }
    crate::exec::modes::adoption::lemma_ai_unfold(p, fe, ca, node_idx, last, counter, bm);
    let c = counter + 1;
    let i = node_idx - 1;
    let node_id = p.open[i].id;
    if node_id == fe.id {
        lemma_keeps_refl(p);
        return;
    }
    lemma_inner_drop_keeps(p, node_id, c, fe.id);
    let p1 = inner_drop(p, node_id, c);
    lemma_keeps_live(p, p1);
    if !in_formatting(p1, node_id) {
        let p2 = remove_open_at(p1, i);
        lemma_remove_open_keeps(p1, i);
        lemma_keeps_trans(p, p1, p2);
        lemma_keeps_live(p1, p2);
        let jb = choose|jb: int| node_idx <= jb < p1.open.len() && (#[trigger] p1.open[jb]).id == fb_id;
        assert(p2.open[fe_idx] == p1.open[fe_idx]);
        assert(p2.open[jb - 1] == p1.open[jb]);
        assert(inner_pre(p2, fe, fb_id, fe_idx, i));
        lemma_ai_keeps(p2, fe, ca, i, last, c, bm, fe_idx, fb_id);
        lemma_keeps_trans(p, p2, ai(p2, fe, ca, i, last, c, bm).0);
    } else {
        lemma_inner_replace_keeps(p1, ca, i, node_id, last, bm, fe, fe_idx, fb_id);
        let r = inner_replace(p1, ca, i, node_id, last, bm);
        lemma_keeps_trans(p, p1, r.0);
        lemma_keeps_live(p1, r.0);
        if !r.0.stopped {
            lemma_ai_keeps(r.0, fe, ca, i, r.1, c, r.2, fe_idx, fb_id);
            lemma_keeps_trans(p, r.0, ai(r.0, fe, ca, i, r.1, c, r.2).0);
        }
    }
}

/// Steps 4.17 to 4.21.
pub proof fn lemma_place_last_keeps(p: Parser, ca: Elem, last_id: NodeId)
    requires
        live(p),
    ensures
        keeps(p, place_last(p, ca, last_id)),
        place_last(p, ca, last_id) == (Parser { doc: place_last(p, ca, last_id).doc, ..p }),
{
    hide(dom_insert);
    hide(dom_remove);
    reveal(place_last);
    let l = adjusted_location(p, Some(appropriate_place(p, Some(ca))));
    let p1 = dom_remove(p, last_id);
    lemma_dom_remove_keeps(p, last_id);
    lemma_dom_insert_keeps(p1, last_id, l.parent, l.child);
    lemma_keeps_trans(p, p1, dom_insert(p1, last_id, l.parent, l.child));
}

/// Step 4.23's list: the entry at the bookmark.
pub proof fn lemma_mid_list_keeps(p3: Parser, fi: int, entry: Fmt, bm: Bookmark)
    requires
        live(p3),
        0 <= fi < p3.formatting.len(),
        !p3.stopped ==> fmt_fresh(p3, entry),
    ensures
        keeps(p3, Parser { formatting: crate::exec::modes::adoption::mid_list(p3.formatting, fi, entry, bm), ..p3 }),
{
    let f1 = p3.formatting.remove(fi);
    let pa = Parser { formatting: f1, ..p3 };
    lemma_fmt_remove_keeps(p3, fi);
    let at = match bm {
        Bookmark::FormattingElement => fi,
        Bookmark::After(b) => fmt_index_of(f1, f1.len() as int, b) + 1,
    };
    if let Bookmark::After(b) = bm {
        crate::exec::modes::adoption::lemma_fmt_index_of(f1, f1.len() as int, b);
    }
    lemma_fmt_insert_keeps(pa, at, entry);
    lemma_keeps_trans(p3, pa, Parser { formatting: f1.insert(at, entry), ..pa });
}

/// Step 4.24's stack: formattingElement removed (at an index `>= 1`) and the
/// new element inserted below furthestBlock.
pub proof fn lemma_mid_stack_keeps(p: Parser, fe_id: NodeId, fb_id: NodeId, ne: Elem, fe_idx: int)
    requires
        live(p),
        elem_tagged(ne),
        !is_html(ne, Tag::Template),
        !p.stopped ==> {
            &&& 1 <= fe_idx < p.open.len()
            &&& p.open[fe_idx].id == fe_id
            &&& on_stack_from(p.open, fe_idx + 1, fb_id)
            &&& fb_id != fe_id
        },
    ensures
        keeps(p, Parser { open: crate::exec::modes::adoption::mid_stack(p, fe_id, fb_id, ne), ..p }),
{
    if p.stopped {
        return;
    }
    let fef = id_is(fe_id);
    let r = open_index_of(p, fe_id);
    assert(r == last_index_where(p.open, p.open.len() as int, fef));
    crate::exec::stack::lemma_last_index_where_found(p.open, p.open.len() as int, fef, fe_idx);
    let pc = remove_open_at(p, r);
    lemma_remove_open_keeps(p, r);
    let o1 = p.open.remove(r);
    let jb = choose|jb: int| fe_idx + 1 <= jb < p.open.len() && (#[trigger] p.open[jb]).id == fb_id;
    let fbf = id_is(fb_id);
    if jb < r {
        assert(o1[jb] == p.open[jb]);
        crate::exec::stack::lemma_last_index_where_found(o1, o1.len() as int, fbf, jb);
    } else {
        assert(jb != r);
        assert(o1[jb - 1] == p.open[jb]);
        crate::exec::stack::lemma_last_index_where_found(o1, o1.len() as int, fbf, jb - 1);
    }
    let at2 = last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb_id) + 1;
    assert(at2 == last_index_where(o1, o1.len() as int, fbf) + 1);
    lemma_open_insert_keeps(pc, at2, ne);
    lemma_keeps_trans(p, pc, Parser { open: pc.open.insert(at2, ne), ..pc });
}

/// Steps 4.22 to 4.24.
pub proof fn lemma_finish_mid_keeps(p2: Parser, fe: Elem, fb_id: NodeId, bm: Bookmark, fe_idx: int)
    requires
        live(p2),
        !p2.stopped ==> inner_pre(p2, fe, fb_id, fe_idx, fe_idx + 1) && fb_id != fe.id,
    ensures
        keeps(p2, finish_mid(p2, fe, fb_id, bm).0),
{
    hide(create_element_for_token);
    hide(crate::exec::modes::adoption::mid_list);
    hide(crate::exec::modes::adoption::mid_stack);
    reveal(finish_mid);
    let fi = fmt_index_of(p2.formatting, p2.formatting.len() as int, fe.id);
    let token = p2.formatting[fi]->Entry_token;
    lemma_ceft_keeps(p2, token, Namespace::Html, fb_id);
    let (p3, new_element) = create_element_for_token(p2, token, Namespace::Html, fb_id);
    if p2.stopped || p3.stopped {
        return;
    }
    crate::exec::modes::adoption::lemma_fmt_index_of(p2.formatting, p2.formatting.len() as int, fe.id);
    lemma_fmt_entries_fresh(p2, fi);
    let entry = Fmt::Entry { elem: new_element, token };
    assert(fmt_fresh(p3, entry));
    let f2 = crate::exec::modes::adoption::mid_list(p3.formatting, fi, entry, bm);
    let pb = Parser { formatting: f2, ..p3 };
    lemma_mid_list_keeps(p3, fi, entry, bm);
    lemma_keeps_trans(p2, p3, pb);
    lemma_mid_stack_keeps(pb, fe.id, fb_id, new_element, fe_idx);
    let p4 = Parser { open: crate::exec::modes::adoption::mid_stack(pb, fe.id, fb_id, new_element), ..pb };
    lemma_keeps_trans(p2, pb, p4);
    assert(crate::exec::modes::adoption::mid_stack(pb, fe.id, fb_id, new_element) == crate::exec::modes::adoption::mid_stack(
        p3,
        fe.id,
        fb_id,
        new_element,
    )) by {
        reveal(crate::exec::modes::adoption::mid_stack);
    }
    assert(finish_mid(p2, fe, fb_id, bm).0 == p4) by {
        reveal(crate::exec::modes::adoption::mid_list);
        reveal(crate::exec::modes::adoption::mid_stack);
    }
}

/// Steps 4.27 to 4.29.
pub proof fn lemma_finish_end_keeps(p4: Parser, fb_id: NodeId, ne_id: NodeId)
    requires
        live(p4),
    ensures
        keeps(p4, finish_end(p4, fb_id, ne_id)),
{
    hide(dom_insert);
    reveal(finish_end);
    let p5 = dom_reparent_children(p4, fb_id, ne_id);
    lemma_reparent_len(p4.doc, fb_id, ne_id, p4.doc.nodes[fb_id as int].children.len());
    lemma_doc_keeps(p4, p5);
    let l2 = adjusted_location(p5, Some(Location { parent: fb_id, child: None }));
    lemma_dom_insert_keeps(p5, ne_id, l2.parent, l2.child);
    lemma_keeps_trans(p4, p5, dom_insert(p5, ne_id, l2.parent, l2.child));
}

/// Steps 4.17 to 4.29.
pub proof fn lemma_af_keeps(p: Parser, fe: Elem, fb: Elem, ca: Elem, last: Elem, bm: Bookmark, fe_idx: int)
    requires
        live(p),
        !p.stopped ==> inner_pre(p, fe, fb.id, fe_idx, fe_idx + 1) && fb.id != fe.id,
    ensures
        keeps(p, af(p, fe, fb, ca, last, bm)),
{
    crate::exec::modes::adoption::lemma_af_unfold(p, fe, fb, ca, last, bm);
    if p.stopped {
        lemma_keeps_refl(p);
        return;
    }
    lemma_place_last_keeps(p, ca, last.id);
    let p2 = place_last(p, ca, last.id);
    lemma_finish_mid_keeps(p2, fe, fb.id, bm, fe_idx);
    let r = finish_mid(p2, fe, fb.id, bm);
    lemma_keeps_trans(p, p2, r.0);
    if !r.0.stopped {
        lemma_finish_end_keeps(r.0, fb.id, r.1.id);
        lemma_keeps_trans(p, r.0, finish_end(r.0, fb.id, r.1.id));
    }
}

/// The parser of an adoption outcome.
pub open spec fn aa_parser(o: AdoptionOutcome) -> Parser {
    match o {
        AdoptionOutcome::Done(q) => q,
        AdoptionOutcome::AnyOtherEndTag(q) => q,
    }
}

/// Step 4, the outer loop.
pub proof fn lemma_ao_keeps(p: Parser, tt: TagTok, counter: nat)
    requires
        live(p),
    ensures
        keeps(p, aa_parser(ao(p, tt, counter))),
    decreases 8 - counter,
{
    hide(pop_until_node_popped);
    if p.stopped || counter >= 8 {
        reveal(ao);
        lemma_keeps_refl(p);
        return;
    }
    crate::exec::modes::adoption::lemma_ao_unfold(p, tt, counter);
    let f = p.formatting;
    crate::exec::modes::in_body_start_lemmas::lemma_after_last_marker_nonneg(f, f.len() as int);
    let pred = |e: Elem| e.name == tt.name;
    let fi = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, pred);
    crate::exec::modes::in_body_start_lemmas::lemma_fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, pred);
    if fi < 0 {
        lemma_keeps_refl(p);
        return;
    }
    let fe = f[fi]->Entry_elem;
    lemma_fmt_entries_fresh(p, fi);
    let fef = id_is(fe.id);
    let fe_idx = open_index_of(p, fe.id);
    assert(fe_idx == last_index_where(p.open, p.open.len() as int, fef));
    crate::termination::helpers_ranking::lemma_last_index_where(p.open, p.open.len() as int, fef);
    if fe_idx < 0 {
        lemma_fmt_remove_keeps(p, fi);
        return;
    }
    if !has_node_in_scope(p, fe.id, Scope::Default) {
        lemma_keeps_refl(p);
        return;
    }
    assert(fe_idx >= 1);
    crate::exec::modes::adoption::lemma_first_special_from(p.open, fe_idx + 1);
    let fb_idx = first_special_from(p.open, fe_idx + 1);
    if fb_idx < 0 {
        lemma_pop_until_node_popped_keeps(p, fe.id, fe_idx);
        let q = pop_until_node_popped(p, fe.id);
        lemma_fmt_remove_keeps(q, fi);
        lemma_keeps_trans(p, q, Parser { formatting: q.formatting.remove(fi), ..q });
        return;
    }
    let fb = p.open[fb_idx];
    let ca = p.open[fe_idx - 1];
    lemma_liw_last(p.open, p.open.len() as int, fef, fb_idx);
    crate::exec::modes::adoption::lemma_fmt_index_of_found(f, f.len() as int, fe.id, fi);
    assert(inner_pre(p, fe, fb.id, fe_idx, fb_idx));
    lemma_ai_keeps(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement, fe_idx, fb.id);
    let r = ai(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
    lemma_af_keeps(r.0, fe, fb, ca, r.1, r.2, fe_idx);
    let p2 = af(r.0, fe, fb, ca, r.1, r.2);
    lemma_keeps_trans(p, r.0, p2);
    lemma_ao_keeps(p2, tt, counter + 1);
    lemma_keeps_trans(p, p2, aa_parser(ao(p2, tt, counter + 1)));
}

/// The adoption agency algorithm, then (step 4.3) "any other end tag", for a
/// tagged token that is not `html`.
pub proof fn lemma_in_body_adoption_keeps(p: Parser, tt: TagTok)
    requires
        live(p),
        tok_tagged(tt),
        tt.tag != Tag::Html,
    ensures
        keeps(p, in_body_adoption(p, tt)),
{
    crate::exec::modes::adoption::lemma_aa_start(p, tt);
    if p.open.len() > 0 && current_node(p).ns == Namespace::Html && current_node(p).name == tt.name && !in_formatting(
        p,
        current_node(p).id,
    ) {
        if !p.stopped {
            assert(p.open.len() >= 2) by {
                if p.open.len() == 1 {
                    assert(elem_tagged(p.open[0]));
                }
            }
        }
        lemma_pop_keeps(p);
    } else {
        lemma_ao_keeps(p, tt, 0);
        match ao(p, tt, 0) {
            AdoptionOutcome::Done(q) => {},
            AdoptionOutcome::AnyOtherEndTag(q) => {
                lemma_any_other_keeps(q, tt);
                lemma_keeps_trans(p, q, in_body_any_other_end_tag(q, tt));
            },
        }
    }
}

} // verus!
