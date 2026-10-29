//! The adoption agency algorithm and the "in body" helpers keep the modes
//! ([`mk`]), whether or not they stop parsing.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::stop_frame::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// The parser an adoption agency outcome carries.
pub open spec fn aa_parser(o: AdoptionOutcome) -> Parser {
    match o {
        AdoptionOutcome::Done(q) => q,
        AdoptionOutcome::AnyOtherEndTag(q) => q,
    }
}

// ---------------------------------------------------------------------
// Editing the list of active formatting elements

/// Removing an entry keeps the list free of `template` entries.
pub proof fn lemma_fok_remove(p: Parser, q: Parser, k: int)
    requires
        formatting_ok(p),
        0 <= k < p.formatting.len(),
        q.formatting == p.formatting.remove(k),
    ensures
        formatting_ok(q),
{
    assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
        != Tag::Template by {
        if i < k {
            assert(q.formatting[i] == p.formatting[i]);
        } else {
            assert(q.formatting[i] == p.formatting[i + 1]);
        }
    }
}

/// Replacing an entry by one for a token other than `template`.
pub proof fn lemma_fok_update(p: Parser, q: Parser, k: int, x: Fmt)
    requires
        formatting_ok(p),
        0 <= k < p.formatting.len(),
        x is Entry ==> x->Entry_token.tag != Tag::Template,
        q.formatting == p.formatting.update(k, x),
    ensures
        formatting_ok(q),
{
    assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
        != Tag::Template by {
        if i != k {
            assert(q.formatting[i] == p.formatting[i]);
        }
    }
}

/// Inserting an entry for a token other than `template`.
pub proof fn lemma_fok_insert(p: Parser, q: Parser, k: int, x: Fmt)
    requires
        formatting_ok(p),
        0 <= k <= p.formatting.len(),
        x is Entry ==> x->Entry_token.tag != Tag::Template,
        q.formatting == p.formatting.insert(k, x),
    ensures
        formatting_ok(q),
{
    assert forall|i: int| 0 <= i < q.formatting.len() && #[trigger] q.formatting[i] is Entry implies q.formatting[i]->Entry_token.tag
        != Tag::Template by {
        if i < k {
            assert(q.formatting[i] == p.formatting[i]);
        } else if i > k {
            assert(q.formatting[i] == p.formatting[i - 1]);
        }
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm

/// Move the children of a node.
pub broadcast proof fn lemma_dom_reparent_children(p: Parser, from: NodeId, to: NodeId)
    ensures
        mk(p, #[trigger] dom_reparent_children(p, from, to)),
        dom_reparent_children(p, from, to).formatting == p.formatting,
{
}

/// Step 4.16.4: removing node from the list keeps [`mk`] and
/// formattingElement in the list.
pub proof fn lemma_inner_drop(p: Parser, node_id: NodeId, fe_id: NodeId, drop: bool)
    requires
        node_id != fe_id,
    ensures
        ({
            let p1 = if drop && in_formatting(p, node_id) {
                Parser { formatting: p.formatting.remove(fmt_index_of(p.formatting, p.formatting.len() as int, node_id)), ..p }
            } else {
                p
            };
            &&& mk(p, p1)
            &&& p1.stopped == p.stopped
            &&& in_formatting(p, fe_id) ==> in_formatting(p1, fe_id)
        }),
{
    let f = p.formatting;
    crate::exec::modes::adoption::lemma_fmt_index_of(f, f.len() as int, node_id);
    if drop && in_formatting(p, node_id) {
        let k0 = fmt_index_of(f, f.len() as int, node_id);
        let p1 = Parser { formatting: f.remove(k0), ..p };
        if formatting_ok(p) {
            lemma_fok_remove(p, p1, k0);
        }
        if in_formatting(p, fe_id) {
            super::adoption::lemma_in_formatting_remove(f, k0, fe_id);
        }
    }
}

/// Steps 4.16.6 and 4.16.11: replacing node's entry with one for a new
/// element and appending lastNode to it keeps [`mk`] and formattingElement
/// in the list.
pub proof fn lemma_inner_replace(
    p2: Parser,
    k: int,
    i: int,
    e: Elem,
    token: TagTok,
    node_id: NodeId,
    fe_id: NodeId,
    last_id: NodeId,
)
    requires
        !p2.stopped,
        0 <= k < p2.formatting.len(),
        p2.formatting[k] is Entry && p2.formatting[k]->Entry_elem.id == node_id,
        formatting_ok(p2) ==> token.tag != Tag::Template,
        node_id != fe_id,
    ensures
        ({
            let p3 = Parser { formatting: p2.formatting.update(k, Fmt::Entry { elem: e, token }), open: p2.open.update(i, e), ..p2 };
            let p4 = dom_insert(p3, last_id, e.id, None);
            &&& mk(p2, p4)
            &&& in_formatting(p2, fe_id) ==> in_formatting(p4, fe_id)
        }),
{
    let x = Fmt::Entry { elem: e, token };
    let p3 = Parser { formatting: p2.formatting.update(k, x), open: p2.open.update(i, e), ..p2 };
    if formatting_ok(p2) {
        lemma_fok_update(p2, p3, k, x);
    }
    if in_formatting(p2, fe_id) {
        super::adoption::lemma_in_formatting_update(p2.formatting, k, x, fe_id);
    }
    lemma_dom_insert(p3, last_id, e.id, None);
}

/// The inner loop keeps [`mk`], and formattingElement in the list while it
/// runs.
#[verifier::spinoff_prover]
pub proof fn lemma_aa_inner(p: Parser, fe: Elem, ca: Elem, node_idx: int, last_node: Elem, counter: nat, bookmark: Bookmark)
    ensures
        mk(p, aa_inner(p, fe, ca, node_idx, last_node, counter, bookmark).0),
        in_formatting(p, fe.id) && !aa_inner(p, fe, ca, node_idx, last_node, counter, bookmark).0.stopped ==> in_formatting(
            aa_inner(p, fe, ca, node_idx, last_node, counter, bookmark).0,
            fe.id,
        ),
    decreases node_idx,
{
    hide(aa_inner);
    hide(create_element_for_token);
    hide(dom_insert);
    hide(remove_open_at);
    hide(in_formatting);
    hide(mk);
    let r = aa_inner(p, fe, ca, node_idx, last_node, counter, bookmark).0;
    if p.stopped || node_idx <= 0 || p.open[node_idx - 1].id == fe.id {
        assert(r == p) by {
            reveal_with_fuel(aa_inner, 1);
        }
        reveal(mk);
        return;
    }
    let c = counter + 1;
    let i = node_idx - 1;
    let node = p.open[i];
    lemma_inner_drop(p, node.id, fe.id, c > 3);
    let p1 = if c > 3 && in_formatting(p, node.id) {
        Parser { formatting: p.formatting.remove(fmt_index_of(p.formatting, p.formatting.len() as int, node.id)), ..p }
    } else {
        p
    };
    if !in_formatting(p1, node.id) {
        let p2 = remove_open_at(p1, i);
        assert(r == aa_inner(p2, fe, ca, i, last_node, c, bookmark).0) by {
            reveal_with_fuel(aa_inner, 1);
        }
        assert(p2.formatting == p1.formatting && mk(p1, p2)) by {
            reveal(remove_open_at);
            reveal(mk);
        }
        lemma_aa_inner(p2, fe, ca, i, last_node, c, bookmark);
        assert(in_formatting(p2, fe.id) == in_formatting(p1, fe.id)) by {
            reveal(in_formatting);
        }
        lemma_mk_trans(p, p1, p2);
        lemma_mk_trans(p, p2, r);
    } else {
        let f1 = p1.formatting;
        let k = fmt_index_of(f1, f1.len() as int, node.id);
        crate::exec::modes::adoption::lemma_fmt_index_of(f1, f1.len() as int, node.id);
        assert(k >= 0) by {
            reveal(in_formatting);
        }
        let token = p1.formatting[k]->Entry_token;
        let (p2, new_element) = create_element_for_token(p1, token, Namespace::Html, ca.id);
        lemma_create_element_for_token(p1, token, Namespace::Html, ca.id);
        assert(in_formatting(p2, fe.id) == in_formatting(p1, fe.id)) by {
            reveal(in_formatting);
        }
        assert(formatting_ok(p1) ==> token.tag != Tag::Template) by {
            reveal(mk);
        }
        if p2.stopped {
            assert(r == p2) by {
                reveal_with_fuel(aa_inner, 1);
            }
            lemma_mk_trans(p, p1, p2);
        } else {
            lemma_inner_replace(p2, k, i, new_element, token, node.id, fe.id, last_node.id);
            let p3 = Parser {
                formatting: p2.formatting.update(k, Fmt::Entry { elem: new_element, token }),
                open: p2.open.update(i, new_element),
                ..p2
            };
            let bm = match bookmark {
                Bookmark::FormattingElement => Bookmark::After(new_element.id),
                Bookmark::After(b) => Bookmark::After(b),
            };
            let p4 = dom_insert(p3, last_node.id, new_element.id, None);
            assert(r == aa_inner(p4, fe, ca, i, new_element, c, bm).0) by {
                reveal_with_fuel(aa_inner, 1);
            }
            lemma_aa_inner(p4, fe, ca, i, new_element, c, bm);
            lemma_mk_trans(p, p1, p2);
            lemma_mk_trans(p, p2, p4);
            lemma_mk_trans(p, p4, r);
        }
    }
}

/// The end of an outer loop iteration (steps 4.14 to 4.29), with
/// formattingElement in the list.
pub proof fn lemma_aa_finish(p: Parser, fe: Elem, fb: Elem, ca: Elem, last_node: Elem, bookmark: Bookmark)
    requires
        !p.stopped ==> in_formatting(p, fe.id),
    ensures
        mk(p, aa_finish(p, fe, fb, ca, last_node, bookmark)),
{
    hide(create_element_for_token);
    hide(dom_reparent_children);
    hide(appropriate_place);
    hide(adjusted_location);
    if !p.stopped {
        let insertion_location = appropriate_place(p, Some(ca));
        let l = adjusted_location(p, Some(insertion_location));
        let target = l.parent;
        let ref_node = l.child;
        let p1 = dom_remove(p, last_node.id);
        let d = p1.doc;
        let p2 = if dom::valid(d, last_node.id) && d.nodes[last_node.id as int].parent is None && !dom::is_inclusive_ancestor(
            d,
            last_node.id,
            target,
        ) && !(d.nodes[target as int].kind is Document && has_element_child(d, target)) && match ref_node {
            None => true,
            Some(r) => d.nodes[r as int].parent == Some(target),
        } {
            dom_insert(p1, last_node.id, target, ref_node)
        } else {
            p1
        };
        assert(p2.formatting == p.formatting && mk(p, p2));
        let f = p2.formatting;
        let fi = fmt_index_of(f, f.len() as int, fe.id);
        crate::exec::modes::adoption::lemma_fmt_index_of(f, f.len() as int, fe.id);
        let token = f[fi]->Entry_token;
        let (p3, new_element) = create_element_for_token(p2, token, Namespace::Html, fb.id);
        lemma_create_element_for_token(p2, token, Namespace::Html, fb.id);
        if !p3.stopped {
            let entry = Fmt::Entry { elem: new_element, token };
            let f1 = p3.formatting.remove(fi);
            let pf1 = Parser { formatting: f1, ..p3 };
            if formatting_ok(p) {
                lemma_fok_remove(p3, pf1, fi);
            }
            let f2 = match bookmark {
                Bookmark::FormattingElement => f1.insert(fi, entry),
                Bookmark::After(b) => f1.insert(fmt_index_of(f1, f1.len() as int, b) + 1, entry),
            };
            match bookmark {
                Bookmark::FormattingElement => {
                    if formatting_ok(p) {
                        lemma_fok_insert(pf1, Parser { formatting: f2, ..pf1 }, fi, entry);
                    }
                },
                Bookmark::After(b) => {
                    crate::exec::modes::adoption::lemma_fmt_index_of(f1, f1.len() as int, b);
                    if formatting_ok(p) {
                        lemma_fok_insert(pf1, Parser { formatting: f2, ..pf1 }, fmt_index_of(f1, f1.len() as int, b) + 1, entry);
                    }
                },
            }
            let o1 = p3.open.remove(open_index_of(p3, fe.id));
            let o2 = o1.insert(last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb.id) + 1, new_element);
            let p4 = Parser { formatting: f2, open: o2, ..p3 };
            assert(mk(p, p4));
            let p5 = dom_reparent_children(p4, fb.id, new_element.id);
            lemma_dom_reparent_children(p4, fb.id, new_element.id);
            let l2 = adjusted_location(p5, Some(Location { parent: fb.id, child: None }));
            assert(mk(p, dom_insert(p5, new_element.id, l2.parent, l2.child)));
        }
    }
}

/// The outer loop.
pub proof fn lemma_aa_outer(p: Parser, tt: TagTok, counter: nat)
    ensures
        mk(p, aa_parser(aa_outer(p, tt, counter))),
    decreases 8 - counter,
{
    hide(aa_inner);
    hide(aa_finish);
    hide(pop_until_node_popped);
    if !(p.stopped || counter >= 8) {
        let f = p.formatting;
        let from = after_last_marker(f, f.len() as int);
        crate::exec::modes::in_body_start_lemmas::lemma_after_last_marker_nonneg(f, f.len() as int);
        let fi = fmt_last_where(f, from, f.len() as int, |e: Elem| e.name == tt.name);
        super::super::theorems::open_elements::lemma_fmt_last_where(f, from, f.len() as int, |e: Elem| e.name == tt.name);
        if fi >= 0 {
            let fe = f[fi]->Entry_elem;
            crate::exec::modes::adoption::lemma_fmt_index_of_found(f, f.len() as int, fe.id, fi);
            let fe_idx = open_index_of(p, fe.id);
            if fe_idx < 0 {
                if formatting_ok(p) {
                    lemma_fok_remove(p, Parser { formatting: f.remove(fi), ..p }, fi);
                }
            } else if has_node_in_scope(p, fe.id, Scope::Default) {
                let fb_idx = first_special_from(p.open, fe_idx + 1);
                if fb_idx < 0 {
                    let q = pop_until_node_popped(p, fe.id);
                    lemma_pop_until_node_popped(p, fe.id);
                    if formatting_ok(p) {
                        lemma_fok_remove(q, Parser { formatting: q.formatting.remove(fi), ..q }, fi);
                    }
                } else {
                    let fb = p.open[fb_idx];
                    let ca = p.open[fe_idx - 1];
                    let (p1, last_node, bm) = aa_inner(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
                    lemma_aa_inner(p, fe, ca, fb_idx, fb, 0, Bookmark::FormattingElement);
                    let p2 = aa_finish(p1, fe, fb, ca, last_node, bm);
                    lemma_aa_finish(p1, fe, fb, ca, last_node, bm);
                    lemma_aa_outer(p2, tt, counter + 1);
                }
            }
        }
    }
}

/// The adoption agency algorithm.
pub broadcast proof fn lemma_adoption_agency(p: Parser, tt: TagTok)
    ensures
        mk(p, aa_parser(#[trigger] adoption_agency(p, tt))),
{
    hide(aa_outer);
    lemma_aa_outer(p, tt, 0);
}

// ---------------------------------------------------------------------
// "in body" helpers

/// Add the attributes the element does not have.
pub broadcast proof fn lemma_add_missing_attributes(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int)
    ensures
        mk(p, #[trigger] add_missing_attributes(p, el, attrs, i)),
    decreases attrs.len() - i,
{
    if !(i < 0 || i >= attrs.len()) {
        let a = attrs[i];
        let q = if !p.stopped && !element_has_attribute_named(p.doc, el, a.local_name) {
            Parser { doc: dom::append_attribute(p.doc, el, a), ..p }
        } else {
            p
        };
        lemma_add_missing_attributes(q, el, attrs, i + 1);
    }
}

/// Pop until an HTML element with the name has been popped.
pub broadcast proof fn lemma_pop_until_named_popped(p: Parser, name: Seq<u32>)
    ensures
        mk(p, #[trigger] pop_until_named_popped(p, name)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html_named(current_node(p), name) {
        lemma_pop_until_named_popped(pop(p), name);
    }
}

/// Insert an element and pop it.
pub broadcast proof fn lemma_insert_and_pop(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] insert_and_pop(p, tt)),
{
    broadcast use {
        lemma_insert_html_element,
        lemma_generate_implied_end_tags,
        lemma_pop_until_popped,
        lemma_pop_until_node_popped,
    };

}

/// Set the frameset-ok flag to "not ok".
pub broadcast proof fn lemma_frameset_not_ok(p: Parser)
    ensures
        mk(p, #[trigger] frameset_not_ok(p)),
{
}

/// Close a `p` element.
pub broadcast proof fn lemma_close_p_element(p: Parser)
    ensures
        mk(p, #[trigger] close_p_element(p)),
{
    broadcast use {
        lemma_insert_html_element,
        lemma_generate_implied_end_tags,
        lemma_pop_until_popped,
        lemma_pop_until_node_popped,
    };

}

/// Close a `p` element if one is in button scope.
pub broadcast proof fn lemma_close_p_if_in_button_scope(p: Parser)
    ensures
        mk(p, #[trigger] close_p_if_in_button_scope(p)),
{
    hide(close_p_element);
    lemma_close_p_element(p);
}

/// The `li` loop.
pub broadcast proof fn lemma_li_loop(p: Parser, i: int)
    ensures
        mk(p, #[trigger] li_loop(p, i)),
    decreases i + 1,
{
    broadcast use {
        lemma_insert_html_element,
        lemma_generate_implied_end_tags,
        lemma_pop_until_popped,
        lemma_pop_until_node_popped,
    };

    if i >= 0 {
        lemma_li_loop(p, i - 1);
    }
}

/// The `dd`/`dt` loop.
pub broadcast proof fn lemma_dd_dt_loop(p: Parser, i: int)
    ensures
        mk(p, #[trigger] dd_dt_loop(p, i)),
    decreases i + 1,
{
    broadcast use {
        lemma_insert_html_element,
        lemma_generate_implied_end_tags,
        lemma_pop_until_popped,
        lemma_pop_until_node_popped,
    };

    if i >= 0 {
        lemma_dd_dt_loop(p, i - 1);
    }
}

/// The "any other end tag" loop.
pub broadcast proof fn lemma_any_other_end_tag_loop(p: Parser, tt: TagTok, i: int)
    ensures
        mk(p, #[trigger] any_other_end_tag_loop(p, tt, i)),
    decreases i + 1,
{
    broadcast use {
        lemma_insert_html_element,
        lemma_generate_implied_end_tags,
        lemma_pop_until_popped,
        lemma_pop_until_node_popped,
    };

    if i >= 0 {
        lemma_any_other_end_tag_loop(p, tt, i - 1);
    }
}

/// "Any other end tag".
pub broadcast proof fn lemma_in_body_any_other_end_tag(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_any_other_end_tag(p, tt)),
{
    hide(any_other_end_tag_loop);
    lemma_any_other_end_tag_loop(p, tt, p.open.len() - 1);
}

/// The adoption agency algorithm, or "any other end tag".
pub broadcast proof fn lemma_in_body_adoption(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_adoption(p, tt)),
{
    hide(adoption_agency);
    hide(in_body_any_other_end_tag);
    lemma_adoption_agency(p, tt);
    match adoption_agency(p, tt) {
        AdoptionOutcome::Done(q) => {},
        AdoptionOutcome::AnyOtherEndTag(q) => {
            lemma_in_body_any_other_end_tag(q, tt);
        },
    }
}

} // verus!
