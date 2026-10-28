//! The "in body" mode and the adoption agency algorithm keep the actions,
//! the confidence and the stopped flag, or stop parsing ([`grows`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use super::frame_base::lemma_pop, super::frame_base::lemma_push, super::frame_base::lemma_stop_parsing, super::frame_base::lemma_dom_insert, super::frame_base::lemma_dom_remove, super::frame_base::lemma_create, super::frame_base::lemma_create_element_for_token, super::frame_base::lemma_insert_element_at, super::frame_base::lemma_insert_foreign_element, super::frame_base::lemma_insert_html_element, super::frame_base::lemma_insert_characters, super::frame_base::lemma_insert_char, super::frame_base::lemma_insert_comment, super::frame_base::lemma_insert_pi, super::frame_base::lemma_generic_text_parsing, super::frame_base::lemma_pop_while, super::frame_base::lemma_generate_implied_end_tags, super::frame_base::lemma_generate_all_implied_end_tags_thoroughly, super::frame_base::lemma_pop_until_popped, super::frame_base::lemma_pop_until_heading_popped, super::frame_base::lemma_pop_until_node_popped, super::frame_base::lemma_remove_open_at, super::frame_base::lemma_reset_insertion_mode, super::frame_base::lemma_push_formatting, super::frame_base::lemma_push_marker, super::frame_base::lemma_clear_to_last_marker, super::frame_base::lemma_reconstruct_create, super::frame_base::lemma_reconstruct_formatting;

/// The parser an adoption agency outcome carries.
pub open spec fn aa_parser(o: AdoptionOutcome) -> Parser {
    match o {
        AdoptionOutcome::Done(q) => q,
        AdoptionOutcome::AnyOtherEndTag(q) => q,
    }
}

// ---------------------------------------------------------------------
// The adoption agency algorithm

/// Move the children of a node.
pub broadcast proof fn lemma_dom_reparent_children(p: Parser, from: NodeId, to: NodeId)
    ensures
        grows(p, #[trigger] dom_reparent_children(p, from, to)),
{
}

/// The inner loop.
pub broadcast proof fn lemma_aa_inner(
    p: Parser,
    fe: Elem,
    ca: Elem,
    node_idx: int,
    last_node: Elem,
    counter: nat,
    bookmark: Bookmark,
)
    ensures
        grows(p, (#[trigger] aa_inner(p, fe, ca, node_idx, last_node, counter, bookmark)).0),
    decreases node_idx,
{
    hide(create_element_for_token);
    hide(dom_insert);
    hide(remove_open_at);
    if !(p.stopped || node_idx <= 0) {
        let counter = counter + 1;
        let i = node_idx - 1;
        let node = p.open[i];
        if node.id != fe.id {
            let p1 = if counter > 3 && in_formatting(p, node.id) {
                Parser { formatting: p.formatting.remove(fmt_index_of(p.formatting, p.formatting.len() as int, node.id)), ..p }
            } else {
                p
            };
            if !in_formatting(p1, node.id) {
                lemma_aa_inner(remove_open_at(p1, i), fe, ca, i, last_node, counter, bookmark);
            } else {
                let k = fmt_index_of(p1.formatting, p1.formatting.len() as int, node.id);
                let token = p1.formatting[k]->Entry_token;
                let (p2, new_element) = create_element_for_token(p1, token, Namespace::Html, ca.id);
                if !p2.stopped {
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
                    lemma_aa_inner(p4, fe, ca, i, new_element, counter, bm);
                }
            }
        }
    }
}

/// The end of an outer loop iteration (steps 4.14 to 4.20).
pub broadcast proof fn lemma_aa_finish(p: Parser, fe: Elem, fb: Elem, ca: Elem, last_node: Elem, bookmark: Bookmark)
    ensures
        grows(p, #[trigger] aa_finish(p, fe, fb, ca, last_node, bookmark)),
{
    hide(create_element_for_token);
    hide(dom_insert);
    hide(dom_remove);
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
        assert(grows(p, p2));
        let fi = fmt_index_of(p2.formatting, p2.formatting.len() as int, fe.id);
        let token = p2.formatting[fi]->Entry_token;
        let (p3, new_element) = create_element_for_token(p2, token, Namespace::Html, fb.id);
        assert(grows(p, p3));
        if !p3.stopped {
            let entry = Fmt::Entry { elem: new_element, token };
            let f1 = p3.formatting.remove(fi);
            let f2 = match bookmark {
                Bookmark::FormattingElement => f1.insert(fi, entry),
                Bookmark::After(b) => f1.insert(fmt_index_of(f1, f1.len() as int, b) + 1, entry),
            };
            let o1 = p3.open.remove(open_index_of(p3, fe.id));
            let o2 = o1.insert(last_index_where(o1, o1.len() as int, |e: Elem| e.id == fb.id) + 1, new_element);
            let p4 = Parser { formatting: f2, open: o2, ..p3 };
            let p5 = dom_reparent_children(p4, fb.id, new_element.id);
            lemma_dom_reparent_children(p4, fb.id, new_element.id);
            let l2 = adjusted_location(p5, Some(Location { parent: fb.id, child: None }));
            assert(grows(p, dom_insert(p5, new_element.id, l2.parent, l2.child)));
        }
    }
}

/// The outer loop.
pub broadcast proof fn lemma_aa_outer(p: Parser, tt: TagTok, counter: nat)
    ensures
        grows(p, aa_parser(#[trigger] aa_outer(p, tt, counter))),
    decreases 8 - counter,
{
    hide(aa_inner);
    hide(aa_finish);
    hide(pop_until_node_popped);
    if !(p.stopped || counter >= 8) {
        let f = p.formatting;
        let fi = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| e.name == tt.name);
        if fi >= 0 {
            let fe = f[fi]->Entry_elem;
            let fe_idx = open_index_of(p, fe.id);
            if fe_idx >= 0 && has_node_in_scope(p, fe.id, Scope::Default) {
                let fb_idx = first_special_from(p.open, fe_idx + 1);
                if fb_idx >= 0 {
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
        grows(p, aa_parser(#[trigger] adoption_agency(p, tt))),
{
    hide(aa_outer);
    lemma_aa_outer(p, tt, 0);
}

// ---------------------------------------------------------------------
// "in body" helpers

/// Add the attributes the element does not have.
pub broadcast proof fn lemma_add_missing_attributes(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int)
    ensures
        grows(p, #[trigger] add_missing_attributes(p, el, attrs, i)),
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
        grows(p, #[trigger] pop_until_named_popped(p, name)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html_named(current_node(p), name) {
        lemma_pop_until_named_popped(pop(p), name);
    }
}

/// Insert an element and pop it.
pub broadcast proof fn lemma_insert_and_pop(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] insert_and_pop(p, tt)),
{
}

/// Set the frameset-ok flag to "not ok".
pub broadcast proof fn lemma_frameset_not_ok(p: Parser)
    ensures
        grows(p, #[trigger] frameset_not_ok(p)),
{
}

/// Close a `p` element.
pub broadcast proof fn lemma_close_p_element(p: Parser)
    ensures
        grows(p, #[trigger] close_p_element(p)),
{
}

/// Close a `p` element if one is in button scope.
pub broadcast proof fn lemma_close_p_if_in_button_scope(p: Parser)
    ensures
        grows(p, #[trigger] close_p_if_in_button_scope(p)),
{
    hide(close_p_element);
    lemma_close_p_element(p);
}

/// The `li` loop.
pub broadcast proof fn lemma_li_loop(p: Parser, i: int)
    ensures
        grows(p, #[trigger] li_loop(p, i)),
    decreases i + 1,
{
    if i >= 0 {
        lemma_li_loop(p, i - 1);
    }
}

/// The `dd`/`dt` loop.
pub broadcast proof fn lemma_dd_dt_loop(p: Parser, i: int)
    ensures
        grows(p, #[trigger] dd_dt_loop(p, i)),
    decreases i + 1,
{
    if i >= 0 {
        lemma_dd_dt_loop(p, i - 1);
    }
}

/// The "any other end tag" loop.
pub broadcast proof fn lemma_any_other_end_tag_loop(p: Parser, tt: TagTok, i: int)
    ensures
        grows(p, #[trigger] any_other_end_tag_loop(p, tt, i)),
    decreases i + 1,
{
    if i >= 0 {
        lemma_any_other_end_tag_loop(p, tt, i - 1);
    }
}

/// "Any other end tag".
pub broadcast proof fn lemma_in_body_any_other_end_tag(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_any_other_end_tag(p, tt)),
{
    hide(any_other_end_tag_loop);
    lemma_any_other_end_tag_loop(p, tt, p.open.len() - 1);
}

/// The adoption agency algorithm, or "any other end tag".
pub broadcast proof fn lemma_in_body_adoption(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_adoption(p, tt)),
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
