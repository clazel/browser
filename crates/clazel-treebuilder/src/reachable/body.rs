//! The "in body" rules keep the reachable-state facts ([`next_core`], see
//! [`super`]).

#[cfg(verus_only)]
use super::adoption::*;
#[cfg(verus_only)]
use super::cells::*;
#[cfg(verus_only)]
use super::early::*;
#[cfg(verus_only)]
use super::helpers::*;
#[cfg(verus_only)]
use super::lists::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Composing

/// Changing flags only.
pub proof fn lemma_flags_keeps(p: Parser, q: Parser)
    requires
        live(p),
        q.open == p.open,
        q.doc == p.doc,
        q.formatting == p.formatting,
        q.form == p.form,
        q.context == p.context,
        q.mode == p.mode,
        q.original_mode == p.original_mode,
        q.template_modes == p.template_modes,
        q.stopped == p.stopped,
    ensures
        keeps(p, q),
{
    assert(crate::termination::template_count(q) == crate::termination::template_count(p));
}

/// Then "insert an HTML element" (not `template`, nor a cell in the "in
/// cell" mode).
pub proof fn lemma_then_insert(p: Parser, q: Parser, tt: TagTok)
    requires
        keeps(p, q),
        tok_tagged(tt),
        tt.tag != Tag::Template,
        tt.tag == Tag::Td || tt.tag == Tag::Th ==> p.mode != Mode::InCell,
    ensures
        keeps(p, insert_html_element(q, tt).0),
{
    lemma_keeps_live(p, q);
    lemma_insert_html_keeps(q, tt);
    lemma_keeps_trans(p, q, insert_html_element(q, tt).0);
}

/// Then "insert an HTML element" and pop it.
pub proof fn lemma_then_insert_pop(p: Parser, q: Parser, tt: TagTok)
    requires
        keeps(p, q),
        tok_tagged(tt),
        tt.tag != Tag::Template,
        tt.tag != Tag::Td && tt.tag != Tag::Th,
    ensures
        keeps(p, insert_and_pop(q, tt)),
{
    lemma_then_insert(p, q, tt);
    let q1 = insert_html_element(q, tt).0;
    lemma_keeps_live(p, q1);
    if !q1.stopped {
        lemma_keeps_live(p, q);
        lemma_insert_html_keeps(q, tt);
        assert(q1.open.len() >= 2);
        lemma_pop_keeps(q1);
        lemma_keeps_trans(p, q1, pop(q1));
    }
}

/// Then "reconstruct the active formatting elements".
pub proof fn lemma_then_reconstruct(p: Parser, q: Parser)
    requires
        keeps(p, q),
    ensures
        keeps(p, reconstruct_formatting(q)),
{
    lemma_keeps_live(p, q);
    lemma_reconstruct_keeps(q);
    lemma_keeps_trans(p, q, reconstruct_formatting(q));
}

/// Then "close a p element" if one is in button scope.
pub proof fn lemma_then_close_p_if(p: Parser, q: Parser)
    requires
        keeps(p, q),
    ensures
        keeps(p, close_p_if_in_button_scope(q)),
{
    lemma_keeps_live(p, q);
    lemma_close_p_if_keeps(q);
    lemma_keeps_trans(p, q, close_p_if_in_button_scope(q));
}

/// Then "set the frameset-ok flag to not ok".
pub proof fn lemma_then_fno(p: Parser, q: Parser)
    requires
        keeps(p, q),
    ensures
        keeps(p, frameset_not_ok(q)),
{
    lemma_keeps_live(p, q);
    lemma_flags_keeps(q, frameset_not_ok(q));
    lemma_keeps_trans(p, q, frameset_not_ok(q));
}

/// What the "in body" cases need: a running, [`good`] parser in a
/// [`rooted_mode`] with `modes_ok`, and a tagged token.
pub open spec fn ib_pre(p: Parser, tt: TagTok) -> bool {
    &&& good(p)
    &&& !p.stopped
    &&& modes_ok(p)
    &&& rooted_mode(p.mode)
    &&& tok_tagged(tt)
}

/// A case that keeps the mode is done.
pub proof fn lemma_ib_done(p: Parser, q: Parser)
    requires
        modes_ok(p),
        rooted_mode(p.mode),
        keeps(p, q),
    ensures
        next_core(Outcome::Done(q)),
{
    if !q.stopped {
        lemma_finish(p, q, q);
    }
}

/// Pop the current node when it is not `html` (nor a cell).
pub proof fn lemma_pop_not_html(p: Parser)
    requires
        good(p),
        !p.stopped,
        p.open.len() > 0,
        !is_html(current_node(p), Tag::Html),
        !cell_pred()(current_node(p)),
    ensures
        keeps(p, pop(p)),
{
    lemma_pop_keeps(p);
}

/// The text cases: "text" over the current mode.
pub proof fn lemma_ib_text(p: Parser, q: Parser, tt: TagTok, rawtext: bool)
    requires
        modes_ok(p),
        rooted_mode(p.mode),
        keeps(p, q),
        tok_tagged(tt),
        tt.tag != Tag::Td && tt.tag != Tag::Th,
        tt.tag != Tag::Template,
    ensures
        next_core(Outcome::Done(generic_text_parsing(q, tt, rawtext))),
{
    lemma_keeps_live(p, q);
    if !q.stopped {
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
        lemma_generic_text_reach(q, tt, rawtext);
    } else {
        lemma_insert_html_keeps(q, tt);
    }
}

// ---------------------------------------------------------------------
// Start tags

/// Case 7, `html`.
pub proof fn lemma_ib_html(p: Parser, tt: TagTok)
    requires
        reach_core(p),
        modes_ok(p),
        !p.stopped,
    ensures
        next_core(Outcome::Done(in_body_start_html(p, tt))),
{
    if !open_has_html(p, Tag::Template) {
        lemma_add_missing_frame(p, p.open[0].id, tt.attrs, 0);
        lemma_core_frame(p, in_body_start_html(p, tt));
    }
}

/// [`add_missing_attributes`] changes only the document (keeping its size).
pub proof fn lemma_add_missing_frame(p: Parser, el: NodeId, attrs: Seq<Attr>, i: int)
    ensures
        add_missing_attributes(p, el, attrs, i) == (Parser { doc: add_missing_attributes(p, el, attrs, i).doc, ..p }),
        add_missing_attributes(p, el, attrs, i).doc.nodes.len() == p.doc.nodes.len(),
    decreases attrs.len() - i,
{
    if !(i < 0 || i >= attrs.len()) {
        let a = attrs[i];
        let q = if !p.stopped && !element_has_attribute_named(p.doc, el, a.local_name) {
            Parser { doc: dom::append_attribute(p.doc, el, a), ..p }
        } else {
            p
        };
        lemma_add_missing_frame(q, el, attrs, i + 1);
    }
}

/// Case 9, `body`.
pub proof fn lemma_ib_body(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
    ensures
        next_core(Outcome::Done(in_body_start_body(p, tt))),
{
    if !(p.open.len() == 1 || !is_html(p.open[1], Tag::Body) || open_has_html(p, Tag::Template)) {
        let q = frameset_not_ok(p);
        lemma_flags_keeps(p, q);
        lemma_add_missing_keeps(q, q.open[1].id, tt.attrs, 0);
        lemma_keeps_trans(p, q, add_missing_attributes(q, q.open[1].id, tt.attrs, 0));
        lemma_ib_done(p, in_body_start_body(p, tt));
    } else {
        lemma_keeps_refl(p);
        lemma_ib_done(p, p);
    }
}

/// Case 10, `frameset` (proven on the parser put in the "in body" mode:
/// in the "in cell" mode it pops the cell, and switches to "in
/// frameset").
pub proof fn lemma_ib_frameset(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Frameset,
    ensures
        next_core(Outcome::Done(in_body_start_frameset(p, tt))),
{
    if p.open.len() == 1 || !is_html(p.open[1], Tag::Body) || !p.frameset_ok {
        lemma_keeps_refl(p);
        lemma_ib_done(p, p);
    } else {
        let p0 = mode_as(p, Mode::InBody);
        assert(good(p0));
        lemma_ib_frameset0(p0, tt);
        let q1 = dom_remove(p, p.open[1].id);
        let q2 = Parser { open: q1.open.take(1), ..q1 };
        assert(dom_remove(p0, p0.open[1].id) == mode_as(q1, Mode::InBody));
        assert(Parser { open: q1.open.take(1), ..mode_as(q1, Mode::InBody) } == mode_as(q2, Mode::InBody));
        lemma_insert_html_mode(q2, tt, Mode::InBody);
        assert(in_body_start_frameset(p0, tt) == in_body_start_frameset(p, tt));
    }
}

/// [`appropriate_place`] does not read the mode.
pub proof fn lemma_place_mode(p: Parser, m: Mode)
    ensures
        appropriate_place(mode_as(p, m), None) == appropriate_place(p, None),
        adjusted_location(mode_as(p, m), None) == adjusted_location(p, None),
{
}

/// [`create`] does not read the mode.
pub proof fn lemma_create_mode(p: Parser, k: NodeKind, m: Mode)
    ensures
        create(mode_as(p, m), k) == (mode_as(create(p, k).0, m), create(p, k).1),
{
}

/// [`create_element_for_token`] does not read the mode.
pub proof fn lemma_ceft_mode(p: Parser, tt: TagTok, ns: Namespace, ip: NodeId, m: Mode)
    ensures
        create_element_for_token(mode_as(p, m), tt, ns, ip) == (
            mode_as(create_element_for_token(p, tt, ns, ip).0, m),
            create_element_for_token(p, tt, ns, ip).1,
        ),
{
    hide(create);
    hide(same_tree);
    hide(parsing_template_contents);
    let pm = mode_as(p, m);
    assert(parsing_template_contents(pm) == parsing_template_contents(p)) by {
        reveal(parsing_template_contents);
    }
    let owner = if is_form_associated(ns, tt.tag) && p.form is Some && !parsing_template_contents(p) && p.context is None && (
    !is_listed(ns, tt.tag) || !has_attr(tt, name_form())) && same_tree(p.doc, ip, p.form->Some_0) {
        p.form
    } else {
        None
    };
    let k = NodeKind::Element {
        namespace: Some(ns),
        prefix: None,
        local_name: tt.name,
        attributes: tt.attrs,
        template_contents: None,
        form_owner: owner,
    };
    lemma_create_mode(p, k, m);
}

/// [`insert_element_at`] does not read the mode.
pub proof fn lemma_iea_mode(p: Parser, el: NodeId, m: Mode)
    ensures
        insert_element_at(mode_as(p, m), el, None) == mode_as(insert_element_at(p, el, None), m),
{
    hide(dom_insert);
    hide(appropriate_place);
    lemma_place_mode(p, m);
    assert(dom_insert(mode_as(p, m), el, adjusted_location(p, None).parent, adjusted_location(p, None).child) == mode_as(
        dom_insert(p, el, adjusted_location(p, None).parent, adjusted_location(p, None).child),
        m,
    )) by {
        reveal(dom_insert);
    }
}

/// [`insert_html_element`] does not read the mode.
pub proof fn lemma_insert_html_mode(p: Parser, tt: TagTok, m: Mode)
    ensures
        insert_html_element(mode_as(p, m), tt).0 == mode_as(insert_html_element(p, tt).0, m),
        insert_html_element(mode_as(p, m), tt).1 == insert_html_element(p, tt).1,
{
    hide(appropriate_place);
    hide(create_element_for_token);
    hide(insert_element_at);
    let pm = mode_as(p, m);
    lemma_place_mode(p, m);
    let ip = appropriate_place(p, None).parent;
    lemma_ceft_mode(p, tt, Namespace::Html, ip, m);
    let (p1, e) = create_element_for_token(p, tt, Namespace::Html, ip);
    lemma_iea_mode(p1, e.id, m);
    let p2 = insert_element_at(p1, e.id, None);
    assert(push(mode_as(p2, m), e) == mode_as(push(p2, e), m));
}

/// [`lemma_ib_frameset`] outside the "in cell" mode.
pub proof fn lemma_ib_frameset0(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Frameset,
        p.mode != Mode::InCell,
    ensures
        next_core(Outcome::Done(in_body_start_frameset(p, tt))),
{
    if p.open.len() == 1 || !is_html(p.open[1], Tag::Body) || !p.frameset_ok {
        lemma_keeps_refl(p);
        lemma_ib_done(p, p);
    } else {
        let q1 = dom_remove(p, p.open[1].id);
        lemma_dom_remove_keeps(p, p.open[1].id);
        let q2 = Parser { open: q1.open.take(1), ..q1 };
        lemma_prefix_keeps(q1, q2);
        lemma_keeps_trans(p, q1, q2);
        lemma_then_insert(p, q2, tt);
        let q3 = insert_html_element(q2, tt).0;
        lemma_finish(p, q3, Parser { mode: Mode::InFrameset, ..q3 });
    }
}

/// Case 15, h1 to h6.
pub proof fn lemma_ib_heading(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        is_heading_tag(tt.tag),
    ensures
        next_core(Outcome::Done(in_body_start_heading(p, tt))),
{
    lemma_keeps_refl(p);
    lemma_then_close_p_if(p, p);
    let q = close_p_if_in_button_scope(p);
    let q1 = if q.open.len() > 0 && is_heading(current_node(q)) {
        pop(q)
    } else {
        q
    };
    if q.open.len() > 0 && is_heading(current_node(q)) {
        lemma_keeps_live(p, q);
        if !q.stopped {
            lemma_pop_not_html(q);
        } else {
            lemma_pop_keeps(q);
        }
        lemma_keeps_trans(p, q, q1);
    }
    lemma_then_insert(p, q1, tt);
    lemma_ib_done(p, in_body_start_heading(p, tt));
}

/// Case 17, `form`.
pub proof fn lemma_ib_form(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Form,
    ensures
        next_core(Outcome::Done(in_body_start_form(p, tt))),
{
    if p.form is Some && !parsing_template_contents(p) {
        lemma_keeps_refl(p);
        lemma_ib_done(p, p);
    } else {
        lemma_keeps_refl(p);
        lemma_then_close_p_if(p, p);
        let q = close_p_if_in_button_scope(p);
        lemma_keeps_live(p, q);
        lemma_then_insert(p, q, tt);
        let (q1, e) = insert_html_element(q, tt);
        if !q1.stopped && !parsing_template_contents(q) {
            lemma_insert_html_keeps(q, tt);
            let q2 = Parser { form: Some(e.id), ..q1 };
            assert(e.id as int >= q.doc.nodes.len());
            assert(good(q2));
            lemma_finish(p, q1, q1);
            assert(modes_ok(q2) == modes_ok(q1));
        } else {
            lemma_ib_done(p, q1);
        }
    }
}

/// Cases 18 and 19, `li`, `dd` and `dt`.
pub proof fn lemma_ib_li_dd(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt,
    ensures
        tt.tag == Tag::Li ==> next_core(Outcome::Done(in_body_start_li(p, tt))),
        tt.tag != Tag::Li ==> next_core(Outcome::Done(in_body_start_dd_dt(p, tt))),
{
    let q = frameset_not_ok(p);
    lemma_flags_keeps(p, q);
    let q1 = if tt.tag == Tag::Li {
        li_loop(q, q.open.len() - 1)
    } else {
        dd_dt_loop(q, q.open.len() - 1)
    };
    if tt.tag == Tag::Li {
        lemma_li_loop_keeps(q, q.open.len() - 1);
    } else {
        lemma_dd_dt_loop_keeps(q, q.open.len() - 1);
    }
    lemma_keeps_trans(p, q, q1);
    lemma_then_close_p_if(p, q1);
    lemma_then_insert(p, close_p_if_in_button_scope(q1), tt);
    lemma_ib_done(p, insert_html_element(close_p_if_in_button_scope(q1), tt).0);
}

/// Case 21, `button`.
pub proof fn lemma_ib_button(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Button,
    ensures
        next_core(Outcome::Done(in_body_start_button(p, tt))),
{
    let q = if has_in_scope(p, Tag::Button, Scope::Default) {
        pop_until_popped(generate_implied_end_tags(p, None), Tag::Button)
    } else {
        p
    };
    if has_in_scope(p, Tag::Button, Scope::Default) {
        let f = |e: Elem| is_html(e, Tag::Button);
        let k = lemma_scope_k(p.open, f, Scope::Default);
        crate::exec::stack::lemma_pop_until_popped(generate_implied_end_tags(p, None), Tag::Button);
        lemma_close_keeps(p, None, f, k);
    } else {
        lemma_keeps_refl(p);
    }
    lemma_then_reconstruct(p, q);
    lemma_then_insert(p, reconstruct_formatting(q), tt);
    lemma_then_fno(p, insert_html_element(reconstruct_formatting(q), tt).0);
    lemma_ib_done(p, in_body_start_button(p, tt));
}

/// Push a fresh formatting element onto the list.
pub proof fn lemma_then_push_formatting(p: Parser, q: Parser, tt: TagTok)
    requires
        keeps(p, q),
        tok_tagged(tt),
        tt.tag != Tag::Template,
        tt.tag != Tag::Td && tt.tag != Tag::Th,
    ensures
        keeps(p, push_formatting(insert_html_element(q, tt).0, insert_html_element(q, tt).1, tt)),
{
    lemma_then_insert(p, q, tt);
    lemma_keeps_live(p, q);
    lemma_insert_html_keeps(q, tt);
    let (q1, e) = insert_html_element(q, tt);
    lemma_keeps_live(p, q1);
    if !q1.stopped {
        assert(e.id != q1.open[0].id);
    }
    lemma_push_formatting_keeps(q1, e, tt);
    lemma_keeps_trans(p, q1, push_formatting(q1, e, tt));
}

/// Case 29's removal of the `a` element (whose id `a_id` is not the last
/// cell's in the "in cell" mode) from the list and the stack.
pub proof fn lemma_a_remove(p: Parser, q1: Parser, a_id: NodeId)
    requires
        good(p),
        !p.stopped,
        keeps(p, q1),
        !q1.stopped,
        a_id != p.open[0].id,
        in_cell(p) ==> p.open[last_cell(p.open)].id != a_id,
    ensures
        ({
            let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a_id);
            let q2 = if k >= 0 {
                Parser { formatting: q1.formatting.remove(k), ..q1 }
            } else {
                q1
            };
            let j = open_index_of(q2, a_id);
            keeps(
                p,
                if j >= 0 {
                    remove_open_at(q2, j)
                } else {
                    q2
                },
            )
        }),
{
    lemma_keeps_live(p, q1);
    let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a_id);
    let q2 = if k >= 0 {
        Parser { formatting: q1.formatting.remove(k), ..q1 }
    } else {
        q1
    };
    if k >= 0 {
        crate::exec::modes::adoption::lemma_fmt_index_of(q1.formatting, q1.formatting.len() as int, a_id);
        lemma_fmt_remove_keeps(q1, k);
        lemma_keeps_trans(p, q1, q2);
    }
    let ff = id_is(a_id);
    let j = open_index_of(q2, a_id);
    assert(j == last_index_where(q2.open, q2.open.len() as int, ff));
    if j >= 0 {
        crate::termination::helpers_ranking::lemma_last_index_where(q2.open, q2.open.len() as int, ff);
        assert(j != 0);
        assert(q2.open[j].id == a_id);
        lemma_keeps_live(p, q2);
        if in_cell(q2) {
            assert(in_cell(p));
            assert(q2.open[last_cell(q2.open)] == p.open[last_cell(p.open)]);
        }
        lemma_remove_open_keeps(q2, j);
        lemma_keeps_trans(p, q2, remove_open_at(q2, j));
    } else {
        lemma_keeps_live(p, q2);
    }
}

/// Case 29, `a`.
pub proof fn lemma_ib_a(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::A,
    ensures
        next_core(Outcome::Done(in_body_start_a(p, tt))),
{
    hide(in_body_adoption);
    let f = p.formatting;
    let i = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| is_html(e, Tag::A));
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
    if i >= 0 {
        crate::exec::modes::in_body_start_lemmas::lemma_after_last_marker_nonneg(f, f.len() as int);
        crate::exec::modes::in_body_start_lemmas::lemma_fmt_last_where(
            f,
            after_last_marker(f, f.len() as int),
            f.len() as int,
            |e: Elem| is_html(e, Tag::A),
        );
        let a = f[i]->Entry_elem;
        lemma_fmt_entries_fresh(p, i);
        lemma_cell_top(p.open);
        if in_cell(p) {
            assert(cell_fresh(p, p.open[last_cell(p.open)].id));
            assert(f[i] is Entry);
        }
        lemma_in_body_adoption_keeps(p, tt);
        let q1 = in_body_adoption(p, tt);
        if !q1.stopped {
            lemma_a_remove(p, q1, a.id);
        }
    } else {
        lemma_keeps_refl(p);
    }
    lemma_then_reconstruct(p, q);
    lemma_then_push_formatting(p, reconstruct_formatting(q), tt);
    lemma_ib_done(p, in_body_start_a(p, tt));
}

/// Case 31, `nobr`.
pub proof fn lemma_ib_nobr(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Nobr,
    ensures
        next_core(Outcome::Done(in_body_start_nobr(p, tt))),
{
    hide(in_body_adoption);
    lemma_keeps_refl(p);
    lemma_then_reconstruct(p, p);
    let q = reconstruct_formatting(p);
    let q1 = if has_in_scope(q, Tag::Nobr, Scope::Default) {
        reconstruct_formatting(in_body_adoption(q, tt))
    } else {
        q
    };
    if has_in_scope(q, Tag::Nobr, Scope::Default) {
        lemma_keeps_live(p, q);
        lemma_in_body_adoption_keeps(q, tt);
        lemma_keeps_trans(p, q, in_body_adoption(q, tt));
        lemma_then_reconstruct(p, in_body_adoption(q, tt));
    }
    lemma_then_push_formatting(p, q1, tt);
    lemma_ib_done(p, in_body_start_nobr(p, tt));
}

/// Case 38, `input`.
pub proof fn lemma_ib_input(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Input,
    ensures
        next_core(Outcome::Done(in_body_start_input(p, tt))),
{
    if p.context is Some && is_html(p.context->Some_0, Tag::Select) {
        lemma_keeps_refl(p);
        lemma_ib_done(p, p);
    } else {
        let q = if has_in_scope(p, Tag::Select, Scope::Default) {
            pop_until_popped(p, Tag::Select)
        } else {
            p
        };
        if has_in_scope(p, Tag::Select, Scope::Default) {
            let k = lemma_scope_k(p.open, |e: Elem| is_html(e, Tag::Select), Scope::Default);
            lemma_pop_until_popped_keeps(p, Tag::Select, k);
        } else {
            lemma_keeps_refl(p);
        }
        lemma_then_reconstruct(p, q);
        lemma_then_insert_pop(p, reconstruct_formatting(q), tt);
        let q1 = insert_and_pop(reconstruct_formatting(q), tt);
        lemma_then_fno(p, q1);
        lemma_ib_done(p, in_body_start_input(p, tt));
    }
}

/// Case 40, `hr`.
pub proof fn lemma_ib_hr(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Hr,
    ensures
        next_core(Outcome::Done(in_body_start_hr(p, tt))),
{
    lemma_keeps_refl(p);
    lemma_then_close_p_if(p, p);
    let q = close_p_if_in_button_scope(p);
    let q1 = if has_in_scope(q, Tag::Select, Scope::Default) {
        generate_implied_end_tags(q, None)
    } else {
        q
    };
    if has_in_scope(q, Tag::Select, Scope::Default) {
        lemma_keeps_live(p, q);
        lemma_implied_keeps(q, None);
        lemma_keeps_trans(p, q, q1);
    }
    lemma_then_insert_pop(p, q1, tt);
    lemma_then_fno(p, insert_and_pop(q1, tt));
    lemma_ib_done(p, in_body_start_hr(p, tt));
}

/// Case 42, `textarea`.
pub proof fn lemma_ib_textarea(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Textarea,
    ensures
        next_core(Outcome::Done(in_body_start_textarea(p, tt))),
{
    lemma_insert_html_keeps(p, tt);
    let (q, e) = insert_html_element(p, tt);
    let r = in_body_start_textarea(p, tt);
    if !r.stopped {
        assert(r.open == p.open.push(e));
        assert(r.open.drop_last() == p.open);
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, r);
    }
}

/// Cases 46 to 48, `select`, `option`, `optgroup`.
pub proof fn lemma_ib_select(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Select || tt.tag == Tag::Option || tt.tag == Tag::Optgroup,
    ensures
        tt.tag == Tag::Select ==> next_core(Outcome::Done(in_body_start_select(p, tt))),
        tt.tag == Tag::Option ==> next_core(Outcome::Done(in_body_start_option(p, tt))),
        tt.tag == Tag::Optgroup ==> next_core(Outcome::Done(in_body_start_optgroup(p, tt))),
{
    let in_sel = has_in_scope(p, Tag::Select, Scope::Default);
    if tt.tag == Tag::Select {
        if p.context is Some && is_html(p.context->Some_0, Tag::Select) {
            lemma_keeps_refl(p);
            lemma_ib_done(p, p);
        } else if in_sel {
            let k = lemma_scope_k(p.open, |e: Elem| is_html(e, Tag::Select), Scope::Default);
            lemma_pop_until_popped_keeps(p, Tag::Select, k);
            lemma_ib_done(p, pop_until_popped(p, Tag::Select));
        } else {
            lemma_keeps_refl(p);
            lemma_then_reconstruct(p, p);
            lemma_then_insert(p, reconstruct_formatting(p), tt);
            lemma_then_fno(p, insert_html_element(reconstruct_formatting(p), tt).0);
            lemma_ib_done(p, in_body_start_select(p, tt));
        }
    } else {
        let except = if tt.tag == Tag::Option {
            Some(Tag::Optgroup)
        } else {
            None
        };
        let q = if in_sel {
            generate_implied_end_tags(p, except)
        } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
            pop(p)
        } else {
            p
        };
        if in_sel {
            lemma_implied_keeps(p, except);
        } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
            lemma_pop_not_html(p);
        } else {
            lemma_keeps_refl(p);
        }
        lemma_then_reconstruct(p, q);
        lemma_then_insert(p, reconstruct_formatting(q), tt);
        if tt.tag == Tag::Option {
            lemma_ib_done(p, in_body_start_option(p, tt));
        } else {
            lemma_ib_done(p, in_body_start_optgroup(p, tt));
        }
    }
}

/// Cases 51 and 52, `math` and `svg`.
pub proof fn lemma_ib_foreign(p: Parser, tt: TagTok)
    requires
        ib_pre(p, tt),
        tt.tag == Tag::Math || tt.tag == Tag::Svg,
    ensures
        tt.tag == Tag::Math ==> next_core(Outcome::Done(in_body_start_math(p, tt))),
        tt.tag == Tag::Svg ==> next_core(Outcome::Done(in_body_start_svg(p, tt))),
{
    lemma_keeps_refl(p);
    lemma_then_reconstruct(p, p);
    let q = reconstruct_formatting(p);
    lemma_keeps_live(p, q);
    let (ns, t2) = if tt.tag == Tag::Math {
        (Namespace::MathMl, adjust_foreign_attributes(adjust_mathml_attributes(tt)))
    } else {
        (Namespace::Svg, adjust_foreign_attributes(adjust_svg_attributes(tt)))
    };
    assert(t2.name == tt.name && t2.tag == tt.tag);
    lemma_insert_foreign_keeps(q, t2, ns);
    let q1 = insert_foreign_element(q, t2, ns).0;
    lemma_keeps_trans(p, q, q1);
    if tt.self_closing && !q1.stopped {
        lemma_keeps_live(p, q1);
        assert(q1.open.len() >= 2);
        lemma_pop_keeps(q1);
        lemma_keeps_trans(p, q1, pop(q1));
        lemma_ib_done(p, pop(q1));
    } else {
        lemma_ib_done(p, q1);
    }
}

/// "Generate implied end tags", then insert (cases 49 and 50).
pub proof fn lemma_ib_ruby(p: Parser, tt: TagTok, except: Option<Tag>)
    requires
        ib_pre(p, tt),
        tt.tag != Tag::Template,
        tt.tag != Tag::Td && tt.tag != Tag::Th,
    ensures
        next_core(Outcome::Done(insert_html_element(if has_in_scope(p, Tag::Ruby, Scope::Default) {
            generate_implied_end_tags(p, except)
        } else {
            p
        }, tt).0)),
{
    let q = if has_in_scope(p, Tag::Ruby, Scope::Default) {
        generate_implied_end_tags(p, except)
    } else {
        p
    };
    if has_in_scope(p, Tag::Ruby, Scope::Default) {
        lemma_implied_keeps(p, except);
    } else {
        lemma_keeps_refl(p);
    }
    lemma_then_insert(p, q, tt);
    lemma_ib_done(p, insert_html_element(q, tt).0);
}

} // verus!
