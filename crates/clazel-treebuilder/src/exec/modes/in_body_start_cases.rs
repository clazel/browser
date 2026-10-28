//! HTML §13.2.6.4.7 the "in body" insertion mode: the start tag cases that
//! are their own spec functions in `spec/modes/in_body.rs`, "close a p
//! element", and the helpers they share, over [`ParserBuf`]. Each function
//! is proven equal to the spec function it names and to keep
//! [`parser_inv`].
//!
//! Every case runs on a parser that has not stopped and whose stack of open
//! elements is rooted at the `html` element ([`stack_rooted`]), which the
//! insertions need; the pops of these cases never pop that element (the
//! lemmas of [`super::in_body_start_lemmas`]).

use super::adoption::*;
use super::in_body_end::*;
#[cfg(verus_only)]
use super::in_body_start_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
use crate::exec::insert::*;
use crate::exec::names::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[cfg(verus_only)]
use clazel_dom::exec::attrs_view;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Helpers

/// Whether [`qualified_name`] of `a` is `name`.
pub fn qualified_name_eq_exec(a: &ExecAttr, name: &[u32]) -> (r: bool)
    ensures
        r == (qualified_name(a@) == name@),
{
    match &a.prefix {
        None => u32s_eq(a.local_name.as_slice(), name),
        Some(px) => {
            let mut v = copy_str(px.as_slice());
            v.push(0x3au32);
            let ghost head = px@ + seq![0x3au32];
            let ln = a.local_name.as_slice();
            let mut j: usize = 0;
            while j < ln.len()
                invariant
                    j <= ln@.len(),
                    ln@ == a.local_name@,
                    v@ == head + ln@.subrange(0, j as int),
                decreases ln@.len() - j,
            {
                if let Some(c) = ln.get(j) {
                    v.push(*c);
                }
                proof {
                    assert(ln@.subrange(0, j + 1) =~= ln@.subrange(0, j as int).push(ln@[j as int]));
                }
                // Never saturates: j < ln.len().
                j = j.saturating_add(1);
            }
            proof {
                assert(ln@.subrange(0, ln@.len() as int) =~= ln@);
                assert(qualified_name(a@) =~= v@);
            }
            u32s_eq(v.as_slice(), name)
        },
    }
}

/// [`attrs_have_name`].
pub fn attrs_have_name_exec(attrs: &[ExecAttr], name: &[u32]) -> (r: bool)
    ensures
        r == attrs_have_name(attrs_view(attrs@), name@),
{
    let ghost all = attrs_view(attrs@);
    let n = attrs.len();
    let mut i: usize = 0;
    proof {
        assert(all.subrange(0, n as int) =~= all);
    }
    while i < n
        invariant
            n == attrs@.len(),
            i <= n,
            all == attrs_view(attrs@),
            attrs_have_name(all, name@) == attrs_have_name(all.subrange(i as int, n as int), name@),
        decreases n - i,
    {
        let a = match attrs.get(i) {
            Some(a) => a,
            None => vstd::pervasive::unreached(),
        };
        proof {
            let s = all.subrange(i as int, n as int);
            assert(s[0] == a@);
            assert(s.drop_first() =~= all.subrange(i + 1, n as int));
        }
        if qualified_name_eq_exec(a, name) {
            return true;
        }
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
    false
}

/// [`element_has_attribute_named`].
pub fn element_has_attribute_named_exec(arena: &Arena, el: usize, name: &[u32]) -> (r: bool)
    requires
        dom::valid(arena@, el),
    ensures
        r == element_has_attribute_named(arena@, el, name@),
{
    match arena.kind(el) {
        ExecKind::Element { attributes, .. } => attrs_have_name_exec(attributes.as_slice(), name),
        _ => false,
    }
}

/// [`add_missing_attributes`] from index 0: the `html` and `body` cases'
/// attribute loop.
pub fn add_missing_attributes_exec(p: &mut ParserBuf, el: usize, attrs: &[ExecAttr])
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        dom::valid(old(p)@.doc, el),
        old(p)@.doc.nodes[el as int].kind is Element,
    ensures
        final(p)@ == add_missing_attributes(old(p)@, el, attrs_view(attrs@), 0),
        parser_inv(final(p)@),
{
    let ghost all = attrs_view(attrs@);
    let n = attrs.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == attrs@.len(),
            i <= n,
            all == attrs_view(attrs@),
            parser_inv(p@),
            !p@.stopped,
            dom::valid(p@.doc, el),
            p@.doc.nodes[el as int].kind is Element,
            add_missing_attributes(p@, el, all, i as int) == add_missing_attributes(old(p)@, el, all, 0),
        decreases n - i,
    {
        let a = match attrs.get(i) {
            Some(a) => a,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(all[i as int] == a@);
        }
        if !element_has_attribute_named_exec(&p.arena, el, a.local_name.as_slice()) {
            let ghost p0 = p@;
            proof {
                lemma_inv_iff(p0);
            }
            p.arena.append_attribute(el, copy_attr(a));
            proof {
                lemma_append_attribute_extends(p0.doc, el, a@);
                clazel_dom::lemmas::theorem_append_attribute_wf(p0.doc, el, a@);
                lemma_inv_doc(p0, p@.doc);
                assert(p@ == Parser { doc: dom::append_attribute(p0.doc, el, a@), ..p0 });
            }
        }
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
}

/// The document is in quirks mode ([`doc_is_quirks`]).
pub fn doc_is_quirks_exec(p: &ParserBuf) -> (r: bool)
    requires
        parser_inv(p@),
    ensures
        r == doc_is_quirks(p@),
{
    proof {
        lemma_wf_nonempty(p@.doc);
    }
    match p.arena.kind(0) {
        ExecKind::Document { mode, .. } => matches!(mode, DocumentMode::Quirks),
        _ => false,
    }
}

/// The parser with the frameset-ok flag "not ok" ([`frameset_not_ok`]).
pub fn frameset_not_ok_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == frameset_not_ok(old(p)@),
        parser_inv(final(p)@),
{
    p.frameset_ok = false;
    proof {
        lemma_inv_iff(old(p)@);
        lemma_inv_iff(p@);
    }
}

/// "Close a p element" ([`close_p_element`]).
pub fn close_p_element_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == close_p_element(old(p)@),
        parser_inv(final(p)@),
        stack_rooted(old(p)@) && has_in_scope(old(p)@, Tag::P, Scope::Button) ==> stack_rooted(final(p)@) && final(p)@
            == with_open(old(p)@, final(p)@.open),
{
    // 1. "Generate implied end tags, except for p elements."
    generate_implied_end_tags_exec(p, Some(Tag::P));
    // 2. (a parse error) 3. "Pop elements from the stack of open elements
    // until a p element has been popped from the stack."
    pop_until_popped_exec(p, Tag::P);
    proof {
        if stack_rooted(old(p)@) && has_in_scope(old(p)@, Tag::P, Scope::Button) {
            lemma_close_p_rooted(old(p)@);
        }
    }
}

/// [`close_p_if_in_button_scope`].
pub fn close_p_if_in_button_scope_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == close_p_if_in_button_scope(old(p)@),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == with_open(old(p)@, final(p)@.open),
{
    if has_in_scope_exec(p, Tag::P, &Scope::Button) {
        close_p_element_exec(p);
    }
}

/// [`insert_and_pop`].
pub fn insert_and_pop_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == insert_and_pop(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let _ = insert_html_element_exec(p, tt);
    if !p.stopped {
        pop_exec(p);
    }
}

/// "Generate implied end tags, except for `except`" on a rooted stack: it
/// stays rooted.
pub fn generate_implied_rooted_exec(p: &mut ParserBuf, except: Option<Tag>)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == generate_implied_end_tags(old(p)@, except),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == with_open(old(p)@, final(p)@.open),
{
    proof {
        lemma_implied_rooted(old(p)@, except);
    }
    generate_implied_end_tags_exec(p, except);
}

/// Pop the current node if it is not the `html` element: the stack stays
/// rooted.
pub fn pop_rooted_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        !is_html(current_node(old(p)@), Tag::Html),
    ensures
        final(p)@ == pop(old(p)@),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == with_open(old(p)@, final(p)@.open),
{
    proof {
        lemma_pop_rooted(old(p)@);
    }
    pop_exec(p);
}

// ---------------------------------------------------------------------
// Cases 7, 9, 10: html, body, frameset

/// Case 7 ([`in_body_start_html`]).
pub fn in_body_start_html_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
    ensures
        final(p)@ == in_body_start_html(old(p)@, tt@),
        parser_inv(final(p)@),
{
    if open_has_html_exec(p, Tag::Template) {
        return ;
    }
    // 1.
    let first: usize = 0;
    let el = match p.open.get(first) {
        Some(e) => e.id,
        None => vstd::pervasive::unreached(),
    };
    proof {
        lemma_inv_iff(p@);
        assert(elem_ok(p@.doc, p@.open[0]));
    }
    // 2.
    add_missing_attributes_exec(p, el, tt.attrs.as_slice());
}

/// Case 9 ([`in_body_start_body`]).
pub fn in_body_start_body_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
    ensures
        final(p)@ == in_body_start_body(old(p)@, tt@),
        parser_inv(final(p)@),
{
    if p.open.len() == 1 {
        return ;
    }
    let el = match p.open.get(1) {
        Some(e) => {
            if !is_html_exec(e, &Tag::Body) {
                return ;
            }
            e.id
        },
        None => vstd::pervasive::unreached(),
    };
    if open_has_html_exec(p, Tag::Template) {
        return ;
    }
    proof {
        lemma_inv_iff(p@);
        assert(elem_ok(p@.doc, p@.open[1]));
    }
    // 1.
    frameset_not_ok_exec(p);
    // 2., 3.
    add_missing_attributes_exec(p, el, tt.attrs.as_slice());
}

/// Case 10's step 2: "Pop all the nodes from the bottom of the stack of
/// open elements, from the current node up to, but not including, the root
/// html element."
pub fn pop_to_root_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == (Parser { open: old(p)@.open.take(1), ..old(p)@ }),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
{
    let ghost q1 = p@;
    proof {
        assert(q1.open.take(q1.open.len() as int) =~= q1.open);
    }
    while p.open.len() > 1
        invariant
            parser_inv(p@),
            q1 == old(p)@,
            1 <= p@.open.len() <= q1.open.len(),
            p@ == (Parser { open: q1.open.take(p@.open.len() as int), ..q1 }),
        decreases p@.open.len(),
    {
        let ghost k = p@.open.len() as int;
        pop_exec(p);
        proof {
            assert(q1.open.take(k).drop_last() =~= q1.open.take(k - 1));
        }
    }
    proof {
        assert(p@.open[0] == q1.open[0]);
    }
}

/// Case 10 ([`in_body_start_frameset`]).
pub fn in_body_start_frameset_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Frameset,
    ensures
        final(p)@ == in_body_start_frameset(old(p)@, tt@),
        parser_inv(final(p)@),
{
    hide(insert_html_element);
    hide(insert_foreign_element);
    hide(parser_inv);
    if p.open.len() == 1 {
        return ;
    }
    let second = match p.open.get(1) {
        Some(e) => {
            if !is_html_exec(e, &Tag::Body) {
                return ;
            }
            e.id
        },
        None => vstd::pervasive::unreached(),
    };
    if !p.frameset_ok {
        return ;
    }
    // 1.
    dom_remove_exec(p, second);
    // 2.
    pop_to_root_exec(p);
    // 3.
    let _ = insert_html_element_exec(p, tt);
    // 4.
    proof {
        lemma_inv_iff(p@);
    }
    p.mode = Mode::InFrameset;
    proof {
        lemma_inv_iff(p@);
    }
}

// ---------------------------------------------------------------------
// Cases 14 to 21

/// Cases 14 and 20's first steps: close a p element if one is in button
/// scope, then insert an HTML element for the token.
pub fn close_p_insert_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == insert_html_element(close_p_if_in_button_scope(old(p)@), tt@).0,
        parser_inv(final(p)@),
        final(p)@.mode == old(p)@.mode,
{
    close_p_if_in_button_scope_exec(p);
    let _ = insert_html_element_exec(p, tt);
}

/// Case 15 ([`in_body_start_heading`]).
pub fn in_body_start_heading_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_heading(old(p)@, tt@),
        parser_inv(final(p)@),
{
    close_p_if_in_button_scope_exec(p);
    if !p.open.is_empty() && is_heading_exec(current_node_exec(p)) {
        pop_rooted_exec(p);
    }
    let _ = insert_html_element_exec(p, tt);
}

/// Case 16 ([`in_body_start_pre`]).
pub fn in_body_start_pre_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_pre(old(p)@, tt@),
        parser_inv(final(p)@),
{
    close_p_insert_exec(p, tt);
    proof {
        lemma_inv_iff(p@);
    }
    p.skip_lf = true;
    p.frameset_ok = false;
    proof {
        lemma_inv_iff(p@);
    }
}

/// Case 17 ([`in_body_start_form`]).
pub fn in_body_start_form_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_form(old(p)@, tt@),
        parser_inv(final(p)@),
{
    if p.form.is_some() && !parsing_template_contents_exec(p) {
        return ;
    }
    // 1.
    close_p_if_in_button_scope_exec(p);
    // 2.
    let ptc = parsing_template_contents_exec(p);
    let e = insert_html_element_exec(p, tt);
    if !p.stopped && !ptc {
        proof {
            lemma_inv_iff(p@);
            assert(elem_ok(p@.doc, p@.open[p@.open.len() - 1]));
        }
        p.form = Some(e.id);
        proof {
            lemma_inv_iff(p@);
        }
    }
}

/// Case 18's steps 2 to 5 ([`li_loop`] from the current node).
pub fn li_loop_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == li_loop(old(p)@, old(p)@.open.len() - 1),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == with_open(old(p)@, final(p)@.open),
{
    let ghost p0 = p@;
    let mut i: usize = p.open.len().saturating_sub(1);
    loop
        invariant
            p@ == p0,
            p0 == old(p)@,
            parser_inv(p0),
            stack_rooted(p0),
            i < p0.open.len(),
            li_loop(p0, i as int) == li_loop(p0, p0.open.len() - 1),
        decreases i,
    {
        let node = match p.open.get(i) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        if is_html_exec(node, &Tag::Li) {
            proof {
                assert(i != 0);
                lemma_close_rooted(p0, Some(Tag::Li), Tag::Li, i as int);
            }
            // 3.1 to 3.4
            generate_implied_end_tags_exec(p, Some(Tag::Li));
            pop_until_popped_exec(p, Tag::Li);
            return ;
        }
        if is_special_exec(node) && !is_html_exec(node, &Tag::Address) && !is_html_exec(node, &Tag::Div) && !is_html_exec(
            node,
            &Tag::P,
        ) {
            // 4.
            return ;
        }
        // 5. (node is not the html element, which is special.)
        proof {
            assert(i != 0);
        }
        i = i.saturating_sub(1);
    }
}

/// Case 18 ([`in_body_start_li`]).
pub fn in_body_start_li_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_li(old(p)@, tt@),
        parser_inv(final(p)@),
{
    // 1.
    frameset_not_ok_exec(p);
    // 2. to 5.
    li_loop_exec(p);
    // 6., 7.
    close_p_insert_exec(p, tt);
}

/// Case 19's steps 2 to 6 ([`dd_dt_loop`] from the current node).
pub fn dd_dt_loop_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == dd_dt_loop(old(p)@, old(p)@.open.len() - 1),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == with_open(old(p)@, final(p)@.open),
{
    let ghost p0 = p@;
    let mut i: usize = p.open.len().saturating_sub(1);
    loop
        invariant
            p@ == p0,
            p0 == old(p)@,
            parser_inv(p0),
            stack_rooted(p0),
            i < p0.open.len(),
            dd_dt_loop(p0, i as int) == dd_dt_loop(p0, p0.open.len() - 1),
        decreases i,
    {
        let node = match p.open.get(i) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        if is_html_exec(node, &Tag::Dd) {
            proof {
                assert(i != 0);
                lemma_close_rooted(p0, Some(Tag::Dd), Tag::Dd, i as int);
            }
            // 3.1 to 3.4
            generate_implied_end_tags_exec(p, Some(Tag::Dd));
            pop_until_popped_exec(p, Tag::Dd);
            return ;
        }
        if is_html_exec(node, &Tag::Dt) {
            proof {
                assert(i != 0);
                lemma_close_rooted(p0, Some(Tag::Dt), Tag::Dt, i as int);
            }
            // 4.1 to 4.4
            generate_implied_end_tags_exec(p, Some(Tag::Dt));
            pop_until_popped_exec(p, Tag::Dt);
            return ;
        }
        if is_special_exec(node) && !is_html_exec(node, &Tag::Address) && !is_html_exec(node, &Tag::Div) && !is_html_exec(
            node,
            &Tag::P,
        ) {
            // 5.
            return ;
        }
        // 6. (node is not the html element, which is special.)
        proof {
            assert(i != 0);
        }
        i = i.saturating_sub(1);
    }
}

/// Case 19 ([`in_body_start_dd_dt`]).
pub fn in_body_start_dd_dt_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_dd_dt(old(p)@, tt@),
        parser_inv(final(p)@),
{
    // 1.
    frameset_not_ok_exec(p);
    // 2. to 6.
    dd_dt_loop_exec(p);
    // 7., 8.
    close_p_insert_exec(p, tt);
}

/// Case 21 ([`in_body_start_button`]).
pub fn in_body_start_button_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_button(old(p)@, tt@),
        parser_inv(final(p)@),
{
    // 1.
    if has_in_scope_exec(p, Tag::Button, &Scope::Default) {
        proof {
            let k = lemma_scope_index(p@, Tag::Button, Scope::Default);
            lemma_close_rooted(p@, None, Tag::Button, k);
        }
        generate_implied_end_tags_exec(p, None);
        pop_until_popped_exec(p, Tag::Button);
    }
    // 2.
    reconstruct_formatting_exec(p);
    // 3.
    let _ = insert_html_element_exec(p, tt);
    // 4.
    frameset_not_ok_exec(p);
}

// ---------------------------------------------------------------------
// Cases 37 to 52

/// Case 37 ([`in_body_void_start_tag`]).
pub fn in_body_void_start_tag_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_void_start_tag(old(p)@, tt@),
        parser_inv(final(p)@),
{
    reconstruct_formatting_exec(p);
    insert_and_pop_exec(p, tt);
    frameset_not_ok_exec(p);
}

/// "type"
fn name_type_exec() -> (r: &'static [u32])
    ensures
        r@ == name_type(),
{
    let l: &[u32] = &[0x74u32, 0x79u32, 0x70u32, 0x65u32];
    proof {
        assert(l@ =~= name_type());
    }
    l
}

/// "hidden"
fn name_hidden_exec() -> (r: &'static [u32])
    ensures
        r@ == name_hidden(),
{
    let l: &[u32] = &[0x68u32, 0x69u32, 0x64u32, 0x64u32, 0x65u32, 0x6eu32];
    proof {
        assert(l@ =~= name_hidden());
    }
    l
}

/// Case 38 ([`in_body_start_input`]).
pub fn in_body_start_input_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_input(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let select_context = match &p.context {
        Some(c) => is_html_exec(c, &Tag::Select),
        None => false,
    };
    if select_context {
        return ;
    }
    if has_in_scope_exec(p, Tag::Select, &Scope::Default) {
        proof {
            let k = lemma_scope_index(p@, Tag::Select, Scope::Default);
            lemma_pop_until_rooted(p@, Tag::Select, k);
        }
        pop_until_popped_exec(p, Tag::Select);
    }
    reconstruct_formatting_exec(p);
    insert_and_pop_exec(p, tt);
    let hidden = match attr_value_exec(tt.attrs.as_slice(), name_type_exec()) {
        Some(v) => ascii_ci_eq_exec(v.as_slice(), name_hidden_exec()),
        None => false,
    };
    if !hidden {
        frameset_not_ok_exec(p);
    }
}

/// Case 40 ([`in_body_start_hr`]).
pub fn in_body_start_hr_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_hr(old(p)@, tt@),
        parser_inv(final(p)@),
{
    close_p_if_in_button_scope_exec(p);
    if has_in_scope_exec(p, Tag::Select, &Scope::Default) {
        generate_implied_rooted_exec(p, None);
    }
    insert_and_pop_exec(p, tt);
    frameset_not_ok_exec(p);
}

/// Case 42 ([`in_body_start_textarea`]).
pub fn in_body_start_textarea_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
    ensures
        final(p)@ == in_body_start_textarea(old(p)@, tt@),
        parser_inv(final(p)@),
{
    // 1.
    let _ = insert_html_element_exec(p, tt);
    proof {
        lemma_inv_iff(old(p)@);
        lemma_inv_iff(p@);
    }
    // 2.
    p.skip_lf = true;
    // 3.
    p.tokenizer = Some(TokenizerState::Rcdata);
    // 4.
    p.original_mode = copy_mode(&p.mode);
    // 5.
    p.frameset_ok = false;
    // 6.
    p.mode = Mode::Text;
    proof {
        lemma_inv_iff(p@);
    }
}

/// Case 46 ([`in_body_start_select`]).
pub fn in_body_start_select_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_select(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let select_context = match &p.context {
        Some(c) => is_html_exec(c, &Tag::Select),
        None => false,
    };
    if select_context {
        return ;
    }
    if has_in_scope_exec(p, Tag::Select, &Scope::Default) {
        pop_until_popped_exec(p, Tag::Select);
        return ;
    }
    reconstruct_formatting_exec(p);
    let _ = insert_html_element_exec(p, tt);
    frameset_not_ok_exec(p);
}

/// Cases 47 and 48's first step.
pub open spec fn option_prelude(p: Parser, except: Option<Tag>) -> Parser {
    if has_in_scope(p, Tag::Select, Scope::Default) {
        generate_implied_end_tags(p, except)
    } else if p.open.len() > 0 && is_html(current_node(p), Tag::Option) {
        pop(p)
    } else {
        p
    }
}

/// Cases 47 and 48's first step: with a select element in scope, generate
/// implied end tags (except for `except`); otherwise pop an option current
/// node.
pub fn option_prelude_exec(p: &mut ParserBuf, except: Option<Tag>)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == option_prelude(old(p)@, except),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == with_open(old(p)@, final(p)@.open),
{
    if has_in_scope_exec(p, Tag::Select, &Scope::Default) {
        generate_implied_rooted_exec(p, except);
    } else if !p.open.is_empty() && is_html_exec(current_node_exec(p), &Tag::Option) {
        pop_rooted_exec(p);
    }
}

/// Case 47 ([`in_body_start_option`]).
pub fn in_body_start_option_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_option(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let ghost p0 = p@;
    proof {
        assert(in_body_start_option(p0, tt@) == insert_html_element(reconstruct_formatting(option_prelude(p0, Some(Tag::Optgroup))), tt@).0);
    }
    option_prelude_exec(p, Some(Tag::Optgroup));
    reconstruct_formatting_exec(p);
    let _ = insert_html_element_exec(p, tt);
}

/// Case 48 ([`in_body_start_optgroup`]).
pub fn in_body_start_optgroup_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == in_body_start_optgroup(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let ghost p0 = p@;
    proof {
        assert(in_body_start_optgroup(p0, tt@) == insert_html_element(reconstruct_formatting(option_prelude(p0, None)), tt@).0);
    }
    option_prelude_exec(p, None);
    reconstruct_formatting_exec(p);
    let _ = insert_html_element_exec(p, tt);
}

/// Cases 49 and 50: with a ruby element in scope, generate implied end tags
/// (except for `except`); then insert an HTML element for the token.
pub fn in_body_start_ruby_exec(p: &mut ParserBuf, tt: &ExecTagTok, except: Option<Tag>)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == insert_html_element(
            if has_in_scope(old(p)@, Tag::Ruby, Scope::Default) {
                generate_implied_end_tags(old(p)@, except)
            } else {
                old(p)@
            },
            tt@,
        ).0,
        parser_inv(final(p)@),
{
    if has_in_scope_exec(p, Tag::Ruby, &Scope::Default) {
        generate_implied_rooted_exec(p, except);
    }
    let _ = insert_html_element_exec(p, tt);
}

/// Case 51 ([`in_body_start_math`]).
pub fn in_body_start_math_exec(p: &mut ParserBuf, tt: ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
    ensures
        final(p)@ == in_body_start_math(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let sc = tt.self_closing;
    reconstruct_formatting_exec(p);
    let mut t2 = tt;
    adjust_mathml_attributes_exec(&mut t2);
    adjust_foreign_attributes_exec(&mut t2);
    let _ = insert_foreign_element_exec(p, &t2, Namespace::MathMl);
    if sc && !p.stopped {
        pop_exec(p);
    }
}

/// Case 52 ([`in_body_start_svg`]).
pub fn in_body_start_svg_exec(p: &mut ParserBuf, tt: ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
    ensures
        final(p)@ == in_body_start_svg(old(p)@, tt@),
        parser_inv(final(p)@),
{
    let sc = tt.self_closing;
    reconstruct_formatting_exec(p);
    let mut t2 = tt;
    adjust_svg_attributes_exec(&mut t2);
    adjust_foreign_attributes_exec(&mut t2);
    let _ = insert_foreign_element_exec(p, &t2, Namespace::Svg);
    if sc && !p.stopped {
        pop_exec(p);
    }
}

// ---------------------------------------------------------------------
// Formatting elements: cases 29 to 31

/// Insert an HTML element for the token and push it onto the list of
/// active formatting elements (cases 29 to 31's last steps).
pub fn insert_push_formatting_exec(p: &mut ParserBuf, tt: ExecTagTok)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == push_formatting(insert_html_element(old(p)@, tt@).0, insert_html_element(old(p)@, tt@).1, tt@),
        parser_inv(final(p)@),
{
    let e = insert_html_element_exec(p, &tt);
    proof {
        if !p@.stopped {
            lemma_inv_iff(p@);
            assert(elem_ok(p@.doc, p@.open[p@.open.len() - 1]));
        }
    }
    push_formatting_exec(p, e, tt);
}

/// "Run the adoption agency algorithm for the token", acting as the "any
/// other end tag" entry describes when its step 4.3 says so
/// ([`in_body_adoption`]).
pub fn in_body_adoption_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Html,
    ensures
        final(p)@ == in_body_adoption(old(p)@, tt@),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        doc_extends(old(p)@.doc, final(p)@.doc),
{
    match adoption_agency_exec(env, p, tt) {
        ExecAdoptionOutcome::Done => {},
        ExecAdoptionOutcome::AnyOtherEndTag => in_body_any_other_end_tag_exec(p, tt),
    }
}

/// Case 29's predicate: an HTML `a` element.
pub open spec fn a_pred() -> spec_fn(Elem) -> bool {
    |e: Elem| is_html(e, Tag::A)
}

/// [`a_pred`] is the predicate case 29 writes in place.
pub proof fn lemma_a_pred()
    ensures
        forall|e: Elem| #[trigger] a_pred()(e) == is_html(e, Tag::A),
        a_pred() == (|e: Elem| is_html(e, Tag::A)),
{
    assert(a_pred() =~= (|e: Elem| is_html(e, Tag::A)));
}

/// The index of the last `a` element entry after the last marker
/// (case 29's [`fmt_last_where`]): `Some` of it, or `None` for -1.
pub fn last_a_after_marker_exec(f: &[ExecFmt]) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < f@.len() && i as int == fmt_last_where(
                fmts_view(f@),
                after_last_marker(fmts_view(f@), f@.len() as int),
                f@.len() as int,
                |e: Elem| is_html(e, Tag::A),
            ),
            None => fmt_last_where(
                fmts_view(f@),
                after_last_marker(fmts_view(f@), f@.len() as int),
                f@.len() as int,
                |e: Elem| is_html(e, Tag::A),
            ) == -1,
        },
{
    let ghost fv = fmts_view(f@);
    proof {
        lemma_a_pred();
    }
    let from = after_last_marker_exec(f);
    let mut i = f.len();
    while i > from
        invariant
            from <= i <= f@.len(),
            fv == fmts_view(f@),
            from as int == after_last_marker(fv, f@.len() as int),
            fmt_last_where(fv, from as int, f@.len() as int, a_pred()) == fmt_last_where(fv, from as int, i as int, a_pred()),
        decreases i,
    {
        let k = i.saturating_sub(1);
        let x = match f.get(k) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        };
        proof {
            lemma_a_pred();
            assert(fv[k as int] == x@);
        }
        let hit = match x {
            ExecFmt::Entry { elem, .. } => is_html_exec(elem, &Tag::A),
            ExecFmt::Marker => false,
        };
        proof {
            match x {
                ExecFmt::Entry { elem, .. } => {
                    assert(fv[k as int] is Entry);
                    assert(fv[k as int]->Entry_elem == elem@);
                    assert(a_pred()(elem@) == is_html(elem@, Tag::A));
                },
                ExecFmt::Marker => {
                    assert(!(fv[k as int] is Entry));
                },
            }
            assert(hit == (fv[k as int] is Entry && a_pred()(fv[k as int]->Entry_elem)));
        }
        if hit {
            return Some(k);
        }
        i = k;
    }
    proof {
        lemma_a_pred();
    }
    None
}

/// [`in_body_start_a`]'s removal step after the adoption agency algorithm.
pub open spec fn a_remove(q1: Parser, a_id: NodeId) -> Parser {
    let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a_id);
    let q2 = if k >= 0 {
        Parser { formatting: q1.formatting.remove(k), ..q1 }
    } else {
        q1
    };
    let j = open_index_of(q2, a_id);
    if j >= 0 {
        remove_open_at(q2, j)
    } else {
        q2
    }
}

/// Case 29's step after the adoption agency algorithm: "remove that
/// element from the list of active formatting elements and the stack of
/// open elements if the adoption agency algorithm didn't already remove
/// it". The element `a` was an HTML `a` element of the document `d0`, which
/// the current document extends, so it is not the root `html` element.
pub fn a_remove_exec(p: &mut ParserBuf, a_id: usize, Ghost(a): Ghost<Elem>, Ghost(d0): Ghost<Document>)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        a.id == a_id,
        elem_in_doc(d0, a),
        elem_tagged(a),
        is_html(a, Tag::A),
        doc_extends(d0, old(p)@.doc),
    ensures
        final(p)@ == a_remove(old(p)@, a_id),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
{
    let ghost q1 = p@;
    let n = p.formatting.len();
    if let Some(k) = fmt_index_of_exec(p.formatting.as_slice(), n, a_id) {
        let ghost v = p.formatting@;
        proof {
            lemma_inv_iff(q1);
        }
        let _ = p.formatting.remove(k);
        proof {
            assert(fmts_view(p.formatting@) =~= fmts_view(v).remove(k as int));
            lemma_fmts_remove(q1.doc, fmts_view(v), k as int);
            lemma_inv_iff(p@);
        }
    }
    let ghost q2 = p@;
    if let Some(j) = open_index_of_exec(p, a_id) {
        proof {
            // The html element at the root is not a: its node has the name
            // of `html`, a's node keeps a's name.
            lemma_last_index_where(q2.open, q2.open.len() as int, |e: Elem| e.id == a_id);
            if j == 0 {
                lemma_inv_iff(q2);
                assert(elem_ok(q2.doc, q2.open[0]));
                assert(kind_kept(d0.nodes[a_id as int].kind, q2.doc.nodes[a_id as int].kind));
                assert(false);
            }
        }
        remove_open_at_exec(p, j);
        proof {
            assert(p@.open[0] == q2.open[0]);
        }
    }
}

/// Case 29's first step when the entry `i` is the last `a` element entry
/// after the last marker: run the adoption agency algorithm for the token,
/// then remove that element from the list and the stack if it is still
/// there.
pub fn a_adopt_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: &ExecTagTok, i: usize)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::A,
        i as int == fmt_last_where(
            old(p)@.formatting,
            after_last_marker(old(p)@.formatting, old(p)@.formatting.len() as int),
            old(p)@.formatting.len() as int,
            |e: Elem| is_html(e, Tag::A),
        ),
    ensures
        ({
            let a = old(p)@.formatting[i as int]->Entry_elem;
            let q1 = in_body_adoption(old(p)@, tt@);
            final(p)@ == if q1.stopped {
                q1
            } else {
                a_remove(q1, a.id)
            }
        }),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
{
    hide(in_body_adoption);
    hide(a_remove);
    hide(parser_inv);
    hide(doc_extends);
    hide(stack_rooted);
    hide(fmt_last_where);
    hide(after_last_marker);
    let ghost p0 = p@;
    let ghost f0 = p0.formatting;
    proof {
        lemma_a_entry(p0, i as int);
    }
    let a_id = match p.formatting.get(i) {
        Some(x) => {
            proof {
                assert(f0[i as int] == x@);
            }
            match x {
                ExecFmt::Entry { elem, .. } => elem.id,
                ExecFmt::Marker => vstd::pervasive::unreached(),
            }
        },
        None => vstd::pervasive::unreached(),
    };
    let ghost a = f0[i as int]->Entry_elem;
    in_body_adoption_exec(env, p, tt);
    if !p.stopped {
        a_remove_exec(p, a_id, Ghost(a), Ghost(p0.doc));
    }
}

/// [`in_body_start_a`] in terms of [`a_remove`].
pub open spec fn start_a_shape(p: Parser, tt: TagTok) -> Parser {
    let f = p.formatting;
    let i = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| is_html(e, Tag::A));
    let q = if i >= 0 {
        let a = f[i]->Entry_elem;
        let q1 = in_body_adoption(p, tt);
        if q1.stopped {
            q1
        } else {
            a_remove(q1, a.id)
        }
    } else {
        p
    };
    let q0 = reconstruct_formatting(q);
    push_formatting(insert_html_element(q0, tt).0, insert_html_element(q0, tt).1, tt)
}

/// [`in_body_start_a`] is [`start_a_shape`].
pub proof fn lemma_start_a_shape(p: Parser, tt: TagTok)
    ensures
        in_body_start_a(p, tt) == start_a_shape(p, tt),
{
}

/// Case 29 ([`in_body_start_a`]).
pub fn in_body_start_a_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::A,
    ensures
        final(p)@ == in_body_start_a(old(p)@, tt@),
        parser_inv(final(p)@),
{
    hide(in_body_adoption);
    hide(reconstruct_formatting);
    hide(insert_html_element);
    hide(push_formatting);
    hide(a_remove);
    hide(fmt_last_where);
    hide(after_last_marker);
    hide(parser_inv);
    hide(stack_rooted);
    hide(in_body_start_a);
    proof {
        lemma_start_a_shape(p@, tt@);
    }
    if let Some(i) = last_a_after_marker_exec(p.formatting.as_slice()) {
        a_adopt_exec(env, p, &tt, i);
    }
    // "Reconstruct the active formatting elements, if any."
    reconstruct_formatting_exec(p);
    // "Insert an HTML element for the token. Push onto the list of active
    // formatting elements that element."
    insert_push_formatting_exec(p, tt);
}

/// Case 31 ([`in_body_start_nobr`]).
pub fn in_body_start_nobr_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, tt: ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Nobr,
    ensures
        final(p)@ == in_body_start_nobr(old(p)@, tt@),
        parser_inv(final(p)@),
{
    reconstruct_formatting_exec(p);
    if has_in_scope_exec(p, Tag::Nobr, &Scope::Default) {
        in_body_adoption_exec(env, p, &tt);
        reconstruct_formatting_exec(p);
    }
    insert_push_formatting_exec(p, tt);
}

} // verus!
