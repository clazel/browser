//! The "in body" rules by token kind keep the reachable-state facts
//! ([`next_core`], see [`super`]).

#[cfg(verus_only)]
use super::adoption::*;
#[cfg(verus_only)]
use super::body::*;
#[cfg(verus_only)]
use super::helpers::*;
#[cfg(verus_only)]
use super::lists::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Cases 14, 16 and 20: block elements, `pre`, `listing`, `plaintext`.
pub proof fn lemma_ib_start_block(p: Parser, t: Tok, tt: TagTok)
    requires
        ib_pre(p, tt),
        t == Tok::Start(tt),
        !is_in_head_start_tag(tt.tag),
        (is_block_start_tag(tt.tag) || tt.tag == Tag::Pre || tt.tag == Tag::Listing || tt.tag == Tag::Plaintext) && tt.tag != Tag::Html && tt.tag != Tag::Body && tt.tag != Tag::Frameset,
    ensures
        next_core(in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(in_body_start_heading);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(in_body_start_nobr);
    hide(doc_is_quirks);
    hide(has_in_scope);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(in_body_start_hr);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(insert_and_pop);
    hide(close_p_element);
    lemma_keeps_refl(p);
    let g = tt.tag;
    lemma_then_close_p_if(p, p);
    lemma_then_insert(p, close_p_if_in_button_scope(p), tt);
    let q = insert_html_element(close_p_if_in_button_scope(p), tt).0;
    lemma_ib_done(p, q);
    if g == Tag::Pre || g == Tag::Listing {
        lemma_flags_keeps(q, Parser { skip_lf: true, frameset_ok: false, ..q });
        lemma_keeps_trans(p, q, Parser { skip_lf: true, frameset_ok: false, ..q });
        lemma_ib_done(p, Parser { skip_lf: true, frameset_ok: false, ..q });
    } else if g == Tag::Plaintext {
        lemma_flags_keeps(q, Parser { tokenizer: Some(TokenizerState::Plaintext), ..q });
        lemma_keeps_trans(p, q, Parser { tokenizer: Some(TokenizerState::Plaintext), ..q });
        lemma_ib_done(p, Parser { tokenizer: Some(TokenizerState::Plaintext), ..q });
    }
}

/// Cases 30 and 33: formatting elements, `applet`, `marquee`, `object`.
pub proof fn lemma_ib_start_fmt(p: Parser, t: Tok, tt: TagTok)
    requires
        ib_pre(p, tt),
        t == Tok::Start(tt),
        !is_in_head_start_tag(tt.tag),
        is_formatting_start_tag(tt.tag) || is_applet_like(tt.tag),
    ensures
        next_core(in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(in_body_start_nobr);
    hide(doc_is_quirks);
    hide(has_in_scope);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(in_body_start_hr);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(insert_and_pop);
    hide(close_p_element);
    lemma_keeps_refl(p);
    let g = tt.tag;
    if is_formatting_start_tag(g) {
        lemma_then_reconstruct(p, p);
        lemma_then_push_formatting(p, reconstruct_formatting(p), tt);
        let (q, e) = insert_html_element(reconstruct_formatting(p), tt);
        lemma_ib_done(p, push_formatting(q, e, tt));
    } else {
        lemma_then_reconstruct(p, p);
        lemma_then_insert(p, reconstruct_formatting(p), tt);
        let q = insert_html_element(reconstruct_formatting(p), tt).0;
        lemma_keeps_live(p, q);
        lemma_push_marker_keeps(q);
        lemma_keeps_trans(p, q, push_marker(q));
        lemma_then_fno(p, push_marker(q));
        lemma_ib_done(p, frameset_not_ok(push_marker(q)));
    }
}

/// Case 35: `table`.
pub proof fn lemma_ib_start_table(p: Parser, t: Tok, tt: TagTok)
    requires
        ib_pre(p, tt),
        t == Tok::Start(tt),
        !is_in_head_start_tag(tt.tag),
        tt.tag == Tag::Table,
    ensures
        next_core(in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(in_body_start_nobr);
    hide(doc_is_quirks);
    hide(has_in_scope);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(in_body_start_hr);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(insert_and_pop);
    hide(close_p_element);
    lemma_keeps_refl(p);
    let g = tt.tag;
    let q = if !doc_is_quirks(p) && has_in_scope(p, Tag::P, Scope::Button) {
        close_p_element(p)
    } else {
        p
    };
    if !doc_is_quirks(p) && has_in_scope(p, Tag::P, Scope::Button) {
        lemma_close_p_keeps(p);
    }
    lemma_then_insert(p, q, tt);
    let q1 = insert_html_element(q, tt).0;
    lemma_finish(p, q1, Parser { frameset_ok: false, mode: Mode::InTable, ..q1 });
}

/// Case 37: void elements.
pub proof fn lemma_ib_start_void(p: Parser, t: Tok, tt: TagTok)
    requires
        ib_pre(p, tt),
        t == Tok::Start(tt),
        is_void_start_tag(tt.tag),
    ensures
        next_core(in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(in_body_start_nobr);
    hide(push_marker);
    hide(doc_is_quirks);
    hide(has_in_scope);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(insert_and_pop);
    hide(close_p_element);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(in_body_start_hr);
    hide(frameset_not_ok);
    lemma_keeps_refl(p);
    lemma_then_reconstruct(p, p);
    lemma_then_insert_pop(p, reconstruct_formatting(p), tt);
    lemma_then_fno(p, insert_and_pop(reconstruct_formatting(p), tt));
    assert(in_body_void_start_tag(p, tt) == frameset_not_ok(insert_and_pop(reconstruct_formatting(p), tt))) by {
        reveal(in_body_void_start_tag);
    }
    lemma_ib_done(p, in_body_void_start_tag(p, tt));
}

/// Case 39: `param`, `source`, `track`.
pub proof fn lemma_ib_start_param(p: Parser, t: Tok, tt: TagTok)
    requires
        ib_pre(p, tt),
        t == Tok::Start(tt),
        tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track,
    ensures
        next_core(in_body_start_tag(p, t, tt)),
{
    hide(in_body_start_html);
    hide(in_body_start_body);
    hide(in_body_start_frameset);
    hide(in_body_start_heading);
    hide(in_body_start_pre);
    hide(in_body_start_form);
    hide(in_body_start_li);
    hide(in_body_start_dd_dt);
    hide(in_body_start_button);
    hide(in_body_start_a);
    hide(in_body_start_nobr);
    hide(push_marker);
    hide(doc_is_quirks);
    hide(has_in_scope);
    hide(in_body_start_textarea);
    hide(generic_text_parsing);
    hide(in_body_start_select);
    hide(in_body_start_option);
    hide(in_body_start_optgroup);
    hide(generate_implied_end_tags);
    hide(in_body_start_math);
    hide(in_body_start_svg);
    hide(insert_html_element);
    hide(close_p_if_in_button_scope);
    hide(reconstruct_formatting);
    hide(push_formatting);
    hide(insert_and_pop);
    hide(close_p_element);
    hide(in_body_void_start_tag);
    hide(in_body_start_input);
    hide(in_body_start_hr);
    hide(frameset_not_ok);
    lemma_keeps_refl(p);
    lemma_then_insert_pop(p, p, tt);
    lemma_ib_done(p, insert_and_pop(p, tt));
}

/// The "in body" start tags.
pub proof fn lemma_ib_start_reach(p: Parser, t: Tok, tt: TagTok)
    requires
        rules_inv(Rules::Html(Mode::InBody), p, t),
        t == Tok::Start(tt),
    ensures
        next_core(in_body_start_tag(p, t, tt)),
{
    hide(super::doc::dinv);
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
    hide(frameset_not_ok);
    hide(doc_is_quirks);
    hide(has_in_scope);
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
    let g = tt.tag;
    if g == Tag::Html {
        lemma_ib_html(p, t, tt);
        return;
    }
    assert(rooted_mode(p.mode));
    assert(good(p));
    assert(ib_pre(p, tt));
    lemma_keeps_refl(p);
    if is_in_head_start_tag(g) {
    } else if g == Tag::Body {
        lemma_ib_body(p, tt);
    } else if g == Tag::Frameset {
        lemma_ib_frameset(p, tt);
    } else if is_heading_tag(g) {
        lemma_ib_heading(p, tt);
    } else if g == Tag::Form {
        lemma_ib_form(p, tt);
    } else if g == Tag::Li || g == Tag::Dd || g == Tag::Dt {
        lemma_ib_li_dd(p, tt);
    } else if g == Tag::Button {
        lemma_ib_button(p, tt);
    } else if g == Tag::A {
        lemma_ib_a(p, tt);
    } else if g == Tag::Nobr {
        lemma_ib_nobr(p, tt);
    } else if g == Tag::Input {
        lemma_ib_input(p, tt);
    } else if g == Tag::Hr {
        lemma_ib_hr(p, tt);
    } else if g == Tag::Image {
    } else if g == Tag::Textarea {
        lemma_ib_textarea(p, tt);
    } else if g == Tag::Xmp {
        lemma_then_close_p_if(p, p);
        lemma_then_reconstruct(p, close_p_if_in_button_scope(p));
        lemma_then_fno(p, reconstruct_formatting(close_p_if_in_button_scope(p)));
        lemma_ib_text(p, frameset_not_ok(reconstruct_formatting(close_p_if_in_button_scope(p))), tt, true);
    } else if g == Tag::Iframe {
        lemma_then_fno(p, p);
        lemma_ib_text(p, frameset_not_ok(p), tt, true);
    } else if g == Tag::Noembed || (g == Tag::Noscript && p.scripting) {
        lemma_ib_text(p, p, tt, true);
    } else if g == Tag::Select || g == Tag::Option || g == Tag::Optgroup {
        lemma_ib_select(p, tt);
    } else if g == Tag::Rb || g == Tag::Rtc {
        lemma_ib_ruby(p, tt, None);
    } else if g == Tag::Rp || g == Tag::Rt {
        lemma_ib_ruby(p, tt, Some(Tag::Rtc));
    } else if g == Tag::Math || g == Tag::Svg {
        lemma_ib_foreign(p, tt);
    } else if is_ignored_start_tag(g) {
    } else if is_block_start_tag(g) || g == Tag::Pre || g == Tag::Listing || g == Tag::Plaintext || is_formatting_start_tag(g)
        || is_applet_like(g) || g == Tag::Table || is_void_start_tag(g) || g == Tag::Param || g == Tag::Source || g
        == Tag::Track {
        if is_block_start_tag(g) || g == Tag::Pre || g == Tag::Listing || g == Tag::Plaintext {
            lemma_ib_start_block(p, t, tt);
        } else if is_formatting_start_tag(g) || is_applet_like(g) {
            lemma_ib_start_fmt(p, t, tt);
        } else if g == Tag::Table {
            lemma_ib_start_table(p, t, tt);
        } else if is_void_start_tag(g) {
            lemma_ib_start_void(p, t, tt);
        } else {
            lemma_ib_start_param(p, t, tt);
        }
    } else {
        lemma_then_reconstruct(p, p);
        lemma_then_insert(p, reconstruct_formatting(p), tt);
        lemma_ib_done(p, insert_html_element(reconstruct_formatting(p), tt).0);
    }
}

/// "Generate implied end tags", then pop until an entry named as the
/// tagged token, not an implied end tag (other than `except`), has been
/// popped, when one is in scope.
pub proof fn lemma_ib_close_named(p: Parser, tt: TagTok, except: Option<Tag>, s: Scope)
    requires
        good(p),
        !p.stopped,
        tok_tagged(tt),
        tt.tag != Tag::Html,
        tt.tag != Tag::Td && tt.tag != Tag::Th,
        s != Scope::Table,
        in_scope_from(p.open, p.open.len() as int, |e: Elem| is_html_named(e, tt.name), s),
        !crate::exec::modes::in_body_start_lemmas::implied_pred(except)(Elem { tag: tt.tag, ns: Namespace::Html, ..p.open[0] }),
    ensures
        keeps(p, pop_until_named_popped(generate_implied_end_tags(p, except), tt.name)),
{
    let f = |e: Elem| is_html_named(e, tt.name);
    assert(!f(p.open[0])) by {
        if f(p.open[0]) {
            assert(elem_tagged(p.open[0]));
        }
    }
    let k = lemma_scope_k(p.open, f, s);
    assert(p.open[k].tag == tt.tag) by {
        assert(elem_tagged(p.open[k]));
    }
    let q = generate_implied_end_tags(p, except);
    lemma_pop_until_named_is(q, tt.name);
    lemma_close_keeps(p, except, f, k);
}

/// The "in body" end tags.
pub proof fn lemma_ib_end_reach(p: Parser, t: Tok, tt: TagTok)
    requires
        rules_inv(Rules::Html(Mode::InBody), p, t),
        t == Tok::End(tt),
    ensures
        next_core(in_body_end_tag(p, t, tt)),
{
    hide(in_body_end_same_name);
    hide(in_body_end_form);
    hide(insert_html_element);
    hide(close_p_element);
    hide(generate_implied_end_tags);
    hide(pop_until_named_popped);
    hide(pop_until_heading_popped);
    hide(in_body_any_other_end_tag);
    hide(in_body_adoption);
    hide(clear_to_last_marker);
    hide(in_body_void_start_tag);
    hide(pop_until_popped);
    let g = tt.tag;
    assert(rooted_mode(p.mode));
    assert(good(p));
    lemma_keeps_refl(p);
    if g == Tag::Template {
    } else if g == Tag::Body || g == Tag::Html {
        lemma_finish(p, p, Parser { mode: Mode::AfterBody, ..p });
    } else if is_block_end_tag(g) {
        if has_same_name_in_scope(p, tt) {
            lemma_ib_close_named(p, tt, None, Scope::Default);
        }
        reveal(in_body_end_same_name);
        lemma_ib_done(p, in_body_end_same_name(p, tt));
    } else if g == Tag::Form {
        lemma_ib_end_form(p);
    } else if g == Tag::P {
        let q = if !has_in_scope(p, Tag::P, Scope::Button) {
            insert_html_element(p, start_tag_named(name_p())).0
        } else {
            p
        };
        if !has_in_scope(p, Tag::P, Scope::Button) {
            assert(tag_of(name_p()) == Tag::P) by (compute);
            lemma_insert_html_keeps(p, start_tag_named(name_p()));
            reveal(insert_html_element);
            let (q1, e) = insert_html_element(p, start_tag_named(name_p()));
            if !q.stopped {
                assert(q.open.last() == e);
                assert(has_in_scope(q, Tag::P, Scope::Button));
            }
        }
        lemma_keeps_live(p, q);
        lemma_close_p_keeps(q);
        lemma_keeps_trans(p, q, close_p_element(q));
        lemma_ib_done(p, close_p_element(q));
    } else if g == Tag::Li {
        if has_in_scope(p, Tag::Li, Scope::ListItem) {
            let f = |e: Elem| is_html(e, Tag::Li);
            let k = lemma_scope_k(p.open, f, Scope::ListItem);
            crate::exec::stack::lemma_pop_until_popped(generate_implied_end_tags(p, Some(Tag::Li)), Tag::Li);
            reveal(generate_implied_end_tags);
            lemma_close_keeps(p, Some(Tag::Li), f, k);
            lemma_ib_done(p, pop_until_popped(generate_implied_end_tags(p, Some(Tag::Li)), Tag::Li));
        }
    } else if g == Tag::Dd || g == Tag::Dt {
        if has_same_name_in_scope(p, tt) {
            lemma_ib_close_named(p, tt, Some(g), Scope::Default);
            lemma_ib_done(p, pop_until_named_popped(generate_implied_end_tags(p, Some(g)), tt.name));
        }
    } else {
        lemma_ib_end_reach2(p, t, tt);
    }
}

/// The "in body" end tags from case 24 on (headings).
pub proof fn lemma_ib_end_reach2(p: Parser, t: Tok, tt: TagTok)
    requires
        rules_inv(Rules::Html(Mode::InBody), p, t),
        t == Tok::End(tt),
        !(tt.tag == Tag::Template || tt.tag == Tag::Body || tt.tag == Tag::Html || is_block_end_tag(tt.tag) || tt.tag
            == Tag::Form || tt.tag == Tag::P || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt),
    ensures
        next_core(in_body_end_tag(p, t, tt)),
{
    hide(in_body_end_same_name);
    hide(in_body_end_form);
    hide(insert_html_element);
    hide(close_p_element);
    hide(generate_implied_end_tags);
    hide(pop_until_named_popped);
    hide(pop_until_heading_popped);
    hide(in_body_any_other_end_tag);
    hide(in_body_adoption);
    hide(clear_to_last_marker);
    hide(in_body_void_start_tag);
    hide(pop_until_popped);
    let g = tt.tag;
    assert(rooted_mode(p.mode));
    assert(good(p));
    assert(in_cell(p) ==> g != Tag::Td && g != Tag::Th);
    lemma_keeps_refl(p);
    if is_heading_tag(g) {
        if has_heading_in_scope(p) {
            let f = |e: Elem| e.ns == Namespace::Html && (e.tag == Tag::H1 || e.tag == Tag::H2 || e.tag == Tag::H3 || e.tag
                == Tag::H4 || e.tag == Tag::H5 || e.tag == Tag::H6);
            let k = lemma_scope_k(p.open, f, Scope::Default);
            let q = generate_implied_end_tags(p, None);
            crate::exec::stack::lemma_pop_until_heading_popped(q);
            let g2 = |e: Elem| is_heading(e);
            assert(g2(p.open[k]));
            lemma_close_keeps(p, None, g2, k);
            lemma_ib_done(p, pop_until_heading_popped(q));
        }
    } else if tt.name == name_sarcasm() {
        lemma_any_other_keeps(p, tt);
        lemma_ib_done(p, in_body_any_other_end_tag(p, tt));
    } else if is_formatting_end_tag(g) {
        lemma_in_body_adoption_keeps(p, tt);
        lemma_ib_done(p, in_body_adoption(p, tt));
    } else if is_applet_like(g) {
        if has_same_name_in_scope(p, tt) {
            lemma_ib_close_named(p, tt, None, Scope::Default);
            let q = pop_until_named_popped(generate_implied_end_tags(p, None), tt.name);
            lemma_keeps_live(p, q);
            lemma_clear_keeps(q);
            lemma_keeps_trans(p, q, clear_to_last_marker(q));
            lemma_ib_done(p, clear_to_last_marker(q));
        }
    } else if g == Tag::Br {
        let t2 = TagTok { attrs: seq![], ..tt };
        lemma_then_reconstruct(p, p);
        lemma_then_insert_pop(p, reconstruct_formatting(p), t2);
        lemma_then_fno(p, insert_and_pop(reconstruct_formatting(p), t2));
        reveal(in_body_void_start_tag);
        lemma_ib_done(p, in_body_void_start_tag(p, t2));
    } else {
        lemma_any_other_keeps(p, tt);
        lemma_ib_done(p, in_body_any_other_end_tag(p, tt));
    }
}

/// The `form` end tag.
pub proof fn lemma_ib_end_form(p: Parser)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        rooted_mode(p.mode),
    ensures
        next_core(Outcome::Done(in_body_end_form(p))),
{
    if !parsing_template_contents(p) {
        let q = Parser { form: None, ..p };
        assert(good(q));
        assert(keeps(p, q));
        match p.form {
            Some(n) if has_node_in_scope(q, n, Scope::Default) => {
                let q1 = generate_implied_end_tags(q, None);
                lemma_implied_keeps(q, None);
                lemma_keeps_trans(p, q, q1);
                let ff = super::adoption::id_is(n);
                let j = open_index_of(q1, n);
                assert(j == last_index_where(q1.open, q1.open.len() as int, ff));
                if j >= 0 {
                    crate::termination::helpers_ranking::lemma_last_index_where(q1.open, q1.open.len() as int, ff);
                    assert(j != 0);
                    super::cells::lemma_cell_top(p.open);
                    if in_cell(p) {
                        assert(cell_fresh(p, p.open[last_cell(p.open)].id));
                        assert(q1.open[j].id == n);
                    }
                    lemma_remove_open_keeps(q1, j);
                    lemma_keeps_trans(p, q1, remove_open_at(q1, j));
                    lemma_ib_done(p, remove_open_at(q1, j));
                } else {
                    lemma_ib_done(p, q1);
                }
            },
            _ => {
                lemma_ib_done(p, q);
            },
        }
    } else if !has_in_scope(p, Tag::Form, Scope::Default) {
        lemma_keeps_refl(p);
        lemma_ib_done(p, p);
    } else {
        let f = |e: Elem| is_html(e, Tag::Form);
        let k = lemma_scope_k(p.open, f, Scope::Default);
        crate::exec::stack::lemma_pop_until_popped(generate_implied_end_tags(p, None), Tag::Form);
        lemma_close_keeps(p, None, f, k);
        lemma_ib_done(p, pop_until_popped(generate_implied_end_tags(p, None), Tag::Form));
    }
}

/// The "in body" rules.
pub proof fn lemma_in_body_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InBody), p, t),
    ensures
        next_core(mode_in_body(env, p, t)),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
    match t {
        Tok::Start(tt) => lemma_ib_start_reach(p, t, tt),
        Tok::End(tt) => lemma_ib_end_reach(p, t, tt),
        Tok::Char(c) => {
            assert(rooted_mode(p.mode));
            assert(good(p));
            reveal(in_body_char);
            if c != 0 {
                lemma_keeps_refl(p);
                lemma_then_reconstruct(p, p);
                let q = reconstruct_formatting(p);
                lemma_keeps_live(p, q);
                lemma_insert_char_keeps(q, c);
                lemma_keeps_trans(p, q, insert_char(q, c));
                lemma_then_fno(p, insert_char(q, c));
                lemma_ib_done(p, in_body_char(p, c));
            }
        },
        Tok::Comment(d) => {
            assert(rooted_mode(p.mode));
            assert(good(p));
            lemma_insert_comment_keeps(p, d, None);
            let q = insert_comment(p, d, None);
            if !q.stopped {
                lemma_core_frame(p, q);
            }
        },
        Tok::Pi(a, d) => {
            assert(rooted_mode(p.mode));
            assert(good(p));
            lemma_insert_pi_keeps(p, a, d, None);
            let q = insert_pi(p, a, d, None);
            if !q.stopped {
                lemma_core_frame(p, q);
            }
        },
        _ => {},
    }
}

} // verus!
