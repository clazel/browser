//! A parser the "in body" rules stop has an empty stack and satisfies
//! `termination::modes_ok` ([`super::stop_early::stop_ok`]): every case
//! keeps the modes ([`mk`]) or sets them as the case says.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::stop_body::*;
#[cfg(verus_only)]
use super::stop_early::*;
#[cfg(verus_only)]
use super::stop_frame::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use {
    lemma_pop,
    lemma_push,
    lemma_stop_parsing,
    lemma_dom_insert,
    lemma_dom_remove,
    lemma_create,
    lemma_create_element_for_token,
    lemma_insert_element_at,
    lemma_insert_foreign_element,
    lemma_insert_html_element,
    lemma_insert_characters,
    lemma_insert_char,
    lemma_insert_comment,
    lemma_insert_pi,
    lemma_generic_text_parsing,
    lemma_pop_while,
    lemma_generate_implied_end_tags,
    lemma_generate_all_implied_end_tags_thoroughly,
    lemma_pop_until_popped,
    lemma_pop_until_heading_popped,
    lemma_pop_until_node_popped,
    lemma_remove_open_at,
    lemma_push_formatting,
    lemma_push_marker,
    lemma_clear_to_last_marker,
    lemma_reconstruct_create,
    lemma_reconstruct_formatting,
    lemma_adoption_agency,
    lemma_add_missing_attributes,
    lemma_pop_until_named_popped,
    lemma_insert_and_pop,
    lemma_frameset_not_ok,
    lemma_close_p_element,
    lemma_close_p_if_in_button_scope,
    lemma_li_loop,
    lemma_dd_dt_loop,
    lemma_any_other_end_tag_loop,
    lemma_in_body_any_other_end_tag,
    lemma_in_body_adoption,
};

// ---------------------------------------------------------------------
// The cases

/// The character tokens.
pub broadcast proof fn lemma_in_body_char(p: Parser, c: u32)
    ensures
        mk(p, #[trigger] in_body_char(p, c)),
{
}

/// The `html` start tag.
pub broadcast proof fn lemma_in_body_start_html(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_html(p, tt)),
{
}

/// The `body` start tag.
pub broadcast proof fn lemma_in_body_start_body(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_body(p, tt)),
{
}

/// The heading start tags.
pub broadcast proof fn lemma_in_body_start_heading(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_heading(p, tt)),
{
}

/// The `pre` and `listing` start tags.
pub broadcast proof fn lemma_in_body_start_pre(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_pre(p, tt)),
{
}

/// The `form` start tag.
pub broadcast proof fn lemma_in_body_start_form(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_form(p, tt)),
{
}

/// The `li` start tag.
pub broadcast proof fn lemma_in_body_start_li(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_li(p, tt)),
{
}

/// The `dd` and `dt` start tags.
pub broadcast proof fn lemma_in_body_start_dd_dt(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_dd_dt(p, tt)),
{
}

/// The `button` start tag.
pub broadcast proof fn lemma_in_body_start_button(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_button(p, tt)),
{
}

/// The `a` start tag.
pub broadcast proof fn lemma_in_body_start_a(p: Parser, tt: TagTok)
    ensures
        tt.tag != Tag::Template ==> mk(p, #[trigger] in_body_start_a(p, tt)),
{
    hide(in_body_adoption);
    hide(reconstruct_formatting);
    hide(insert_html_element);
    hide(push_formatting);
    let f = p.formatting;
    let i = fmt_last_where(f, after_last_marker(f, f.len() as int), f.len() as int, |e: Elem| is_html(e, Tag::A));
    if i >= 0 {
        let a = f[i]->Entry_elem;
        let q1 = in_body_adoption(p, tt);
        lemma_in_body_adoption(p, tt);
        if !q1.stopped {
            let k = fmt_index_of(q1.formatting, q1.formatting.len() as int, a.id);
            crate::exec::modes::adoption::lemma_fmt_index_of(q1.formatting, q1.formatting.len() as int, a.id);
            if k >= 0 && formatting_ok(q1) {
                lemma_fok_remove(q1, Parser { formatting: q1.formatting.remove(k), ..q1 }, k);
            }
        }
    }
}

/// The `nobr` start tag.
pub broadcast proof fn lemma_in_body_start_nobr(p: Parser, tt: TagTok)
    ensures
        tt.tag != Tag::Template ==> mk(p, #[trigger] in_body_start_nobr(p, tt)),
{
}

/// The void start tags.
pub broadcast proof fn lemma_in_body_void_start_tag(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_void_start_tag(p, tt)),
{
}

/// The `input` start tag.
pub broadcast proof fn lemma_in_body_start_input(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_input(p, tt)),
{
}

/// The `hr` start tag.
pub broadcast proof fn lemma_in_body_start_hr(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_hr(p, tt)),
{
}

/// The `select` start tag.
pub broadcast proof fn lemma_in_body_start_select(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_select(p, tt)),
{
}

/// The `option` start tag.
pub broadcast proof fn lemma_in_body_start_option(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_option(p, tt)),
{
}

/// The `optgroup` start tag.
pub broadcast proof fn lemma_in_body_start_optgroup(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_optgroup(p, tt)),
{
}

/// The `math` start tag.
pub broadcast proof fn lemma_in_body_start_math(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_math(p, tt)),
{
}

/// The `svg` start tag.
pub broadcast proof fn lemma_in_body_start_svg(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_start_svg(p, tt)),
{
}

/// The block end tags.
pub broadcast proof fn lemma_in_body_end_same_name(p: Parser, tt: TagTok)
    ensures
        mk(p, #[trigger] in_body_end_same_name(p, tt)),
{
}

/// The `frameset` start tag keeps [`mk`] but the mode, "in frameset" or
/// unchanged.
pub broadcast proof fn lemma_in_body_start_frameset(p: Parser, tt: TagTok)
    ensures
        ({
            let q = #[trigger] in_body_start_frameset(p, tt);
            !p.stopped ==> mk(p, Parser { mode: p.mode, ..q }) && (q.mode == p.mode || q.mode == Mode::InFrameset)
        }),
{
    hide(insert_html_element);
    if !p.stopped && !(p.open.len() == 1 || !is_html(p.open[1], Tag::Body)) && p.frameset_ok {
        let q1 = dom_remove(p, p.open[1].id);
        let q2 = Parser { open: q1.open.take(1), ..q1 };
        assert(mk(p, q2));
        lemma_insert_html_element(q2, tt);
    }
}

/// The `textarea` start tag keeps [`mk`] but the modes: "text", returning
/// to the current one.
pub broadcast proof fn lemma_in_body_start_textarea(p: Parser, tt: TagTok)
    ensures
        ({
            let q = #[trigger] in_body_start_textarea(p, tt);
            mk(p, Parser { mode: p.mode, original_mode: p.original_mode, ..q }) && q.mode == Mode::Text && q.original_mode
                == p.mode
        }),
{
}

/// The `form` end tag.
pub broadcast proof fn lemma_in_body_end_form(p: Parser)
    ensures
        mk(p, #[trigger] in_body_end_form(p)),
{
}

// ---------------------------------------------------------------------
// The rules

/// The start tags of cases 7 to 21.
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_start_tag_stop_1(p: Parser, t: Tok, tt: TagTok)
    requires
        stop_pre(Mode::InBody, p),
        tt.tag == Tag::Html || is_in_head_start_tag(tt.tag) || tt.tag == Tag::Body || tt.tag == Tag::Frameset || is_block_start_tag(tt.tag) || is_heading_tag(tt.tag) || tt.tag == Tag::Pre || tt.tag == Tag::Listing || tt.tag == Tag::Form || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt || tt.tag == Tag::Plaintext || tt.tag == Tag::Button,
    ensures
        stop_ok(outcome_parser(in_body_start_tag(p, t, tt))),
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
    hide(frameset_not_ok);
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
    broadcast use {
        lemma_in_body_char,
        lemma_in_body_start_html,
        lemma_in_body_start_body,
        lemma_in_body_start_frameset,
        lemma_in_body_start_heading,
        lemma_in_body_start_pre,
        lemma_in_body_start_form,
        lemma_in_body_start_li,
        lemma_in_body_start_dd_dt,
        lemma_in_body_start_button,
        lemma_in_body_start_a,
        lemma_in_body_start_nobr,
        lemma_in_body_void_start_tag,
        lemma_in_body_start_input,
        lemma_in_body_start_hr,
        lemma_in_body_start_textarea,
        lemma_in_body_start_select,
        lemma_in_body_start_option,
        lemma_in_body_start_optgroup,
        lemma_in_body_start_math,
        lemma_in_body_start_svg,
        lemma_in_body_end_same_name,
        lemma_in_body_end_form,
    };

    lemma_stop_from(p, outcome_parser(in_body_start_tag(p, t, tt)));
}

/// The start tags of cases 29 to 41.
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_start_tag_stop_2(p: Parser, t: Tok, tt: TagTok)
    requires
        stop_pre(Mode::InBody, p),
        !(tt.tag == Tag::Html || is_in_head_start_tag(tt.tag) || tt.tag == Tag::Body || tt.tag == Tag::Frameset || is_block_start_tag(tt.tag) || is_heading_tag(tt.tag) || tt.tag == Tag::Pre || tt.tag == Tag::Listing || tt.tag == Tag::Form || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt || tt.tag == Tag::Plaintext || tt.tag == Tag::Button) && (tt.tag == Tag::A || is_formatting_start_tag(tt.tag) || tt.tag == Tag::Nobr || is_applet_like(tt.tag) || tt.tag == Tag::Table || is_void_start_tag(tt.tag) || tt.tag == Tag::Input || tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track || tt.tag == Tag::Hr || tt.tag == Tag::Image),
    ensures
        stop_ok(outcome_parser(in_body_start_tag(p, t, tt))),
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
    hide(frameset_not_ok);
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
    broadcast use {
        lemma_in_body_char,
        lemma_in_body_start_html,
        lemma_in_body_start_body,
        lemma_in_body_start_frameset,
        lemma_in_body_start_heading,
        lemma_in_body_start_pre,
        lemma_in_body_start_form,
        lemma_in_body_start_li,
        lemma_in_body_start_dd_dt,
        lemma_in_body_start_button,
        lemma_in_body_start_a,
        lemma_in_body_start_nobr,
        lemma_in_body_void_start_tag,
        lemma_in_body_start_input,
        lemma_in_body_start_hr,
        lemma_in_body_start_textarea,
        lemma_in_body_start_select,
        lemma_in_body_start_option,
        lemma_in_body_start_optgroup,
        lemma_in_body_start_math,
        lemma_in_body_start_svg,
        lemma_in_body_end_same_name,
        lemma_in_body_end_form,
    };

    lemma_stop_from(p, outcome_parser(in_body_start_tag(p, t, tt)));
}

/// The start tags of cases 42 to 54.
#[verifier::spinoff_prover]
pub proof fn lemma_in_body_start_tag_stop_3(p: Parser, t: Tok, tt: TagTok)
    requires
        stop_pre(Mode::InBody, p),
        !(tt.tag == Tag::Html || is_in_head_start_tag(tt.tag) || tt.tag == Tag::Body || tt.tag == Tag::Frameset || is_block_start_tag(tt.tag) || is_heading_tag(tt.tag) || tt.tag == Tag::Pre || tt.tag == Tag::Listing || tt.tag == Tag::Form || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt || tt.tag == Tag::Plaintext || tt.tag == Tag::Button) && !(tt.tag == Tag::A || is_formatting_start_tag(tt.tag) || tt.tag == Tag::Nobr || is_applet_like(tt.tag) || tt.tag == Tag::Table || is_void_start_tag(tt.tag) || tt.tag == Tag::Input || tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track || tt.tag == Tag::Hr || tt.tag == Tag::Image),
    ensures
        stop_ok(outcome_parser(in_body_start_tag(p, t, tt))),
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
    hide(frameset_not_ok);
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
    broadcast use {
        lemma_in_body_char,
        lemma_in_body_start_html,
        lemma_in_body_start_body,
        lemma_in_body_start_frameset,
        lemma_in_body_start_heading,
        lemma_in_body_start_pre,
        lemma_in_body_start_form,
        lemma_in_body_start_li,
        lemma_in_body_start_dd_dt,
        lemma_in_body_start_button,
        lemma_in_body_start_a,
        lemma_in_body_start_nobr,
        lemma_in_body_void_start_tag,
        lemma_in_body_start_input,
        lemma_in_body_start_hr,
        lemma_in_body_start_textarea,
        lemma_in_body_start_select,
        lemma_in_body_start_option,
        lemma_in_body_start_optgroup,
        lemma_in_body_start_math,
        lemma_in_body_start_svg,
        lemma_in_body_end_same_name,
        lemma_in_body_end_form,
    };

    lemma_stop_from(p, outcome_parser(in_body_start_tag(p, t, tt)));
}

/// The start tags.
pub proof fn lemma_in_body_start_tag_stop(p: Parser, t: Tok, tt: TagTok)
    requires
        stop_pre(Mode::InBody, p),
    ensures
        stop_ok(outcome_parser(in_body_start_tag(p, t, tt))),
{
    if tt.tag == Tag::Html || is_in_head_start_tag(tt.tag) || tt.tag == Tag::Body || tt.tag == Tag::Frameset || is_block_start_tag(tt.tag) || is_heading_tag(tt.tag) || tt.tag == Tag::Pre || tt.tag == Tag::Listing || tt.tag == Tag::Form || tt.tag == Tag::Li || tt.tag == Tag::Dd || tt.tag == Tag::Dt || tt.tag == Tag::Plaintext || tt.tag == Tag::Button {
        lemma_in_body_start_tag_stop_1(p, t, tt);
    } else if tt.tag == Tag::A || is_formatting_start_tag(tt.tag) || tt.tag == Tag::Nobr || is_applet_like(tt.tag) || tt.tag == Tag::Table || is_void_start_tag(tt.tag) || tt.tag == Tag::Input || tt.tag == Tag::Param || tt.tag == Tag::Source || tt.tag == Tag::Track || tt.tag == Tag::Hr || tt.tag == Tag::Image {
        lemma_in_body_start_tag_stop_2(p, t, tt);
    } else {
        lemma_in_body_start_tag_stop_3(p, t, tt);
    }
}

/// The end tags.
pub proof fn lemma_in_body_end_tag_stop(p: Parser, t: Tok, tt: TagTok)
    requires
        stop_pre(Mode::InBody, p),
    ensures
        stop_ok(outcome_parser(in_body_end_tag(p, t, tt))),
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
    hide(has_in_scope);
    broadcast use {
        lemma_in_body_char,
        lemma_in_body_start_html,
        lemma_in_body_start_body,
        lemma_in_body_start_frameset,
        lemma_in_body_start_heading,
        lemma_in_body_start_pre,
        lemma_in_body_start_form,
        lemma_in_body_start_li,
        lemma_in_body_start_dd_dt,
        lemma_in_body_start_button,
        lemma_in_body_start_a,
        lemma_in_body_start_nobr,
        lemma_in_body_void_start_tag,
        lemma_in_body_start_input,
        lemma_in_body_start_hr,
        lemma_in_body_start_textarea,
        lemma_in_body_start_select,
        lemma_in_body_start_option,
        lemma_in_body_start_optgroup,
        lemma_in_body_start_math,
        lemma_in_body_start_svg,
        lemma_in_body_end_same_name,
        lemma_in_body_end_form,
    };

    lemma_stop_from(p, outcome_parser(in_body_end_tag(p, t, tt)));
}

/// §13.2.6.4.7 "in body".
pub proof fn lemma_in_body_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InBody, p),
    ensures
        stop_ok(outcome_parser(mode_in_body(env, p, t))),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
    broadcast use lemma_in_body_char;

    match t {
        Tok::Start(tt) => lemma_in_body_start_tag_stop(p, t, tt),
        Tok::End(tt) => lemma_in_body_end_tag_stop(p, t, tt),
        _ => lemma_stop_from(p, outcome_parser(mode_in_body(env, p, t))),
    }
}

} // verus!
