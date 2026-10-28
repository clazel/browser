//! The "in body" insertion mode keeps the actions, the confidence and the
//! stopped flag, or stops parsing ([`grows`]), case by case.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use super::frame_base::lemma_pop, super::frame_base::lemma_push, super::frame_base::lemma_stop_parsing, super::frame_base::lemma_dom_insert, super::frame_base::lemma_dom_remove, super::frame_base::lemma_create, super::frame_base::lemma_create_element_for_token, super::frame_base::lemma_insert_element_at, super::frame_base::lemma_insert_foreign_element, super::frame_base::lemma_insert_html_element, super::frame_base::lemma_insert_characters, super::frame_base::lemma_insert_char, super::frame_base::lemma_insert_comment, super::frame_base::lemma_insert_pi, super::frame_base::lemma_generic_text_parsing, super::frame_base::lemma_pop_while, super::frame_base::lemma_generate_implied_end_tags, super::frame_base::lemma_generate_all_implied_end_tags_thoroughly, super::frame_base::lemma_pop_until_popped, super::frame_base::lemma_pop_until_heading_popped, super::frame_base::lemma_pop_until_node_popped, super::frame_base::lemma_remove_open_at, super::frame_base::lemma_reset_insertion_mode, super::frame_base::lemma_push_formatting, super::frame_base::lemma_push_marker, super::frame_base::lemma_clear_to_last_marker, super::frame_base::lemma_reconstruct_create, super::frame_base::lemma_reconstruct_formatting, super::frame_body::lemma_dom_reparent_children, super::frame_body::lemma_aa_inner, super::frame_body::lemma_aa_finish, super::frame_body::lemma_aa_outer, super::frame_body::lemma_adoption_agency, super::frame_body::lemma_add_missing_attributes, super::frame_body::lemma_pop_until_named_popped, super::frame_body::lemma_insert_and_pop, super::frame_body::lemma_frameset_not_ok, super::frame_body::lemma_close_p_element, super::frame_body::lemma_close_p_if_in_button_scope, super::frame_body::lemma_li_loop, super::frame_body::lemma_dd_dt_loop, super::frame_body::lemma_any_other_end_tag_loop, super::frame_body::lemma_in_body_any_other_end_tag, super::frame_body::lemma_in_body_adoption;

/// The character tokens.
pub broadcast proof fn lemma_in_body_char(p: Parser, c: u32)
    ensures
        grows(p, #[trigger] in_body_char(p, c)),
{
}

/// The `html` start tag.
pub broadcast proof fn lemma_in_body_start_html(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_html(p, tt)),
{
}

/// The `body` start tag.
pub broadcast proof fn lemma_in_body_start_body(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_body(p, tt)),
{
}

/// The `frameset` start tag.
pub broadcast proof fn lemma_in_body_start_frameset(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_frameset(p, tt)),
{
}

/// The heading start tags.
pub broadcast proof fn lemma_in_body_start_heading(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_heading(p, tt)),
{
}

/// The `pre` and `listing` start tags.
pub broadcast proof fn lemma_in_body_start_pre(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_pre(p, tt)),
{
}

/// The `form` start tag.
pub broadcast proof fn lemma_in_body_start_form(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_form(p, tt)),
{
}

/// The `li` start tag.
pub broadcast proof fn lemma_in_body_start_li(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_li(p, tt)),
{
}

/// The `dd` and `dt` start tags.
pub broadcast proof fn lemma_in_body_start_dd_dt(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_dd_dt(p, tt)),
{
}

/// The `button` start tag.
pub broadcast proof fn lemma_in_body_start_button(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_button(p, tt)),
{
}

/// The `a` start tag.
pub broadcast proof fn lemma_in_body_start_a(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_a(p, tt)),
{
}

/// The `nobr` start tag.
pub broadcast proof fn lemma_in_body_start_nobr(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_nobr(p, tt)),
{
}

/// The void start tags.
pub broadcast proof fn lemma_in_body_void_start_tag(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_void_start_tag(p, tt)),
{
}

/// The `input` start tag.
pub broadcast proof fn lemma_in_body_start_input(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_input(p, tt)),
{
}

/// The `hr` start tag.
pub broadcast proof fn lemma_in_body_start_hr(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_hr(p, tt)),
{
}

/// The `textarea` start tag.
pub broadcast proof fn lemma_in_body_start_textarea(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_textarea(p, tt)),
{
}

/// The `select` start tag.
pub broadcast proof fn lemma_in_body_start_select(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_select(p, tt)),
{
}

/// The `option` start tag.
pub broadcast proof fn lemma_in_body_start_option(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_option(p, tt)),
{
}

/// The `optgroup` start tag.
pub broadcast proof fn lemma_in_body_start_optgroup(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_optgroup(p, tt)),
{
}

/// The `math` start tag.
pub broadcast proof fn lemma_in_body_start_math(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_math(p, tt)),
{
}

/// The `svg` start tag.
pub broadcast proof fn lemma_in_body_start_svg(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_start_svg(p, tt)),
{
}

/// The block end tags.
pub broadcast proof fn lemma_in_body_end_same_name(p: Parser, tt: TagTok)
    ensures
        grows(p, #[trigger] in_body_end_same_name(p, tt)),
{
}

/// The `form` end tag.
pub broadcast proof fn lemma_in_body_end_form(p: Parser)
    ensures
        grows(p, #[trigger] in_body_end_form(p)),
{
}

/// The start tags.
pub proof fn lemma_in_body_start_tag(p: Parser, t: Tok, tt: TagTok)
    ensures
        grows(p, outcome_parser(in_body_start_tag(p, t, tt))),
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
    broadcast use lemma_in_body_char, lemma_in_body_start_html, lemma_in_body_start_body, lemma_in_body_start_frameset, lemma_in_body_start_heading, lemma_in_body_start_pre, lemma_in_body_start_form, lemma_in_body_start_li, lemma_in_body_start_dd_dt, lemma_in_body_start_button, lemma_in_body_start_a, lemma_in_body_start_nobr, lemma_in_body_void_start_tag, lemma_in_body_start_input, lemma_in_body_start_hr, lemma_in_body_start_textarea, lemma_in_body_start_select, lemma_in_body_start_option, lemma_in_body_start_optgroup, lemma_in_body_start_math, lemma_in_body_start_svg, lemma_in_body_end_same_name, lemma_in_body_end_form;

}

/// The end tags.
pub proof fn lemma_in_body_end_tag(p: Parser, t: Tok, tt: TagTok)
    ensures
        grows(p, outcome_parser(in_body_end_tag(p, t, tt))),
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
    broadcast use lemma_in_body_char, lemma_in_body_start_html, lemma_in_body_start_body, lemma_in_body_start_frameset, lemma_in_body_start_heading, lemma_in_body_start_pre, lemma_in_body_start_form, lemma_in_body_start_li, lemma_in_body_start_dd_dt, lemma_in_body_start_button, lemma_in_body_start_a, lemma_in_body_start_nobr, lemma_in_body_void_start_tag, lemma_in_body_start_input, lemma_in_body_start_hr, lemma_in_body_start_textarea, lemma_in_body_start_select, lemma_in_body_start_option, lemma_in_body_start_optgroup, lemma_in_body_start_math, lemma_in_body_start_svg, lemma_in_body_end_same_name, lemma_in_body_end_form;

}

/// §13.2.6.4.7 the "in body" insertion mode.
pub proof fn lemma_mode_in_body(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_body(env, p, t))),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
    broadcast use lemma_in_body_char, lemma_in_body_start_html, lemma_in_body_start_body, lemma_in_body_start_frameset, lemma_in_body_start_heading, lemma_in_body_start_pre, lemma_in_body_start_form, lemma_in_body_start_li, lemma_in_body_start_dd_dt, lemma_in_body_start_button, lemma_in_body_start_a, lemma_in_body_start_nobr, lemma_in_body_void_start_tag, lemma_in_body_start_input, lemma_in_body_start_hr, lemma_in_body_start_textarea, lemma_in_body_start_select, lemma_in_body_start_option, lemma_in_body_start_optgroup, lemma_in_body_start_math, lemma_in_body_start_svg, lemma_in_body_end_same_name, lemma_in_body_end_form;

    match t {
        Tok::Start(tt) => lemma_in_body_start_tag(p, t, tt),
        Tok::End(tt) => lemma_in_body_end_tag(p, t, tt),
        _ => {},
    }
}


} // verus!
