//! A parser the rules of the table modes, "in template", the modes after
//! the body and foreign content stop has an empty stack and satisfies
//! `termination::modes_ok` ([`super::stop_early::stop_ok`]).

#[allow(unused_imports)]
use super::spec::*;
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
    lemma_pop_while,
    lemma_generate_implied_end_tags,
    lemma_generate_all_implied_end_tags_thoroughly,
    lemma_pop_until_popped,
    lemma_pop_until_cell_popped,
    lemma_pop_until_node_popped,
    lemma_reset_insertion_mode,
    lemma_push_marker,
    lemma_clear_to_last_marker,
};

// ---------------------------------------------------------------------
// "in table" and "in table text"

/// A [`mk`]-kept parser with foster parenting enabled or disabled.
pub proof fn lemma_foster(p: Parser, q: Parser, b: bool)
    requires
        mk(p, q),
    ensures
        mk(p, Parser { foster: b, ..q }),
{
}

/// The parser of an "in body" outcome that uses other rules is the one the
/// rules were applied to.
pub proof fn lemma_in_body_using(env: EncFns, p: Parser, t: Tok)
    ensures
        mode_in_body(env, p, t) is Using ==> outcome_parser(mode_in_body(env, p, t)) == p,
{
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
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
    hide(in_body_end_same_name);
    hide(in_body_end_form);
    hide(pop_until_popped);
    hide(pop_until_named_popped);
    hide(pop_until_heading_popped);
    hide(in_body_any_other_end_tag);
    hide(in_body_adoption);
    hide(clear_to_last_marker);
}

/// The "in table" mode's "anything else": the "in body" rules (and the
/// "in head" rules they use) with foster parenting.
pub proof fn lemma_in_table_anything_else_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InTable, p),
    ensures
        stop_ok(outcome_parser(in_table_anything_else(env, p, t))),
{
    hide(mode_in_body);
    hide(mode_in_head);
    let pf = Parser { foster: true, ..p };
    let o = mode_in_body(env, pf, t);
    super::stop_in_body::lemma_in_body_stop(env, pf, t);
    lemma_in_body_using(env, pf, t);
    match o {
        Outcome::Using(Mode::InHead, q, t2) => {
            lemma_in_head_stop(env, q, t2);
        },
        _ => {},
    }
}

/// A character of the pending table character tokens keeps [`mk`].
pub proof fn lemma_in_table_char(env: EncFns, p: Parser, c: u32)
    ensures
        mk(p, outcome_parser(in_table_anything_else(env, p, Tok::Char(c)))),
{
    let pf = Parser { foster: true, ..p };
    assert(mk(p, pf));
    super::stop_in_body::lemma_in_body_char(pf, c);
    assert(in_table_anything_else(env, p, Tok::Char(c)) == outcome_without_foster(Outcome::Done(in_body_char(pf, c))));
}

/// Reprocessing the pending table character tokens keeps [`mk`].
pub proof fn lemma_reprocess_pending(env: EncFns, p: Parser, s: Seq<u32>, i: int)
    ensures
        mk(p, reprocess_pending(env, p, s, i)),
    decreases s.len() - i,
{
    hide(in_table_anything_else);
    if !(i < 0 || i >= s.len()) {
        let q = outcome_parser(in_table_anything_else(env, p, Tok::Char(s[i])));
        lemma_in_table_char(env, p, s[i]);
        lemma_reprocess_pending(env, q, s, i + 1);
        lemma_mk_trans(p, q, reprocess_pending(env, q, s, i + 1));
    }
}

/// §13.2.6.4.9 "in table".
pub proof fn lemma_in_table_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InTable, p),
    ensures
        stop_ok(outcome_parser(mode_in_table(env, p, t))),
{
    hide(in_table_anything_else);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    hide(has_in_scope);
    hide(parsing_template_contents);
    let q = outcome_parser(mode_in_table(env, p, t));
    lemma_in_table_anything_else_stop(env, p, t);
    let cur = current_node(p);
    if t is Char && (is_html(cur, Tag::Table) || is_html(cur, Tag::Tbody) || is_html(cur, Tag::Template) || is_html(
        cur,
        Tag::Tfoot,
    ) || is_html(cur, Tag::Thead) || is_html(cur, Tag::Tr)) {
    } else if t is Comment || t is Pi || t is Doctype || t is Start || t is End {
        if !(q == outcome_parser(in_table_anything_else(env, p, t))) {
            lemma_stop_from(p, q);
        }
    }
}

/// §13.2.6.4.10 "in table text".
pub proof fn lemma_in_table_text_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InTableText, p),
    ensures
        stop_ok(outcome_parser(mode_in_table_text(env, p, t))),
{
    hide(reprocess_pending);
    hide(insert_characters);
    hide(has_non_whitespace);
    lemma_reprocess_pending(env, p, p.pending_table_text, 0);
    lemma_insert_characters(p, p.pending_table_text);
    lemma_stop_from(p, outcome_parser(mode_in_table_text(env, p, t)));
}

// ---------------------------------------------------------------------
// The other modes

/// §13.2.6.4.11 "in caption".
pub proof fn lemma_in_caption_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InCaption, p),
    ensures
        stop_ok(outcome_parser(mode_in_caption(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_in_caption(env, p, t)));
}

/// §13.2.6.4.12 "in column group".
pub proof fn lemma_in_column_group_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InColumnGroup, p),
    ensures
        stop_ok(outcome_parser(mode_in_column_group(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_in_column_group(env, p, t)));
}

/// §13.2.6.4.13 "in table body".
pub proof fn lemma_in_table_body_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InTableBody, p),
    ensures
        stop_ok(outcome_parser(mode_in_table_body(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_in_table_body(env, p, t)));
}

/// §13.2.6.4.14 "in row".
pub proof fn lemma_in_row_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InRow, p),
    ensures
        stop_ok(outcome_parser(mode_in_row(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_in_row(env, p, t)));
}

/// §13.2.6.4.15 "in cell".
pub proof fn lemma_in_cell_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InCell, p),
    ensures
        stop_ok(outcome_parser(mode_in_cell(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_in_cell(env, p, t)));
}

/// §13.2.6.4.17 "after body".
pub proof fn lemma_after_body_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::AfterBody, p),
    ensures
        stop_ok(outcome_parser(mode_after_body(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_after_body(env, p, t)));
}

/// §13.2.6.4.18 "in frameset".
pub proof fn lemma_in_frameset_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InFrameset, p),
    ensures
        stop_ok(outcome_parser(mode_in_frameset(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_in_frameset(env, p, t)));
}

/// §13.2.6.4.19 "after frameset".
pub proof fn lemma_after_frameset_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::AfterFrameset, p),
    ensures
        stop_ok(outcome_parser(mode_after_frameset(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_after_frameset(env, p, t)));
}

/// §13.2.6.4.20 "after after body".
pub proof fn lemma_after_after_body_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::AfterAfterBody, p),
    ensures
        stop_ok(outcome_parser(mode_after_after_body(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_after_after_body(env, p, t)));
}

/// §13.2.6.4.21 "after after frameset".
pub proof fn lemma_after_after_frameset_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::AfterAfterFrameset, p),
    ensures
        stop_ok(outcome_parser(mode_after_after_frameset(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    lemma_stop_from(p, outcome_parser(mode_after_after_frameset(env, p, t)));
}

/// §13.2.6.4.16 "in template".
pub proof fn lemma_in_template_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InTemplate, p),
    ensures
        stop_ok(outcome_parser(mode_in_template(env, p, t))),
{
    let q = outcome_parser(mode_in_template(env, p, t));
    if t is Eof && open_has_html(p, Tag::Template) {
        lemma_template_on_stack(p);
        if q.stopped {
            assert(q.open.len() == 0);
            assert(q.mode == Mode::InBody);
            assert(templates_in(q.open, 0) == 0);
            assert forall|i: int| 0 <= i < q.template_modes.len() implies template_mode_ok(#[trigger] q.template_modes[i]) by {
                assert(q.template_modes[i] == p.template_modes[i]);
            }
        }
    } else if t is Start && !(t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag
        == Tag::Bgsound || t->Start_0.tag == Tag::Link || t->Start_0.tag == Tag::Meta || t->Start_0.tag == Tag::Noframes
        || t->Start_0.tag == Tag::Script || t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Template
        || t->Start_0.tag == Tag::Title) {
        assert(!q.stopped);
    } else {
        lemma_stop_from(p, q);
    }
}

/// §13.2.6.5 the rules for parsing tokens in foreign content.
pub proof fn lemma_foreign_stop(env: EncFns, p: Parser, t: Tok)
    requires
        !p.stopped,
        modes_ok(p),
    ensures
        stop_ok(outcome_parser(foreign_content(env, p, t))),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(adjust_foreign_start_tag);
    hide(adjusted_current_node);
    hide(is_foreign_breakout);
    hide(foreign_end_tag_loop);
    hide(svg_script_end);
    hide(pop_while);
    let q = outcome_parser(foreign_content(env, p, t));
    lemma_foreign_end_tag_loop(p, t, p.open.len() - 1);
    assert forall|r: Parser| #[trigger] svg_script_end(r) == pop(r) by {
        reveal(svg_script_end);
    }
    lemma_stop_from(p, q);
}

/// The foreign content end tag loop keeps [`mk`].
pub proof fn lemma_foreign_end_tag_loop(p: Parser, t: Tok, i: int)
    ensures
        mk(p, outcome_parser(foreign_end_tag_loop(p, t, i))),
    decreases i,
{
    if !(i <= 0 || i >= p.open.len()) && ascii_lowercase(p.open[i].name) != t->End_0.name && p.open[i - 1].ns
        != clazel_dom::spec::Namespace::Html {
        lemma_foreign_end_tag_loop(p, t, i - 1);
    }
}

} // verus!
