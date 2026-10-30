//! Every insertion mode and foreign content satisfies [`step_ok`] from its
//! parser to its outcome's; all but "in head" (its `meta` rule changes the
//! encoding), "text" (its `script` end tag), and the modes that use the "in
//! head" rules directly ("after head", "in table", "in table text") even
//! [`grows`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use super::frame_base::lemma_pop, super::frame_base::lemma_push, super::frame_base::lemma_stop_parsing, super::frame_base::lemma_dom_insert, super::frame_base::lemma_dom_remove, super::frame_base::lemma_create, super::frame_base::lemma_create_element_for_token, super::frame_base::lemma_insert_element_at, super::frame_base::lemma_insert_foreign_element, super::frame_base::lemma_insert_html_element, super::frame_base::lemma_insert_characters, super::frame_base::lemma_insert_char, super::frame_base::lemma_insert_comment, super::frame_base::lemma_insert_pi, super::frame_base::lemma_generic_text_parsing, super::frame_base::lemma_pop_while, super::frame_base::lemma_generate_implied_end_tags, super::frame_base::lemma_generate_all_implied_end_tags_thoroughly, super::frame_base::lemma_pop_until_popped, super::frame_base::lemma_pop_until_heading_popped, super::frame_base::lemma_pop_until_node_popped, super::frame_base::lemma_remove_open_at, super::frame_base::lemma_reset_insertion_mode, super::frame_base::lemma_push_formatting, super::frame_base::lemma_push_marker, super::frame_base::lemma_clear_to_last_marker, super::frame_base::lemma_reconstruct_create, super::frame_base::lemma_reconstruct_formatting, super::frame_body::lemma_dom_reparent_children, super::frame_body::lemma_aa_inner, super::frame_body::lemma_aa_finish, super::frame_body::lemma_aa_outer, super::frame_body::lemma_adoption_agency, super::frame_body::lemma_add_missing_attributes, super::frame_body::lemma_pop_until_named_popped, super::frame_body::lemma_insert_and_pop, super::frame_body::lemma_frameset_not_ok, super::frame_body::lemma_close_p_element, super::frame_body::lemma_close_p_if_in_button_scope, super::frame_body::lemma_li_loop, super::frame_body::lemma_dd_dt_loop, super::frame_body::lemma_any_other_end_tag_loop, super::frame_body::lemma_in_body_any_other_end_tag, super::frame_body::lemma_in_body_adoption;

/// [`grows`] gives [`step_ok`].
pub broadcast proof fn lemma_grows_implies_step_ok(p: Parser, q: Parser)
    ensures
        grows(p, q) ==> #[trigger] step_ok(p, q),
{
    if grows(p, q) {
        lemma_grows_step_ok(p, q);
    }
}

/// Appending one action other than `StopParsing` to a running parser, which
/// stays running; a `ChangeEncoding` only from tentative to certain, any
/// other action keeping the confidence.
pub proof fn lemma_push_action(p: Parser, q: Parser, a: Action)
    requires
        !p.stopped,
        !q.stopped,
        q.actions == p.actions.push(a),
        !(a is StopParsing),
        a is ChangeEncoding ==> p.tentative && !q.tentative,
        !(a is ChangeEncoding) ==> q.tentative == p.tentative,
    ensures
        step_ok(p, q),
{
    assert(q.actions.subrange(0, p.actions.len() as int) =~= p.actions);
    assert forall|i: int, j: int|
        p.actions.len() <= i < j < q.actions.len() && (#[trigger] q.actions[i]) is ChangeEncoding implies !((#[trigger] q.actions[j]) is ChangeEncoding) by {
        assert(i == p.actions.len());
    }
}

// ---------------------------------------------------------------------
// The modes that grow

/// §13.2.6.4.1 "initial".
pub proof fn lemma_mode_initial(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_initial(env, p, t))),
{
}

/// §13.2.6.4.2 "before html".
pub proof fn lemma_mode_before_html(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_before_html(env, p, t))),
{
}

/// §13.2.6.4.3 "before head".
pub proof fn lemma_mode_before_head(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_before_head(env, p, t))),
{
}

/// §13.2.6.4.5 "in head noscript".
pub proof fn lemma_mode_in_head_noscript(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_head_noscript(env, p, t))),
{
}

/// §13.2.6.4.11 "in caption".
pub proof fn lemma_mode_in_caption(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_caption(env, p, t))),
{
}

/// §13.2.6.4.12 "in column group".
pub proof fn lemma_mode_in_column_group(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_column_group(env, p, t))),
{
}

/// §13.2.6.4.13 "in table body".
pub proof fn lemma_mode_in_table_body(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_table_body(env, p, t))),
{
}

/// §13.2.6.4.14 "in row".
pub proof fn lemma_mode_in_row(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_row(env, p, t))),
{
}

/// "Pop until a `td` or `th` has been popped".
pub broadcast proof fn lemma_pop_until_cell_popped(p: Parser)
    ensures
        grows(p, #[trigger] pop_until_cell_popped(p)),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        lemma_pop_until_cell_popped(pop(p));
    }
}

/// §13.2.6.4.15 "in cell".
pub proof fn lemma_mode_in_cell(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_cell(env, p, t))),
{
    broadcast use lemma_pop_until_cell_popped;

}

/// §13.2.6.4.16 "in template".
pub proof fn lemma_mode_in_template(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_template(env, p, t))),
{
}

/// §13.2.6.4.17 "after body".
pub proof fn lemma_mode_after_body(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_after_body(env, p, t))),
{
}

/// §13.2.6.4.18 "in frameset".
pub proof fn lemma_mode_in_frameset(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_in_frameset(env, p, t))),
{
}

/// §13.2.6.4.19 "after frameset".
pub proof fn lemma_mode_after_frameset(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_after_frameset(env, p, t))),
{
}

/// §13.2.6.4.20 "after after body".
pub proof fn lemma_mode_after_after_body(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_after_after_body(env, p, t))),
{
}

/// §13.2.6.4.21 "after after frameset".
pub proof fn lemma_mode_after_after_frameset(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(mode_after_after_frameset(env, p, t))),
{
}

/// The foreign content end tag loop.
pub proof fn lemma_foreign_end_tag_loop(p: Parser, t: Tok, i: int)
    ensures
        grows(p, outcome_parser(foreign_end_tag_loop(p, t, i))),
    decreases i,
{
    if !(i <= 0 || i >= p.open.len()) && ascii_lowercase(p.open[i].name) != t->End_0.name && p.open[i - 1].ns
        != clazel_dom::spec::Namespace::Html {
        lemma_foreign_end_tag_loop(p, t, i - 1);
    }
}

/// §13.2.6.5 the rules for parsing tokens in foreign content.
pub proof fn lemma_foreign_content(env: EncFns, p: Parser, t: Tok)
    ensures
        grows(p, outcome_parser(foreign_content(env, p, t))),
{
    hide(foreign_end_tag_loop);
    lemma_foreign_end_tag_loop(p, t, p.open.len() - 1);
}

// ---------------------------------------------------------------------
// The modes that may change the encoding or ready a script

/// "Change the encoding", from a tentative confidence.
pub proof fn lemma_change_the_encoding(p: Parser, enc: nat)
    requires
        p.tentative,
    ensures
        step_ok(p, change_the_encoding(p, enc)),
{
    if p.stopped {
        lemma_step_ok_refl(p);
    } else {
        lemma_push_action(p, change_the_encoding(p, enc), Action::ChangeEncoding(enc));
    }
}

/// The "in head" `meta` rule.
pub proof fn lemma_in_head_meta(env: EncFns, p: Parser, tt: TagTok)
    ensures
        step_ok(p, in_head_meta(env, p, tt)),
{
    hide(insert_html_element);
    hide(pop);
    hide(change_the_encoding);
    let p1 = pop(insert_html_element(p, tt).0);
    assert(grows(p, p1));
    let charset = attr_value(tt.attrs, in_head_name_charset());
    let http_equiv = attr_value(tt.attrs, in_head_name_http_equiv());
    let content = attr_value(tt.attrs, in_head_name_content());
    if charset is Some && (env.get_an_encoding)(charset->Some_0) is Some && p1.tentative {
        lemma_change_the_encoding(p1, (env.get_an_encoding)(charset->Some_0)->Some_0);
        lemma_grows_step_ok_trans(p, p1, in_head_meta(env, p, tt));
    } else if http_equiv is Some && ascii_ci_eq(http_equiv->Some_0, in_head_content_type()) && content is Some
        && meta_extracted_encoding(env, content->Some_0) is Some && p1.tentative {
        lemma_change_the_encoding(p1, meta_extracted_encoding(env, content->Some_0)->Some_0);
        lemma_grows_step_ok_trans(p, p1, in_head_meta(env, p, tt));
    } else {
        lemma_grows_step_ok(p, p1);
    }
}

/// §13.2.6.4.4 "in head".
pub proof fn lemma_mode_in_head(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(mode_in_head(env, p, t))),
{
    hide(in_head_meta);
    hide(in_head_template_start);
    hide(in_head_template_end);
    hide(in_head_script);
    hide(generic_text_parsing);
    hide(insert_html_element);
    broadcast use lemma_grows_implies_step_ok;

    if t is Start {
        lemma_in_head_meta(env, p, t->Start_0);
    }
    assert(grows(p, in_head_template_start(p, t->Start_0))) by {
        reveal(in_head_template_start);
    }
    assert(grows(p, in_head_template_end(p))) by {
        reveal(in_head_template_end);
    }
    assert(grows(p, in_head_script(p, t->Start_0))) by {
        reveal(in_head_script);
    }
}

/// The "text" mode's `script` end tag.
pub proof fn lemma_text_script_end(p: Parser)
    ensures
        step_ok(p, text_script_end(p)),
{
    let script = current_node(p);
    let p2 = Parser { mode: pop(p).original_mode, ..pop(p) };
    if p2.stopped {
        lemma_grows_step_ok(p, p2);
    } else {
        lemma_push_action(p2, text_script_end(p), Action::ScriptReady(script.id));
        lemma_grows_step_ok_trans(p, p2, text_script_end(p));
    }
}

/// §13.2.6.4.8 "text".
pub proof fn lemma_mode_text(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(mode_text(env, p, t))),
{
    hide(text_script_end);
    broadcast use lemma_grows_implies_step_ok;

    lemma_text_script_end(p);
}

/// "after head" using the "in head" rules.
pub proof fn lemma_after_head_using_in_head(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(after_head_using_in_head(env, p, t))),
{
    hide(mode_in_head);
    hide(push);
    hide(remove_open_at);
    match p.head {
        None => lemma_step_ok_refl(p),
        Some(h) => {
            let p1 = push(p, head_elem(h));
            lemma_mode_in_head(env, p1, t);
            lemma_grows_step_ok_trans(p, p1, outcome_parser(mode_in_head(env, p1, t)));
            match mode_in_head(env, p1, t) {
                Outcome::Done(p2) => {
                    let i = open_index_of(p2, h);
                    if !(p2.stopped || i < 0) {
                        lemma_step_ok_grows(p, p2, remove_open_at(p2, i));
                    }
                },
                _ => {},
            }
        },
    }
}

/// §13.2.6.4.6 "after head".
pub proof fn lemma_mode_after_head(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(mode_after_head(env, p, t))),
{
    hide(after_head_using_in_head);
    broadcast use lemma_grows_implies_step_ok;

    lemma_after_head_using_in_head(env, p, t);
}

/// The outcome with foster parenting disabled keeps [`step_ok`].
pub proof fn lemma_without_foster(p: Parser, o: Outcome)
    requires
        step_ok(p, outcome_parser(o)),
    ensures
        step_ok(p, outcome_parser(outcome_without_foster(o))),
{
    lemma_step_ok_grows(p, outcome_parser(o), outcome_parser(outcome_without_foster(o)));
}

/// The "in table" mode's "anything else".
pub proof fn lemma_in_table_anything_else(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(in_table_anything_else(env, p, t))),
{
    hide(mode_in_body);
    hide(mode_in_head);
    hide(outcome_without_foster);
    let pf = Parser { foster: true, ..p };
    let o = mode_in_body(env, pf, t);
    crate::theorems::frame_in_body::lemma_mode_in_body(env, pf, t);
    lemma_grows_step_ok(p, outcome_parser(o));
    match o {
        Outcome::Using(Mode::InHead, q, t2) => {
            lemma_mode_in_head(env, q, t2);
            lemma_step_ok_trans(p, q, outcome_parser(mode_in_head(env, q, t2)));
            lemma_without_foster(p, mode_in_head(env, q, t2));
        },
        _ => {
            lemma_without_foster(p, o);
        },
    }
}

/// §13.2.6.4.9 "in table".
pub proof fn lemma_mode_in_table(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(mode_in_table(env, p, t))),
{
    hide(in_table_anything_else);
    broadcast use lemma_grows_implies_step_ok;

    lemma_in_table_anything_else(env, p, t);
}

/// Reprocess the pending table character tokens.
pub proof fn lemma_reprocess_pending(env: EncFns, p: Parser, s: Seq<u32>, i: int)
    ensures
        step_ok(p, reprocess_pending(env, p, s, i)),
    decreases s.len() - i,
{
    hide(in_table_anything_else);
    if i < 0 || i >= s.len() {
        lemma_step_ok_refl(p);
    } else {
        let q = outcome_parser(in_table_anything_else(env, p, Tok::Char(s[i])));
        lemma_in_table_anything_else(env, p, Tok::Char(s[i]));
        lemma_reprocess_pending(env, q, s, i + 1);
        lemma_step_ok_trans(p, q, reprocess_pending(env, p, s, i));
    }
}

/// §13.2.6.4.10 "in table text".
pub proof fn lemma_mode_in_table_text(env: EncFns, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(mode_in_table_text(env, p, t))),
{
    hide(reprocess_pending);
    hide(insert_characters);
    broadcast use lemma_grows_implies_step_ok;

    if !(t is Char) {
        let pending = p.pending_table_text;
        let p1 = if has_non_whitespace(pending) {
            reprocess_pending(env, p, pending, 0)
        } else if pending.len() == 0 {
            p
        } else {
            insert_characters(p, pending)
        };
        if has_non_whitespace(pending) {
            lemma_reprocess_pending(env, p, pending, 0);
        } else {
            lemma_grows_step_ok(p, p1);
        }
        lemma_step_ok_grows(p, p1, Parser { mode: p1.original_mode, ..p1 });
    }
}

// ---------------------------------------------------------------------
// Every set of rules

/// The rules of every insertion mode.
pub proof fn lemma_mode_rules(env: EncFns, m: Mode, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(mode_rules(env, m, p, t))),
{
    hide(mode_initial);
    hide(mode_before_html);
    hide(mode_before_head);
    hide(mode_in_head);
    hide(mode_in_head_noscript);
    hide(mode_after_head);
    hide(mode_in_body);
    hide(mode_text);
    hide(mode_in_table);
    hide(mode_in_table_text);
    hide(mode_in_caption);
    hide(mode_in_column_group);
    hide(mode_in_table_body);
    hide(mode_in_row);
    hide(mode_in_cell);
    hide(mode_in_template);
    hide(mode_after_body);
    hide(mode_in_frameset);
    hide(mode_after_frameset);
    hide(mode_after_after_body);
    hide(mode_after_after_frameset);
    broadcast use lemma_grows_implies_step_ok;

    match m {
        Mode::Initial => lemma_mode_initial(env, p, t),
        Mode::BeforeHtml => lemma_mode_before_html(env, p, t),
        Mode::BeforeHead => lemma_mode_before_head(env, p, t),
        Mode::InHead => lemma_mode_in_head(env, p, t),
        Mode::InHeadNoscript => lemma_mode_in_head_noscript(env, p, t),
        Mode::AfterHead => lemma_mode_after_head(env, p, t),
        Mode::InBody => crate::theorems::frame_in_body::lemma_mode_in_body(env, p, t),
        Mode::Text => lemma_mode_text(env, p, t),
        Mode::InTable => lemma_mode_in_table(env, p, t),
        Mode::InTableText => lemma_mode_in_table_text(env, p, t),
        Mode::InCaption => lemma_mode_in_caption(env, p, t),
        Mode::InColumnGroup => lemma_mode_in_column_group(env, p, t),
        Mode::InTableBody => lemma_mode_in_table_body(env, p, t),
        Mode::InRow => lemma_mode_in_row(env, p, t),
        Mode::InCell => lemma_mode_in_cell(env, p, t),
        Mode::InTemplate => lemma_mode_in_template(env, p, t),
        Mode::AfterBody => lemma_mode_after_body(env, p, t),
        Mode::InFrameset => lemma_mode_in_frameset(env, p, t),
        Mode::AfterFrameset => lemma_mode_after_frameset(env, p, t),
        Mode::AfterAfterBody => lemma_mode_after_after_body(env, p, t),
        Mode::AfterAfterFrameset => lemma_mode_after_after_frameset(env, p, t),
    }
}

/// Every set of rules.
pub proof fn lemma_apply_rules(env: EncFns, r: Rules, p: Parser, t: Tok)
    ensures
        step_ok(p, outcome_parser(apply_rules(env, r, p, t))),
{
    hide(mode_rules);
    hide(foreign_content);
    broadcast use lemma_grows_implies_step_ok;

    match r {
        Rules::Html(m) => lemma_mode_rules(env, m, p, t),
        Rules::Foreign => lemma_foreign_content(env, p, t),
    }
}

} // verus!
