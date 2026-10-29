//! A parser the rules of "initial", "before html", "before head", "in
//! head", "in head noscript", "after head" and "text" stop has an empty
//! stack and satisfies `termination::modes_ok` ([`stop_ok`]).

#[allow(unused_imports)]
use super::spec::*;
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
    lemma_remove_open_at,
    lemma_reset_insertion_mode,
    lemma_push_marker,
    lemma_clear_to_last_marker,
};

/// A stopped parser has an empty stack and satisfies
/// `termination::modes_ok`.
pub open spec fn stop_ok(q: Parser) -> bool {
    q.stopped ==> q.open.len() == 0 && modes_ok(q)
}

/// What the rules `m` are applied to: a running parser whose modes satisfy
/// `termination::modes_ok`, and `termination::rules_ok`.
pub open spec fn stop_pre(m: Mode, p: Parser) -> bool {
    &&& !p.stopped
    &&& modes_ok(p)
    &&& rules_ok(Rules::Html(m), p)
}

/// A stopped parser that [`mk`] keeps from a parser whose modes are fine,
/// with the mode (and original mode) fine, satisfies [`stop_ok`]: its stack
/// is empty, so its `template` count is the context's, which the template
/// insertion modes of `p` (at most as many as `q`'s) cover.
pub proof fn lemma_stop_from(p: Parser, q: Parser)
    requires
        modes_ok(p),
        !p.stopped,
        mk(p, Parser { mode: p.mode, original_mode: p.original_mode, template_modes: p.template_modes, ..q }),
        q.template_modes.len() >= p.template_modes.len(),
        forall|i: int| 0 <= i < q.template_modes.len() ==> template_mode_ok(#[trigger] q.template_modes[i]),
        q.mode == Mode::InTableText ==> q.original_mode != Mode::Text && q.original_mode != Mode::InTableText,
        q.mode == Mode::Text ==> q.original_mode != Mode::Text && q.original_mode != Mode::InTableText,
        q.mode == Mode::InTemplate ==> q.template_modes.len() > 0,
        (q.mode == Mode::Text || q.mode == Mode::InTableText) && q.original_mode == Mode::InTemplate ==> q.template_modes.len() > 0,
    ensures
        stop_ok(q),
{
    if q.stopped {
        assert(q.open.len() == 0);
        assert(templates_in(q.open, 0) == 0);
        crate::termination::helpers_ranking::lemma_template_count(p);
    }
}

/// With a `template` element on the stack, the template insertion modes
/// outnumber the context's `template`.
pub proof fn lemma_template_on_stack(p: Parser)
    requires
        modes_ok(p),
        open_has_html(p, Tag::Template),
    ensures
        p.template_modes.len() >= 1 + (if p.context is Some && is_html(p.context->Some_0, Tag::Template) {
            1int
        } else {
            0int
        }),
{
    let j = crate::termination::helpers_ranking::lemma_open_has_html(p, Tag::Template);
    crate::termination::helpers_ranking::lemma_templates_in_pos(p.open, p.open.len() as int, j);
}

// ---------------------------------------------------------------------
// The modes

/// The "initial" DOCTYPE keeps [`mk`] but the mode, "before html".
pub proof fn lemma_initial_doctype(
    p: Parser,
    name: Option<Seq<u32>>,
    public_id: Option<Seq<u32>>,
    system_id: Option<Seq<u32>>,
    force_quirks: bool,
)
    ensures
        ({
            let q = initial_doctype(p, name, public_id, system_id, force_quirks);
            mk(p, Parser { mode: p.mode, ..q }) && q.mode == Mode::BeforeHtml
        }),
{
    hide(doctype_is_quirks);
    hide(doctype_is_limited_quirks);
    hide(has_doctype_child);
    hide(has_element_child);
}

/// The "in head" `meta` rule keeps [`mk`].
pub proof fn lemma_in_head_meta(env: EncFns, p: Parser, tt: TagTok)
    ensures
        mk(p, in_head_meta(env, p, tt)),
{
    hide(attr_value);
    hide(ascii_ci_eq);
    hide(meta_extracted_encoding);
}

/// The "in head" `script` start tag keeps [`mk`] but the modes.
pub proof fn lemma_in_head_script(p: Parser, tt: TagTok)
    ensures
        ({
            let q = in_head_script(p, tt);
            mk(p, Parser { mode: p.mode, original_mode: p.original_mode, ..q }) && q.mode == Mode::Text && q.original_mode
                == p.mode
        }),
{
}

/// §13.2.6.4.1 "initial".
pub proof fn lemma_initial_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::Initial, p),
    ensures
        stop_ok(outcome_parser(mode_initial(env, p, t))),
{
    hide(initial_doctype);
    hide(set_document_mode);
    let q = outcome_parser(mode_initial(env, p, t));
    if t is Doctype {
        lemma_initial_doctype(p, t->Doctype_name, t->Doctype_public_id, t->Doctype_system_id, t->Doctype_force_quirks);
    }
    assert(mk(p, Parser { mode: p.mode, ..q }) && (q.mode == p.mode || q.mode == Mode::BeforeHtml)) by {
        reveal(set_document_mode);
    }
    lemma_stop_from(p, q);
}

/// §13.2.6.4.2 "before html".
pub proof fn lemma_before_html_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::BeforeHtml, p),
    ensures
        stop_ok(outcome_parser(mode_before_html(env, p, t))),
{
    let q = outcome_parser(mode_before_html(env, p, t));
    lemma_stop_from(p, q);
}

/// §13.2.6.4.3 "before head".
pub proof fn lemma_before_head_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::BeforeHead, p),
    ensures
        stop_ok(outcome_parser(mode_before_head(env, p, t))),
{
    let q = outcome_parser(mode_before_head(env, p, t));
    lemma_stop_from(p, q);
}

/// The "in head" `template` end tag.
pub proof fn lemma_in_head_template_end_stop(p: Parser)
    requires
        !p.stopped,
        modes_ok(p),
    ensures
        stop_ok(in_head_template_end(p)),
{
    let q = in_head_template_end(p);
    if open_has_html(p, Tag::Template) {
        lemma_template_on_stack(p);
        let p1 = generate_all_implied_end_tags_thoroughly(p);
        let p2 = pop_until_popped(p1, Tag::Template);
        let p3 = clear_to_last_marker(p2);
        let p4 = Parser { template_modes: p3.template_modes.drop_last(), ..p3 };
        assert(mk(p, p3));
        if q.stopped {
            assert(q.open.len() == 0);
            assert(q.mode == Mode::InBody);
            assert(templates_in(q.open, 0) == 0);
            assert forall|i: int| 0 <= i < q.template_modes.len() implies template_mode_ok(#[trigger] q.template_modes[i]) by {
                assert(q.template_modes[i] == p.template_modes[i]);
            }
        }
    } else {
        lemma_stop_from(p, q);
    }
}

/// The "in head" `template` start tag.
pub proof fn lemma_in_head_template_start_stop(p: Parser, tt: TagTok)
    requires
        !p.stopped,
        modes_ok(p),
    ensures
        stop_ok(in_head_template_start(p, tt)),
{
    let q = in_head_template_start(p, tt);
    let p1 = push_marker(p);
    let p2 = Parser { frameset_ok: false, mode: Mode::InTemplate, template_modes: p1.template_modes.push(Mode::InTemplate), ..p1 };
    assert forall|i: int| 0 <= i < q.template_modes.len() implies template_mode_ok(#[trigger] q.template_modes[i]) by {
        if i < p.template_modes.len() {
            assert(q.template_modes[i] == p.template_modes[i]);
        }
    }
    lemma_stop_from(p, q);
}

/// §13.2.6.4.4 "in head".
pub proof fn lemma_in_head_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InHead, p),
    ensures
        stop_ok(outcome_parser(mode_in_head(env, p, t))),
{
    hide(in_head_template_end);
    hide(in_head_template_start);
    hide(in_head_meta);
    hide(in_head_script);
    hide(generic_text_parsing);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    hide(pop);
    let q = outcome_parser(mode_in_head(env, p, t));
    if t is Start {
        lemma_in_head_meta(env, p, t->Start_0);
        lemma_in_head_script(p, t->Start_0);
    }
    if t is Start && t->Start_0.tag == Tag::Template {
        lemma_in_head_template_start_stop(p, t->Start_0);
    } else if t is End && t->End_0.tag == Tag::Template {
        lemma_in_head_template_end_stop(p);
    } else {
        lemma_stop_from(p, q);
    }
}

/// §13.2.6.4.5 "in head noscript".
pub proof fn lemma_in_head_noscript_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::InHeadNoscript, p),
    ensures
        stop_ok(outcome_parser(mode_in_head_noscript(env, p, t))),
{
    let q = outcome_parser(mode_in_head_noscript(env, p, t));
    lemma_stop_from(p, q);
}

/// "after head" using the "in head" rules, with the `head` element pushed.
pub proof fn lemma_after_head_using_in_head_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::AfterHead, p),
    ensures
        stop_ok(outcome_parser(after_head_using_in_head(env, p, t))),
{
    hide(mode_in_head);
    match p.head {
        None => {},
        Some(h) => {
            let p1 = push(p, head_elem(h));
            crate::termination::helpers_ranking::lemma_tcount_push(p.open, head_elem(h));
            crate::termination::helpers_ranking::lemma_template_count(p);
            crate::termination::helpers_ranking::lemma_template_count(p1);
            assert(modes_ok(p1));
            lemma_in_head_stop(env, p1, t);
        },
    }
}

/// §13.2.6.4.6 "after head".
pub proof fn lemma_after_head_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::AfterHead, p),
    ensures
        stop_ok(outcome_parser(mode_after_head(env, p, t))),
{
    hide(after_head_using_in_head);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    let q = outcome_parser(mode_after_head(env, p, t));
    if t is Start && after_head_in_head_tag(t->Start_0.tag) && !(t->Start_0.tag == Tag::Html) && !(t->Start_0.tag
        == Tag::Body) && !(t->Start_0.tag == Tag::Frameset) {
        lemma_after_head_using_in_head_stop(env, p, t);
    } else {
        lemma_stop_from(p, q);
    }
}

/// §13.2.6.4.8 "text".
pub proof fn lemma_text_stop(env: EncFns, p: Parser, t: Tok)
    requires
        stop_pre(Mode::Text, p),
    ensures
        stop_ok(outcome_parser(mode_text(env, p, t))),
{
    let q = outcome_parser(mode_text(env, p, t));
    lemma_stop_from(p, q);
}

} // verus!
