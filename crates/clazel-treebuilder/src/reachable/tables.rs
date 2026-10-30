//! The rules of the table modes and "in template" keep the reachable-state
//! facts ([`next_core`], see [`super`]).

#[cfg(verus_only)]
use super::body::*;
#[cfg(verus_only)]
use super::body_tags::*;
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
// Shared

/// Pop while the current node satisfies `f`, which an entry at `k >= 1`
/// does not: at least two entries stay.
pub proof fn lemma_clear_back_keeps(p: Parser, f: spec_fn(Elem) -> bool, k: int)
    requires
        good(p),
        !p.stopped,
        p.mode != Mode::InCell,
        !f(p.open[0]),
        1 <= k < p.open.len(),
        !f(p.open[k]),
    ensures
        keeps(p, pop_while(p, f)),
        pop_while(p, f).open.len() >= 2,
        pop_while(p, f) == (Parser { open: pop_while(p, f).open, ..p }),
{
    crate::termination::helpers_tables::lemma_pop_while(p, f);
    lemma_pop_while_keeps(p, f);
}

/// A rule application whose outcome continues in a [`rooted_mode`] or is
/// done there.
pub proof fn lemma_to_mode(p: Parser, q1: Parser, m: Mode)
    requires
        modes_ok(p),
        keeps(p, q1),
        rooted_mode(m),
        m == Mode::InTemplate ==> p.template_modes.len() > 0,
        m == Mode::InCell && p.mode != Mode::InCell && !q1.stopped ==> cell_scoped(q1.open),
    ensures
        next_core(Outcome::Done(Parser { mode: m, ..q1 })),
        next_core(Outcome::Reprocess(Parser { mode: m, ..q1 }, Tok::Eof)),
{
    if !q1.stopped {
        lemma_finish(p, q1, Parser { mode: m, ..q1 });
    }
}

/// The outcome of a reprocessing has [`next_core`] for every token when it
/// has it for one.
pub proof fn lemma_reprocess_any(q: Parser, t: Tok)
    requires
        next_core(Outcome::Reprocess(q, Tok::Eof)),
    ensures
        next_core(Outcome::Reprocess(q, t)),
{
}

/// "Reset the insertion mode appropriately" after popping, done or
/// reprocessing.
pub proof fn lemma_reset_outcome(p: Parser, p1: Parser)
    requires
        modes_ok(p),
        keeps(p, p1),
        !p1.stopped,
    ensures
        next_core(Outcome::Done(reset_insertion_mode(p1))),
        reset_insertion_mode(p1).stopped || reach_core(reset_insertion_mode(p1)),
{
    assert(crate::termination::helpers_ranking::count_ok(p1));
    lemma_reset_keeps(p1);
    crate::termination::helpers_ranking::lemma_reset_modes_ok(p1);
}

/// [`next_core`] does not read the foster parenting flag.
pub proof fn lemma_without_foster(o: Outcome)
    requires
        next_core(o),
    ensures
        next_core(outcome_without_foster(o)),
{
}

// ---------------------------------------------------------------------
// "in table"

/// The parser "in table"'s anything else entry gives the "in body" rules.
pub proof fn lemma_foster_inv(p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
    ensures
        rules_inv(Rules::Html(Mode::InBody), Parser { foster: true, ..p }, t),
{
    assert(rooted_mode(p.mode));
}

/// The "in head" rules for the tokens "in body" sends them, with foster
/// parenting.
pub proof fn lemma_foster_in_head(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InBody), p, t),
        rooted_mode(p.mode),
        mode_in_body(env, p, t) is Using,
        mode_in_body(env, p, t)->Using_0 == Mode::InHead,
    ensures
        next_core(outcome_without_foster(mode_in_head(env, mode_in_body(env, p, t)->Using_1, mode_in_body(env, p, t)->Using_2))),
{
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_eof);
    hide(in_body_char);
    hide(insert_comment);
    hide(insert_pi);
    match t {
        Tok::Start(tt) => {
            crate::termination::helpers_in_body::lemma_in_body_start_tag_outcome(p, t, tt);
        },
        Tok::End(tt) => {
            crate::termination::helpers_in_body::lemma_in_body_end_tag_outcome(p, t, tt);
        },
        Tok::Eof => {
            crate::termination::helpers_in_body::lemma_in_body_eof_outcome(p, t);
        },
        _ => {},
    }
    let q = mode_in_body(env, p, t)->Using_1;
    let t2 = mode_in_body(env, p, t)->Using_2;
    assert(q == p && t2 == t);
    assert(rules_inv(Rules::Html(Mode::InHead), q, t2));
    lemma_in_head_reach(env, q, t2);
    lemma_without_foster(mode_in_head(env, q, t2));
}

/// The "in table" anything else entry: the "in body" rules with foster
/// parenting.
pub proof fn lemma_in_table_anything_else_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
        !(t is Eof),
    ensures
        next_core(in_table_anything_else(env, p, t)),
{
    hide(mode_in_body);
    hide(mode_in_head);
    hide(rules_inv);
    let pf = Parser { foster: true, ..p };
    lemma_foster_inv(p, t);
    assert(rooted_mode(pf.mode)) by {
        reveal(rules_inv);
    }
    super::body_tags::lemma_in_body_reach(env, pf, t);
    let o = mode_in_body(env, pf, t);
    if o is Using && o->Using_0 == Mode::InHead {
        lemma_foster_in_head(env, pf, t);
    } else {
        lemma_without_foster(o);
    }
}

/// "In table" for a start tag of a table section or row element.
pub proof fn lemma_in_table_section(p: Parser, t: Tok, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        p.mode != Mode::InCell,
        modes_ok(p),
        rooted_mode(p.mode),
        tok_tagged(tt),
        tt.tag == Tag::Caption || tt.tag == Tag::Colgroup || tt.tag == Tag::Col || tt.tag == Tag::Tbody || tt.tag == Tag::Tfoot
            || tt.tag == Tag::Thead || tt.tag == Tag::Td || tt.tag == Tag::Th || tt.tag == Tag::Tr,
    ensures
        ({
            let p1 = clear_stack_back_to_table_context(p);
            let q = if tt.tag == Tag::Caption {
                insert_html_element(push_marker(p1), tt).0
            } else if tt.tag == Tag::Colgroup || tt.tag == Tag::Tbody || tt.tag == Tag::Tfoot || tt.tag == Tag::Thead {
                insert_html_element(p1, tt).0
            } else if tt.tag == Tag::Col {
                insert_html_element(p1, start_tag_named(name_colgroup())).0
            } else {
                insert_html_element(p1, start_tag_named(name_tbody())).0
            };
            keeps(p, q)
        }),
{
    hide(insert_html_element);
    let f = |e: Elem| !(is_html(e, Tag::Table) || is_html(e, Tag::Template) || is_html(e, Tag::Html));
    lemma_pop_while_keeps(p, f);
    let p1 = clear_stack_back_to_table_context(p);
    assert(tag_of(name_colgroup()) == Tag::Colgroup) by (compute);
    assert(tag_of(name_tbody()) == Tag::Tbody) by (compute);
    if tt.tag == Tag::Caption {
        lemma_push_marker_keeps(p1);
        lemma_keeps_trans(p, p1, push_marker(p1));
        lemma_then_insert(p, push_marker(p1), tt);
    } else if tt.tag == Tag::Colgroup || tt.tag == Tag::Tbody || tt.tag == Tag::Tfoot || tt.tag == Tag::Thead {
        lemma_then_insert(p, p1, tt);
    } else if tt.tag == Tag::Col {
        lemma_then_insert(p, p1, start_tag_named(name_colgroup()));
    } else {
        lemma_then_insert(p, p1, start_tag_named(name_tbody()));
    }
}

/// "In table": the table section and row start tags.
pub proof fn lemma_in_table_sections(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
        t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Colgroup || t->Start_0.tag == Tag::Col
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
            == Tag::Td || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Tr),
    ensures
        next_core(mode_in_table(env, p, t)),
{
    hide(in_table_anything_else);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_context);
    hide(push_marker);
    hide(insert_comment);
    hide(insert_pi);
    hide(reset_insertion_mode);
    hide(pop_until_popped);
    hide(in_table_input_is_hidden);
    hide(parsing_template_contents);
    hide(has_in_scope);
    assert(rooted_mode(p.mode));
    assert(good(p));
    lemma_keeps_refl(p);
    let tt = t->Start_0;
    lemma_in_table_section(p, t, tt);
    let p1 = clear_stack_back_to_table_context(p);
    if tt.tag == Tag::Caption {
        lemma_to_mode(p, insert_html_element(push_marker(p1), tt).0, Mode::InCaption);
    } else if tt.tag == Tag::Colgroup {
        lemma_to_mode(p, insert_html_element(p1, tt).0, Mode::InColumnGroup);
    } else if tt.tag == Tag::Tbody || tt.tag == Tag::Tfoot || tt.tag == Tag::Thead {
        lemma_to_mode(p, insert_html_element(p1, tt).0, Mode::InTableBody);
    } else if tt.tag == Tag::Col {
        let q1 = insert_html_element(p1, start_tag_named(name_colgroup())).0;
        lemma_to_mode(p, q1, Mode::InColumnGroup);
        lemma_reprocess_any(Parser { mode: Mode::InColumnGroup, ..q1 }, t);
    } else {
        let q1 = insert_html_element(p1, start_tag_named(name_tbody())).0;
        lemma_to_mode(p, q1, Mode::InTableBody);
        lemma_reprocess_any(Parser { mode: Mode::InTableBody, ..q1 }, t);
    }
}

/// "In table": the `table` start and end tags.
pub proof fn lemma_in_table_table(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
        (t is Start && t->Start_0.tag == Tag::Table) || (t is End && t->End_0.tag == Tag::Table),
    ensures
        next_core(mode_in_table(env, p, t)),
{
    hide(in_table_anything_else);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_context);
    hide(push_marker);
    hide(insert_comment);
    hide(insert_pi);
    hide(reset_insertion_mode);
    hide(pop_until_popped);
    hide(in_table_input_is_hidden);
    hide(parsing_template_contents);
    hide(has_in_scope);
    assert(rooted_mode(p.mode));
    assert(good(p));
    lemma_keeps_refl(p);
    if has_in_scope(p, Tag::Table, Scope::Table) {
        reveal(has_in_scope);
        let k = lemma_scope_k(p.open, |e: Elem| is_html(e, Tag::Table), Scope::Table);
        lemma_pop_until_popped_keeps(p, Tag::Table, k);
        let p1 = pop_until_popped(p, Tag::Table);
        if !p1.stopped {
            lemma_reset_outcome(p, p1);
        }
    }
}

/// "In table": the hidden `input` and the `form` start tags.
pub proof fn lemma_in_table_input_form(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
        t is Start && (t->Start_0.tag == Tag::Input || t->Start_0.tag == Tag::Form),
        t->Start_0.tag == Tag::Input ==> in_table_input_is_hidden(t->Start_0),
    ensures
        next_core(mode_in_table(env, p, t)),
{
    hide(in_table_anything_else);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_context);
    hide(push_marker);
    hide(insert_comment);
    hide(insert_pi);
    hide(reset_insertion_mode);
    hide(pop_until_popped);
    hide(in_table_input_is_hidden);
    hide(parsing_template_contents);
    hide(has_in_scope);
    assert(rooted_mode(p.mode));
    assert(good(p));
    lemma_keeps_refl(p);
    reveal(insert_html_element);
    lemma_insert_html_keeps(p, t->Start_0);
    let (p1, e) = insert_html_element(p, t->Start_0);
    if t->Start_0.tag == Tag::Input {
        if !p1.stopped {
            lemma_pop_keeps(p1);
            lemma_keeps_trans(p, p1, pop(p1));
            lemma_ib_done(p, pop(p1));
        }
    } else if !(p.form is Some && !parsing_template_contents(p)) {
        let p2 = if !parsing_template_contents(p1) && !p1.stopped {
            Parser { form: Some(e.id), ..p1 }
        } else {
            p1
        };
        if !p2.stopped {
            assert(good(p2));
            assert(keeps(p, p2));
            lemma_pop_keeps(p2);
            lemma_keeps_trans(p, p2, pop(p2));
            lemma_ib_done(p, pop(p2));
        }
    }
}

/// "In table": the other cases.
pub proof fn lemma_in_table_rest(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
        !((t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Colgroup || t->Start_0.tag == Tag::Col
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
            == Tag::Td || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Tr)) || ((t is Start && t->Start_0.tag == Tag::Table) || (t is End && t->End_0.tag == Tag::Table)) || (t is Start && t->Start_0.tag == Tag::Form)),
        !(t is Start && t->Start_0.tag == Tag::Input && in_table_input_is_hidden(t->Start_0)),
    ensures
        next_core(mode_in_table(env, p, t)),
{
    hide(in_table_anything_else);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_context);
    hide(push_marker);
    hide(insert_comment);
    hide(insert_pi);
    hide(reset_insertion_mode);
    hide(pop_until_popped);
    hide(in_table_input_is_hidden);
    hide(parsing_template_contents);
    hide(has_in_scope);
    assert(rooted_mode(p.mode));
    assert(good(p));
    lemma_keeps_refl(p);
    let cur = current_node(p);
    if t is Char && (is_html(cur, Tag::Table) || is_html(cur, Tag::Tbody) || is_html(cur, Tag::Template) || is_html(
        cur,
        Tag::Tfoot,
    ) || is_html(cur, Tag::Thead) || is_html(cur, Tag::Tr)) {
        let q = Parser { pending_table_text: seq![], original_mode: p.mode, mode: Mode::InTableText, ..p };
        assert(p.open.len() >= 2);
        assert(reach_core(q));
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, None);
        let q = insert_comment(p, t->Comment_0, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, None);
        let q = insert_pi(p, t->Pi_0, t->Pi_1, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Doctype || t is Eof || (t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption
        || t->End_0.tag == Tag::Col || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Tbody
        || t->End_0.tag == Tag::Td || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Th || t->End_0.tag == Tag::Thead
        || t->End_0.tag == Tag::Tr || t->End_0.tag == Tag::Template)) {
    } else if (t is Start && (t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Script || t->Start_0.tag
        == Tag::Template)) || (t is Start && t->Start_0.tag == Tag::Input && in_table_input_is_hidden(t->Start_0)) {
    } else {
        reveal(in_table_anything_else);
        lemma_in_table_anything_else_reach(env, p, t);
    }
}

/// The "in table" rules.
pub proof fn lemma_in_table_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTable), p, t),
    ensures
        next_core(mode_in_table(env, p, t)),
{
    if t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Colgroup || t->Start_0.tag == Tag::Col
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
            == Tag::Td || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Tr) {
        lemma_in_table_sections(env, p, t);
    } else if (t is Start && t->Start_0.tag == Tag::Table) || (t is End && t->End_0.tag == Tag::Table) {
        lemma_in_table_table(env, p, t);
    } else if (t is Start && t->Start_0.tag == Tag::Form) || (t is Start && t->Start_0.tag == Tag::Input && in_table_input_is_hidden(t->Start_0)) {
        lemma_in_table_input_form(env, p, t);
    } else {
        lemma_in_table_rest(env, p, t);
    }
}

// ---------------------------------------------------------------------
// "in table text"

/// [`reprocess_pending`] keeps a live parser.
pub proof fn lemma_reprocess_pending_keeps(env: EncFns, p: Parser, s: Seq<u32>, i: int)
    requires
        live(p),
    ensures
        keeps(p, reprocess_pending(env, p, s, i)),
    decreases s.len() - i,
{
    hide(in_table_anything_else);
    if i < 0 || i >= s.len() {
        lemma_keeps_refl(p);
    } else {
        let c = s[i];
        let pf = Parser { foster: true, ..p };
        assert(in_table_anything_else(env, p, Tok::Char(c)) == outcome_without_foster(Outcome::Done(in_body_char(pf, c)))) by {
            reveal(in_table_anything_else);
        }
        lemma_flags_keeps(p, pf);
        let q0 = in_body_char(pf, c);
        if c != 0 {
            lemma_keeps_live(p, pf);
            lemma_then_reconstruct(pf, pf);
            let r = reconstruct_formatting(pf);
            lemma_keeps_live(pf, r);
            lemma_insert_char_keeps(r, c);
            lemma_keeps_trans(pf, r, insert_char(r, c));
            lemma_then_fno(pf, insert_char(r, c));
            lemma_keeps_trans(p, pf, q0);
        } else {
            lemma_keeps_refl(pf);
        }
        let q = Parser { foster: false, ..q0 };
        lemma_keeps_live(p, q0);
        lemma_flags_keeps(q0, q);
        lemma_keeps_trans(p, q0, q);
        lemma_reprocess_pending_keeps(env, q, s, i + 1);
        lemma_keeps_trans(p, q, reprocess_pending(env, q, s, i + 1));
    }
}

/// The "in table text" rules.
pub proof fn lemma_in_table_text_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTableText), p, t),
    ensures
        next_core(mode_in_table_text(env, p, t)),
{
    hide(reprocess_pending);
    hide(insert_characters);
    assert(p.mode == Mode::InTableText);
    assert(good(p));
    if t is Char {
        if t->Char_0 != 0 {
            let q = Parser { pending_table_text: p.pending_table_text.push(t->Char_0), ..p };
            lemma_core_frame(p, q);
        }
    } else {
        let pending = p.pending_table_text;
        let p1 = if has_non_whitespace(pending) {
            reprocess_pending(env, p, pending, 0)
        } else if pending.len() == 0 {
            p
        } else {
            insert_characters(p, pending)
        };
        if has_non_whitespace(pending) {
            lemma_reprocess_pending_keeps(env, p, pending, 0);
        } else if pending.len() == 0 {
            lemma_keeps_refl(p);
        } else {
            lemma_insert_characters_keeps(p, pending);
        }
        let q = Parser { mode: p1.original_mode, ..p1 };
        if !q.stopped {
            assert(rooted_mode(q.mode));
            assert(good(q));
        }
    }
}

// ---------------------------------------------------------------------
// "in caption"

/// "In caption": close the caption.
pub proof fn lemma_close_caption(p: Parser)
    requires
        good(p),
        !p.stopped,
        p.mode != Mode::InCell,
        modes_ok(p),
        has_in_scope(p, Tag::Caption, Scope::Table),
    ensures
        keeps(p, clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), Tag::Caption))),
{
    let f = |e: Elem| is_html(e, Tag::Caption);
    let k = lemma_scope_k(p.open, f, Scope::Table);
    let q = generate_implied_end_tags(p, None);
    crate::exec::stack::lemma_pop_until_popped(q, Tag::Caption);
    lemma_close_keeps(p, None, f, k);
    let q2 = pop_until_popped(q, Tag::Caption);
    lemma_keeps_live(p, q2);
    lemma_clear_keeps(q2);
    lemma_keeps_trans(p, q2, clear_to_last_marker(q2));
}

/// The "in caption" rules.
pub proof fn lemma_in_caption_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InCaption), p, t),
    ensures
        next_core(mode_in_caption(env, p, t)),
{
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    assert(rooted_mode(p.mode));
    assert(good(p));
    if has_in_scope(p, Tag::Caption, Scope::Table) {
        lemma_close_caption(p);
        let q1 = clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), Tag::Caption));
        lemma_to_mode(p, q1, Mode::InTable);
        lemma_reprocess_any(Parser { mode: Mode::InTable, ..q1 }, t);
    }
}

// ---------------------------------------------------------------------
// "in column group"

/// The "in column group" rules.
pub proof fn lemma_in_column_group_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InColumnGroup), p, t),
    ensures
        next_core(mode_in_column_group(env, p, t)),
{
    hide(insert_html_element);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    assert(rooted_mode(p.mode));
    assert(good(p));
    lemma_keeps_refl(p);
    if t is Char && is_ascii_whitespace(t->Char_0) {
        lemma_insert_char_keeps(p, t->Char_0);
        let q = insert_char(p, t->Char_0);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, None);
        let q = insert_comment(p, t->Comment_0, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, None);
        let q = insert_pi(p, t->Pi_0, t->Pi_1, None);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Doctype || (t is Start && t->Start_0.tag == Tag::Html) {
    } else if t is Start && t->Start_0.tag == Tag::Col {
        lemma_then_insert(p, p, t->Start_0);
        let p1 = insert_html_element(p, t->Start_0).0;
        if !p1.stopped {
            reveal(insert_html_element);
            lemma_insert_html_keeps(p, t->Start_0);
            lemma_pop_keeps(p1);
            lemma_keeps_trans(p, p1, pop(p1));
            lemma_ib_done(p, pop(p1));
        }
    } else if (t is End && t->End_0.tag == Tag::Colgroup) || !((t is End && t->End_0.tag == Tag::Col) || (t is Start
        && t->Start_0.tag == Tag::Template) || (t is End && t->End_0.tag == Tag::Template) || t is Eof) {
        if is_html(current_node(p), Tag::Colgroup) {
            lemma_pop_keeps(p);
            lemma_to_mode(p, pop(p), Mode::InTable);
            lemma_reprocess_any(Parser { mode: Mode::InTable, ..pop(p) }, t);
        }
    }
}

// ---------------------------------------------------------------------
// "in table body" and "in row"

/// Clear back to a table body or row context and pop, with an entry the
/// clearing stops at, at `k >= 1`.
pub proof fn lemma_clear_pop(p: Parser, f: spec_fn(Elem) -> bool, k: int, m: Mode)
    requires
        good(p),
        !p.stopped,
        p.mode != Mode::InCell,
        m != Mode::InCell,
        modes_ok(p),
        rooted_mode(m),
        m != Mode::InTemplate,
        !f(p.open[0]),
        1 <= k < p.open.len(),
        !f(p.open[k]),
    ensures
        next_core(Outcome::Done(Parser { mode: m, ..pop(pop_while(p, f)) })),
        next_core(Outcome::Reprocess(Parser { mode: m, ..pop(pop_while(p, f)) }, Tok::Eof)),
{
    lemma_clear_back_keeps(p, f, k);
    let p1 = pop_while(p, f);
    assert(!in_cell(p1));
    lemma_pop_keeps(p1);
    lemma_keeps_trans(p, p1, pop(p1));
    lemma_to_mode(p, pop(p1), m);
}

/// The "in table body" rules.
pub proof fn lemma_in_table_body_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTableBody), p, t),
    ensures
        next_core(mode_in_table_body(env, p, t)),
{
    hide(insert_html_element);
    assert(rooted_mode(p.mode));
    assert(good(p));
    let f = |e: Elem|
        !(is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(e, Tag::Template) || is_html(
            e,
            Tag::Html,
        ));
    if t is Start && (t->Start_0.tag == Tag::Tr || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        lemma_pop_while_keeps(p, f);
        let p1 = clear_stack_back_to_table_body_context(p);
        assert(tag_of(name_tr()) == Tag::Tr) by (compute);
        if t->Start_0.tag == Tag::Tr {
            lemma_then_insert(p, p1, t->Start_0);
            lemma_to_mode(p, insert_html_element(p1, t->Start_0).0, Mode::InRow);
        } else {
            lemma_then_insert(p, p1, start_tag_named(name_tr()));
            let q1 = insert_html_element(p1, start_tag_named(name_tr())).0;
            lemma_to_mode(p, q1, Mode::InRow);
            lemma_reprocess_any(Parser { mode: Mode::InRow, ..q1 }, t);
        }
    } else if t is End && (t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead) {
        if has_same_name_in_table_scope(p, t->End_0) {
            let g = |e: Elem| e.ns == Namespace::Html && e.name == t->End_0.name;
            assert(!g(p.open[0])) by {
                assert(elem_tagged(p.open[0]));
            }
            let k = lemma_scope_k(p.open, g, Scope::Table);
            assert(elem_tagged(p.open[k]));
            lemma_clear_pop(p, f, k, Mode::InTable);
        }
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead)) || (t is End
        && t->End_0.tag == Tag::Table) {
        if has_table_section_in_table_scope(p) {
            let g = |e: Elem| is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot);
            let k = lemma_scope_k(p.open, g, Scope::Table);
            lemma_clear_pop(p, f, k, Mode::InTable);
            lemma_reprocess_any(Parser { mode: Mode::InTable, ..pop(pop_while(p, f)) }, t);
        }
    }
}

/// The "in row" rules.
pub proof fn lemma_in_row_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InRow), p, t),
    ensures
        next_core(mode_in_row(env, p, t)),
{
    hide(insert_html_element);
    hide(push_marker);
    assert(rooted_mode(p.mode));
    assert(good(p));
    let f = |e: Elem| !(is_html(e, Tag::Tr) || is_html(e, Tag::Template) || is_html(e, Tag::Html));
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        lemma_pop_while_keeps(p, f);
        let p1 = clear_stack_back_to_table_row_context(p);
        lemma_then_insert(p, p1, t->Start_0);
        let p2 = insert_html_element(p1, t->Start_0).0;
        let p3 = Parser { mode: Mode::InCell, ..p2 };
        lemma_keeps_live(p, p2);
        lemma_push_marker_keeps(p2);
        lemma_keeps_trans(p, p2, push_marker(p2));
        if !p2.stopped {
            reveal(insert_html_element);
            lemma_insert_html_keeps(p1, t->Start_0);
            let e = insert_html_element(p1, t->Start_0).1;
            assert(p2.open == p1.open.push(e));
            assert(push_marker(p2).open == p2.open) by {
                reveal(push_marker);
            }
            assert(cell_pred()(e));
            crate::exec::stack::lemma_last_index_where_found(p2.open, p2.open.len() as int, cell_pred(), p2.open.len() - 1);
        }
        lemma_to_mode(p, push_marker(p2), Mode::InCell);
        assert(push_marker(p3) == Parser { mode: Mode::InCell, ..push_marker(p2) }) by {
            reveal(push_marker);
        }
    } else if (t is End && t->End_0.tag == Tag::Tr) || (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag
        == Tag::Col || t->Start_0.tag == Tag::Colgroup || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot
        || t->Start_0.tag == Tag::Thead || t->Start_0.tag == Tag::Tr)) || (t is End && t->End_0.tag == Tag::Table) {
        if has_in_scope(p, Tag::Tr, Scope::Table) {
            let k = lemma_scope_k(p.open, |e: Elem| is_html(e, Tag::Tr), Scope::Table);
            lemma_clear_pop(p, f, k, Mode::InTableBody);
            lemma_reprocess_any(Parser { mode: Mode::InTableBody, ..pop(pop_while(p, f)) }, t);
        }
    } else if t is End && (t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead) {
        if has_same_name_in_table_scope(p, t->End_0) && has_in_scope(p, Tag::Tr, Scope::Table) {
            let k = lemma_scope_k(p.open, |e: Elem| is_html(e, Tag::Tr), Scope::Table);
            lemma_clear_pop(p, f, k, Mode::InTableBody);
            lemma_reprocess_any(Parser { mode: Mode::InTableBody, ..pop(pop_while(p, f)) }, t);
        }
    }
}

} // verus!
