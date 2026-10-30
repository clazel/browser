//! The rules of "in cell", "in template", "after body", the frameset modes,
//! the "after after" modes and foreign content keep the reachable-state
//! facts ([`next_core`], see [`super`]).

#[cfg(verus_only)]
use super::body::*;
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
#[cfg(verus_only)]
use super::tables::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// "in cell"

/// [`pop_until_cell_popped`] is a [`crate::exec::stack::pop_until_where`].
pub proof fn lemma_pop_until_cell_is(p: Parser)
    ensures
        pop_until_cell_popped(p) == crate::exec::stack::pop_until_where(p, cell_pred()),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !(is_html(current_node(p), Tag::Td) || is_html(current_node(p), Tag::Th)) {
        lemma_pop_until_cell_is(pop(p));
    }
}

/// "Close the cell", with a cell on the stack (proven on the parser put in
/// the "in row" mode, the mode it ends in: it pops the cell).
pub proof fn lemma_close_the_cell(p: Parser)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        has_cell(p.open),
    ensures
        next_core(Outcome::Reprocess(close_the_cell(p), Tok::Eof)),
{
    let p0 = mode_as(p, Mode::InRow);
    assert(good(p0));
    let k = lemma_has_k(p0.open, cell_pred());
    let q = generate_implied_end_tags(p0, None);
    lemma_pop_until_cell_is(q);
    lemma_close_keeps(p0, None, cell_pred(), k);
    let q2 = pop_until_cell_popped(q);
    lemma_keeps_live(p0, q2);
    lemma_clear_keeps(q2);
    lemma_keeps_trans(p0, q2, clear_to_last_marker(q2));
    lemma_to_mode(p0, clear_to_last_marker(q2), Mode::InRow);
    let fi = crate::exec::modes::in_body_start_lemmas::implied_pred(None);
    let r = generate_implied_end_tags(p, None);
    assert(r == pop_while(p, fi));
    assert(q == pop_while(p0, fi));
    lemma_pop_while_mode(p, fi, Mode::InRow);
    lemma_pop_until_cell_is(r);
    lemma_pop_until_where_mode(r, cell_pred(), Mode::InRow);
    lemma_clear_mode(pop_until_cell_popped(r), Mode::InRow);
}

/// The "in cell" `td` and `th` end tags with the token's element in table
/// scope (proven on the parser put in the "in row" mode, the mode they end
/// in: they pop the cell).
pub proof fn lemma_cell_end_cell(p: Parser, tt: TagTok)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        tok_tagged(tt),
        crate::independent::equivalence_body::attrs_plain(tt.attrs),
        tt.tag == Tag::Td || tt.tag == Tag::Th,
        has_same_name_in_table_scope(p, tt),
    ensures
        next_core(
            Outcome::Done(
                Parser {
                    mode: Mode::InRow,
                    ..clear_to_last_marker(pop_until_popped(generate_implied_end_tags(p, None), tt.tag))
                },
            ),
        ),
{
    let p0 = mode_as(p, Mode::InRow);
    assert(good(p0));
    let g = |e: Elem| e.ns == Namespace::Html && e.name == tt.name;
    assert(!g(p0.open[0])) by {
        assert(elem_tagged(p0.open[0]));
    }
    assert(has_same_name_in_table_scope(p0, tt));
    let k = lemma_scope_k(p0.open, g, Scope::Table);
    assert(elem_tagged(p0.open[k]));
    let f = |e: Elem| is_html(e, tt.tag);
    let q = generate_implied_end_tags(p0, None);
    crate::exec::stack::lemma_pop_until_popped(q, tt.tag);
    lemma_close_keeps(p0, None, f, k);
    let q2 = pop_until_popped(q, tt.tag);
    lemma_keeps_live(p0, q2);
    lemma_clear_keeps(q2);
    lemma_keeps_trans(p0, q2, clear_to_last_marker(q2));
    lemma_to_mode(p0, clear_to_last_marker(q2), Mode::InRow);
    let fi = crate::exec::modes::in_body_start_lemmas::implied_pred(None);
    let r = generate_implied_end_tags(p, None);
    assert(r == pop_while(p, fi));
    assert(q == pop_while(p0, fi));
    lemma_pop_while_mode(p, fi, Mode::InRow);
    crate::exec::stack::lemma_pop_until_popped(r, tt.tag);
    lemma_pop_until_where_mode(r, f, Mode::InRow);
    lemma_clear_mode(pop_until_popped(r, tt.tag), Mode::InRow);
}

/// The "in cell" rules.
pub proof fn lemma_in_cell_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InCell), p, t),
    ensures
        next_core(mode_in_cell(env, p, t)),
{
    hide(close_the_cell);
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    assert(p.mode == Mode::InCell);
    assert(good(p));
    if t is End && (t->End_0.tag == Tag::Td || t->End_0.tag == Tag::Th) {
        let tt = t->End_0;
        if has_same_name_in_table_scope(p, tt) {
            lemma_cell_end_cell(p, tt);
        }
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag
        == Tag::Th || t->Start_0.tag == Tag::Thead || t->Start_0.tag == Tag::Tr)) || (t is End && (t->End_0.tag == Tag::Table
        || t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead || t->End_0.tag
        == Tag::Tr)) {
        reveal(close_the_cell);
        reveal(generate_implied_end_tags);
        reveal(clear_to_last_marker);
        lemma_close_the_cell(p);
        lemma_reprocess_any(close_the_cell(p), t);
    }
}

// ---------------------------------------------------------------------
// "in template"

/// The "in template" end-of-file token with a `template` on the stack
/// (proven on the parser put in the "in body" mode: in the "in cell" mode
/// it pops the cell, and the mode is reset).
pub proof fn lemma_in_template_eof(p: Parser)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        open_has_html(p, Tag::Template),
    ensures
        ({
            let p1 = pop_until_popped(p, Tag::Template);
            let p2 = clear_to_last_marker(p1);
            let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
            next_core(Outcome::Reprocess(reset_insertion_mode(p3), Tok::Eof))
        }),
{
    let p0 = mode_as(p, Mode::InBody);
    assert(good(p0));
    lemma_in_template_eof0(p0);
    let f = |e: Elem| is_html(e, Tag::Template);
    crate::exec::stack::lemma_pop_until_popped(p, Tag::Template);
    crate::exec::stack::lemma_pop_until_popped(p0, Tag::Template);
    lemma_pop_until_where_mode(p, f, Mode::InBody);
    let p1 = pop_until_popped(p, Tag::Template);
    lemma_clear_mode(p1, Mode::InBody);
    let p2 = clear_to_last_marker(p1);
    let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
    assert(Parser { template_modes: p2.template_modes.drop_last(), ..mode_as(p2, Mode::InBody) } == mode_as(p3, Mode::InBody));
    lemma_reset_from_mode(p3, Mode::InBody, p3.open.len() - 1);
    assert(reset_insertion_mode(mode_as(p3, Mode::InBody)) == reset_insertion_mode(p3));
}

/// [`lemma_in_template_eof`] outside the "in cell" mode.
pub proof fn lemma_in_template_eof0(p: Parser)
    requires
        good(p),
        !p.stopped,
        modes_ok(p),
        open_has_html(p, Tag::Template),
        p.mode != Mode::InCell,
    ensures
        ({
            let p1 = pop_until_popped(p, Tag::Template);
            let p2 = clear_to_last_marker(p1);
            let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
            next_core(Outcome::Reprocess(reset_insertion_mode(p3), Tok::Eof))
        }),
{
    let j = crate::termination::helpers_ranking::lemma_open_has_html(p, Tag::Template);
    assert(j >= 1);
    let p1 = pop_until_popped(p, Tag::Template);
    lemma_pop_until_popped_keeps(p, Tag::Template, j);
    crate::termination::helpers_ranking::lemma_pop_until_template(p, j);
    let p2 = clear_to_last_marker(p1);
    lemma_keeps_live(p, p1);
    lemma_clear_keeps(p1);
    lemma_keeps_trans(p, p1, p2);
    let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
    if !p3.stopped {
        crate::termination::helpers_ranking::lemma_template_count(p);
        crate::termination::helpers_ranking::lemma_template_count(p1);
        crate::termination::helpers_ranking::lemma_template_count(p3);
        assert(p.template_modes.len() > 0);
        assert forall|i: int| 0 <= i < p3.template_modes.len() implies crate::termination::template_mode_ok(
            #[trigger] p3.template_modes[i],
        ) by {
            assert(p3.template_modes[i] == p.template_modes[i]);
        }
        assert(crate::termination::helpers_ranking::count_ok(p3));
        assert(good(p3));
        lemma_reset_keeps(p3);
    }
}

/// The "in template" rules.
pub proof fn lemma_in_template_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InTemplate), p, t),
    ensures
        next_core(mode_in_template(env, p, t)),
{
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    hide(reset_insertion_mode);
    assert(rooted_mode(p.mode));
    assert(good(p));
    if t is Eof && open_has_html(p, Tag::Template) {
        lemma_in_template_eof(p);
    }
}

// ---------------------------------------------------------------------
// "after body", the frameset modes, the "after after" modes

/// Insert a character, comment or processing instruction, keeping the
/// stack.
pub proof fn lemma_insert_tok(p: Parser, t: Tok, loc: Option<Location>)
    requires
        reach_core(p),
        modes_ok(p),
        good(p),
        !p.stopped,
        loc is None || loc == Some(document_location()) || loc == Some(Location { parent: p.open[0].id, child: None }),
    ensures
        t is Char ==> next_core(Outcome::Done(insert_char(p, t->Char_0))),
        t is Comment ==> next_core(Outcome::Done(insert_comment(p, t->Comment_0, loc))),
        t is Pi ==> next_core(Outcome::Done(insert_pi(p, t->Pi_0, t->Pi_1, loc))),
{
    super::doc::lemma_dinv_at(p, 0);
    super::doc::lemma_document_pok(p.doc);
    assert(loc_pok(p, loc));
    if t is Char {
        lemma_insert_char_keeps(p, t->Char_0);
        let q = insert_char(p, t->Char_0);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, loc);
        let q = insert_comment(p, t->Comment_0, loc);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, loc);
        let q = insert_pi(p, t->Pi_0, t->Pi_1, loc);
        if !q.stopped {
            lemma_core_frame(p, q);
        }
    }
}

/// The "after body" rules.
pub proof fn lemma_after_body_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::AfterBody), p, t),
    ensures
        next_core(mode_after_body(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    assert(p.mode == Mode::AfterBody);
    assert(good(p));
    lemma_insert_tok(p, t, Some(Location { parent: p.open[0].id, child: None }));
    lemma_keeps_refl(p);
    lemma_to_mode(p, p, Mode::AfterAfterBody);
    lemma_to_mode(p, p, Mode::InBody);
    lemma_reprocess_any(Parser { mode: Mode::InBody, ..p }, t);
}

/// The "in frameset" rules.
pub proof fn lemma_in_frameset_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::InFrameset), p, t),
    ensures
        next_core(mode_in_frameset(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_html_element);
    assert(p.mode == Mode::InFrameset);
    assert(good(p));
    lemma_insert_tok(p, t, None);
    lemma_keeps_refl(p);
    if t is Start && (t->Start_0.tag == Tag::Frameset || t->Start_0.tag == Tag::Frame) {
        lemma_then_insert(p, p, t->Start_0);
        let p1 = insert_html_element(p, t->Start_0).0;
        lemma_ib_done(p, p1);
        if !p1.stopped {
            reveal(insert_html_element);
            lemma_insert_html_keeps(p, t->Start_0);
            lemma_pop_keeps(p1);
            lemma_keeps_trans(p, p1, pop(p1));
            lemma_ib_done(p, pop(p1));
        }
    } else if t is End && t->End_0.tag == Tag::Frameset && p.open.len() > 1 {
        lemma_pop_keeps(p);
        lemma_ib_done(p, pop(p));
        lemma_to_mode(p, pop(p), Mode::AfterFrameset);
    }
}

/// The "after frameset" rules.
pub proof fn lemma_after_frameset_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::AfterFrameset), p, t),
    ensures
        next_core(mode_after_frameset(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    assert(p.mode == Mode::AfterFrameset);
    assert(good(p));
    lemma_insert_tok(p, t, None);
    lemma_keeps_refl(p);
    lemma_to_mode(p, p, Mode::AfterAfterFrameset);
}

/// The "after after body" rules.
pub proof fn lemma_after_after_body_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::AfterAfterBody), p, t),
    ensures
        next_core(mode_after_after_body(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    assert(p.mode == Mode::AfterAfterBody);
    assert(good(p));
    lemma_insert_tok(p, t, Some(document_location()));
    lemma_keeps_refl(p);
    lemma_to_mode(p, p, Mode::InBody);
    lemma_reprocess_any(Parser { mode: Mode::InBody, ..p }, t);
}

/// The "after after frameset" rules.
pub proof fn lemma_after_after_frameset_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Html(Mode::AfterAfterFrameset), p, t),
    ensures
        next_core(mode_after_after_frameset(env, p, t)),
{
    hide(insert_comment);
    hide(insert_pi);
    assert(p.mode == Mode::AfterAfterFrameset);
    assert(good(p));
    lemma_insert_tok(p, t, Some(document_location()));
}

// ---------------------------------------------------------------------
// Foreign content

/// `q` keeps every HTML element of `p`'s stack where it was.
pub open spec fn html_kept(p: Parser, q: Parser) -> bool {
    forall|h: int| 0 <= h < p.open.len() && (#[trigger] p.open[h]).ns == Namespace::Html ==> q.open.len() > h && q.open[h]
        == p.open[h]
}

/// [`html_above`] survives [`html_kept`].
pub proof fn lemma_html_above_kept(p: Parser, q: Parser)
    requires
        html_kept(p, q),
        html_above(p.open),
    ensures
        html_above(q.open),
{
    let h = last_index_where(p.open, p.open.len() as int, html_ns());
    crate::termination::helpers_ranking::lemma_last_index_where(p.open, p.open.len() as int, html_ns());
    assert(q.open[h] == p.open[h]);
    crate::exec::stack::lemma_last_index_where_found(q.open, q.open.len() as int, html_ns(), h);
}

/// Foreign content's end tag loop from entry `i`, with every entry from `i`
/// up not HTML.
pub proof fn lemma_foreign_loop(p: Parser, t: Tok, i: int)
    requires
        good(p),
        !p.stopped,
        0 <= i < p.open.len(),
        forall|j: int| i <= j < p.open.len() ==> (#[trigger] p.open[j]).ns != Namespace::Html,
    ensures
        match foreign_end_tag_loop(p, t, i) {
            Outcome::Done(q) => keeps(p, q) && html_kept(p, q) && q == (Parser { open: q.open, ..p }),
            Outcome::Reprocess(q, t2) => q == p && t2 == t,
            Outcome::Using(_, _, _) => false,
        },
    decreases i,
{
    if i <= 0 {
        lemma_keeps_refl(p);
    } else if ascii_lowercase(p.open[i].name) == t->End_0.name {
        let f = |e: Elem| e.id == p.open[i].id;
        crate::exec::stack::lemma_pop_until_node_popped(p, p.open[i].id);
        crate::exec::modes::in_body_start_lemmas::lemma_pop_until_where_prefix(p, f);
        crate::exec::stack::lemma_last_index_where_found(p.open, p.open.len() as int, f, i);
        lemma_cell_top(p.open);
        if in_cell(p) {
            assert(p.open[last_cell(p.open)].ns == Namespace::Html);
        }
        lemma_pop_until_node_popped_keeps(p, p.open[i].id, i);
        let q = pop_until_node_popped(p, p.open[i].id);
        assert forall|h: int| 0 <= h < p.open.len() && (#[trigger] p.open[h]).ns == Namespace::Html implies q.open.len() > h
            && q.open[h] == p.open[h] by {
            assert(h < i);
        }
    } else if p.open[i - 1].ns != Namespace::Html {
        lemma_foreign_loop(p, t, i - 1);
    } else {
        lemma_keeps_refl(p);
    }
}

/// The parser of foreign content's outcome keeps the stack's HTML elements.
pub open spec fn foreign_ok(p: Parser, o: Outcome) -> bool {
    match o {
        Outcome::Done(q) => keeps(p, q) && (!q.stopped ==> html_kept(p, q)),
        Outcome::Reprocess(q, t2) => keeps(p, q) && (!q.stopped ==> html_kept(p, q)),
        Outcome::Using(_, _, _) => false,
    }
}

/// Foreign content: characters, comments, processing instructions, DOCTYPEs.
pub proof fn lemma_foreign_ok_text(env: EncFns, p: Parser, t: Tok)
    requires
        good(p),
        !p.stopped,
        in_foreign_content(p),
        crate::exec::modes::initial::tok_ok(t),
        t is Char || t is Comment || t is Pi || t is Doctype,
    ensures
        foreign_ok(p, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(foreign_end_tag_loop);
    hide(adjust_foreign_start_tag);
    hide(svg_script_end);
    if t is Char {
        let c = if t->Char_0 == 0 {
            0xFFFDu32
        } else {
            t->Char_0
        };
        lemma_insert_char_keeps(p, c);
    } else if t is Comment {
        lemma_insert_comment_keeps(p, t->Comment_0, None);
    } else if t is Pi {
        lemma_insert_pi_keeps(p, t->Pi_0, t->Pi_1, None);
    } else {
        lemma_keeps_refl(p);
    }
}

/// Foreign content: the breakout tags.
pub proof fn lemma_foreign_ok_breakout(env: EncFns, p: Parser, t: Tok)
    requires
        good(p),
        !p.stopped,
        in_foreign_content(p),
        crate::exec::modes::initial::tok_ok(t),
        is_foreign_breakout(t) && !(t is Char || t is Comment || t is Pi || t is Doctype),
    ensures
        foreign_ok(p, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(foreign_end_tag_loop);
    hide(adjust_foreign_start_tag);
    hide(svg_script_end);
    let f = |e: Elem|
        !(is_mathml_text_integration_point(e) || is_html_integration_point(e) || e.ns == Namespace::Html);
    lemma_cell_top(p.open);
    lemma_pop_while_keeps(p, f);
    crate::termination::helpers_tables::lemma_pop_while(p, f);
}

/// Foreign content: the other start tags.
pub proof fn lemma_foreign_ok_start(env: EncFns, p: Parser, t: Tok)
    requires
        good(p),
        !p.stopped,
        in_foreign_content(p),
        crate::exec::modes::initial::tok_ok(t),
        t is Start && !is_foreign_breakout(t),
    ensures
        foreign_ok(p, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(foreign_end_tag_loop);
    hide(adjust_foreign_start_tag);
    hide(svg_script_end);
    let a = adjusted_current_node(p);
    let tt = adjust_foreign_start_tag(a, t->Start_0);
    assert(tok_tagged(tt)) by {
        reveal(adjust_foreign_start_tag);
    }
    lemma_insert_foreign_keeps(p, tt, a.ns);
    let (p1, e) = insert_foreign_element(p, tt, a.ns);
    if !p1.stopped && tt.self_closing {
        lemma_pop_keeps(p1);
        lemma_keeps_trans(p, p1, pop(p1));
        assert(svg_script_end(p1) == pop(p1)) by {
            reveal(svg_script_end);
        }
    }
}

/// Foreign content: the end tags.
pub proof fn lemma_foreign_ok_end(env: EncFns, p: Parser, t: Tok)
    requires
        good(p),
        !p.stopped,
        in_foreign_content(p),
        crate::exec::modes::initial::tok_ok(t),
        t is End && !is_foreign_breakout(t),
    ensures
        foreign_ok(p, foreign_content(env, p, t)),
{
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_foreign_element);
    hide(foreign_end_tag_loop);
    hide(adjust_foreign_start_tag);
    hide(svg_script_end);
    if t->End_0.tag == Tag::Script && p.open.len() > 0 && is_svg(current_node(p), Tag::Script) {
        lemma_pop_keeps(p);
        assert(svg_script_end(p) == pop(p)) by {
            reveal(svg_script_end);
        }
    } else if p.open.len() >= 2 {
        assert(p.open[p.open.len() - 1].ns != Namespace::Html);
        lemma_foreign_loop(p, t, p.open.len() - 1);
        lemma_keeps_refl(p);
    } else {
        assert(foreign_end_tag_loop(p, t, p.open.len() - 1) == Outcome::Reprocess(p, t) || foreign_end_tag_loop(
            p,
            t,
            p.open.len() - 1,
        ) == Outcome::Done(p)) by {
            reveal(foreign_end_tag_loop);
        }
        lemma_keeps_refl(p);
    }
}

/// Foreign content keeps [`good`] and every HTML element of the stack.
pub proof fn lemma_foreign_ok(env: EncFns, p: Parser, t: Tok)
    requires
        good(p),
        !p.stopped,
        in_foreign_content(p),
        crate::exec::modes::initial::tok_ok(t),
    ensures
        foreign_ok(p, foreign_content(env, p, t)),
{
    hide(foreign_content);
    if t is Char || t is Comment || t is Pi || t is Doctype {
        lemma_foreign_ok_text(env, p, t);
    } else if is_foreign_breakout(t) {
        lemma_foreign_ok_breakout(env, p, t);
    } else if t is Start {
        lemma_foreign_ok_start(env, p, t);
    } else if t is End {
        lemma_foreign_ok_end(env, p, t);
    } else {
        assert(foreign_content(env, p, t) == Outcome::Done(p)) by {
            reveal(foreign_content);
        }
        lemma_keeps_refl(p);
    }
}

/// The rules for parsing tokens in foreign content.
pub proof fn lemma_foreign_reach(env: EncFns, p: Parser, t: Tok)
    requires
        rules_inv(Rules::Foreign, p, t),
    ensures
        next_core(foreign_content(env, p, t)),
{
    hide(foreign_content);
    assert(p.mode != Mode::Initial && p.mode != Mode::BeforeHtml);
    assert(p.mode != Mode::InHeadNoscript && p.mode != Mode::Text && p.mode != Mode::InTableText) by {
        if p.mode == Mode::InHeadNoscript || p.mode == Mode::Text || p.mode == Mode::InTableText {
            assert(adjusted_current_node(p) == current_node(p));
        }
    }
    assert(good(p));
    lemma_foreign_ok(env, p, t);
    let o = foreign_content(env, p, t);
    let q = match o {
        Outcome::Done(q) => q,
        Outcome::Reprocess(q, _) => q,
        Outcome::Using(_, q, _) => q,
    };
    if !q.stopped {
        if p.mode == Mode::InHead {
            lemma_html_above_kept(p, q);
        }
        crate::termination::helpers_ranking::lemma_modes_ok_from(p, q);
        assert(reach_core(q));
    }
}

} // verus!
