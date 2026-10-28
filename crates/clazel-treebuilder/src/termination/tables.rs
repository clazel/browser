//! The edges of the "in table", "in table text", "in caption", "in column group", "in table body", "in row", "in cell", "in template" modes are ranked
//! (see [`super`]).
//!
//! Gaps (each is an `assert` marked `GAP` below, which fails: the edge is
//! not ranked from [`modes_ok`] and [`rules_ok`] alone):
//! - "in table" `table` start tag and "in template" end-of-file: "reset the
//!   insertion mode appropriately" returns `template_modes.last()` on
//!   reaching a template element (or a template context element), which is
//!   unspecified when the stack of template insertion modes is empty (it
//!   could be "text" or "in table text", breaking `modes_ok`, or "initial",
//!   whose growth budget 3 exceeds the token's 2). Needs the invariant
//!   [`super::helpers_tables::template_reset_ok`] (better: as many template insertion modes as
//!   template elements on the stack, counting a template context).
//! - "in template" cases 3 to 7 and end-of-file pop the stack of template
//!   insertion modes, whose length after `drop_last` is unspecified when it
//!   is empty. Needs "the mode (or rules) is "in template" ⇒ the stack of
//!   template insertion modes is not empty".
//! - "in table text" "anything else", when the pending characters are
//!   reprocessed with the "in body" rules: each reconstructs the active
//!   formatting elements, which pushes up to one element per entry of the
//!   list, so the stack can grow by more than the growth budget released (5
//!   to at most 4); the budget `B` increases. A ranking gap, not a table
//!   value (see the report).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "in table" mode are ranked.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTable), p),
    ensures
        edge_ok(Rules::Html(Mode::InTable), p, t, mode_in_table(env, p, t)),
{
    hide(in_table_anything_else);
    hide(clear_stack_back_to_table_context);
    hide(insert_html_element);
    hide(pop_until_popped);
    hide(reset_insertion_mode);
    hide(insert_comment);
    hide(insert_pi);
    hide(push_marker);
    hide(pop);
    hide(has_in_scope);
    hide(in_table_input_is_hidden);
    hide(parsing_template_contents);
    let cur = current_node(p);
    if t is Char && (is_html(cur, Tag::Table) || is_html(cur, Tag::Tbody) || is_html(cur, Tag::Template) || is_html(
        cur,
        Tag::Tfoot,
    ) || is_html(cur, Tag::Thead) || is_html(cur, Tag::Tr)) {
        // 1. In table text, original mode the current mode.
    } else if t is Comment || t is Pi || t is Doctype {
    } else if t is Start && t->Start_0.tag == Tag::Caption {
    } else if t is Start && t->Start_0.tag == Tag::Colgroup {
    } else if t is Start && t->Start_0.tag == Tag::Col {
        lemma_in_table_insert_reprocess(p, t, start_tag_named(name_colgroup()), Mode::InColumnGroup);
    } else if t is Start && (t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead) {
    } else if t is Start && (t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Tr) {
        lemma_in_table_insert_reprocess(p, t, start_tag_named(name_tbody()), Mode::InTableBody);
    } else if t is Start && t->Start_0.tag == Tag::Table {
        if has_in_scope(p, Tag::Table, Scope::Table) {
            lemma_in_table_table_start(p, t);
        }
    } else if t is End && t->End_0.tag == Tag::Table {
    } else if t is End && (t->End_0.tag == Tag::Body || t->End_0.tag == Tag::Caption || t->End_0.tag == Tag::Col
        || t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Html || t->End_0.tag == Tag::Tbody || t->End_0.tag
        == Tag::Td || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Th || t->End_0.tag == Tag::Thead
        || t->End_0.tag == Tag::Tr) {
    } else if (t is Start && (t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Script || t->Start_0.tag
        == Tag::Template)) || (t is End && t->End_0.tag == Tag::Template) {
        // 13. Using in head: order 13 to 11.
    } else if t is Start && t->Start_0.tag == Tag::Input && in_table_input_is_hidden(t->Start_0) {
    } else if t is Start && t->Start_0.tag == Tag::Form {
    } else if t is Eof {
        // 16. Using in body: order 13 to 12.
    } else {
        // 17. Anything else.
        assert(super::helpers_tables::in_table_else_tok(t));
        super::helpers_tables::lemma_in_table_anything_else_edges(env, p, t);
    }
}

/// "in table" cases 7 and 9: clear the stack back to a table context,
/// insert a `colgroup` or `tbody` and reprocess in "in column group" or
/// "in table body": G 1 to 0, 4 to 3, 1 to 0.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_insert_reprocess(p: Parser, t: Tok, tt: TagTok, m: Mode)
    requires
        modes_ok(p),
        (m == Mode::InColumnGroup && is_start(t, Tag::Col)) || (m == Mode::InTableBody && (is_start(t, Tag::Td) || is_start(
            t,
            Tag::Th,
        ) || is_start(t, Tag::Tr))),
    ensures
        edge_ok(
            Rules::Html(Mode::InTable),
            p,
            t,
            Outcome::Reprocess(Parser { mode: m, ..insert_html_element(clear_stack_back_to_table_context(p), tt).0 }, t),
        ),
{
    super::helpers_tables::lemma_pop_while_all(p);
    let p1 = clear_stack_back_to_table_context(p);
    super::helpers_tables::lemma_insert_html_element(p1, tt);
}

/// "in table" case 10 with a table in table scope: pop to the table (L
/// lower) and reset: G 2 to at most 2.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_table_start(p: Parser, t: Tok)
    requires
        modes_ok(p),
        is_start(t, Tag::Table),
        has_in_scope(p, Tag::Table, Scope::Table),
    ensures
        edge_ok(Rules::Html(Mode::InTable), p, t, Outcome::Reprocess(reset_insertion_mode(pop_until_popped(p, Tag::Table)), t)),
{
    assert(p.open.len() > 0);
    let p1 = pop_until_popped(p, Tag::Table);
    super::helpers_tables::lemma_pop_until_popped(p, Tag::Table);
    // GAP: reset with an empty stack of template insertion modes.
    assert(super::helpers_tables::template_reset_ok(p));
    super::helpers_tables::lemma_template_reset_ok_prefix(p, p1);
    super::helpers_tables::lemma_reset_from(p1, p1.open.len() - 1);
    let p2 = reset_insertion_mode(p1);
    super::helpers_tables::lemma_reset_mode_growth_table(p2.mode, t);
}

/// The edges of the "in table text" mode are ranked.
pub proof fn lemma_in_table_text_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableText), p),
    ensures
        edge_ok(Rules::Html(Mode::InTableText), p, t, mode_in_table_text(env, p, t)),
{
    hide(reprocess_pending);
    if !(t is Char) {
        // 3. Anything else: reprocess in the original mode, G 5 to at most 4.
        assert(p.mode == Mode::InTableText);
        let pending = p.pending_table_text;
        super::helpers_tables::lemma_growth_le_4(p.original_mode, t);
        if has_non_whitespace(pending) {
            // GAP: reprocessing the pending characters with the "in body"
            // rules reconstructs the active formatting elements, which can
            // push more elements than the growth budget releases.
            assert(edge_ok(Rules::Html(Mode::InTableText), p, t, mode_in_table_text(env, p, t)));
        } else if pending.len() != 0 {
            super::helpers_tables::lemma_insert_characters(p, pending);
        }
    }
}

/// The edges of the "in caption" mode are ranked.
pub proof fn lemma_in_caption_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InCaption), p),
    ensures
        edge_ok(Rules::Html(Mode::InCaption), p, t, mode_in_caption(env, p, t)),
{
    if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag
        == Tag::Th || t->Start_0.tag == Tag::Thead || t->Start_0.tag == Tag::Tr)) || (t is End && t->End_0.tag
        == Tag::Table) {
        // 2. Reprocess in table: G kept, L kept or lower, order 16 to 13.
        super::helpers_tables::lemma_pop_while_all(p);
        let p1 = generate_implied_end_tags(p, None);
        super::helpers_tables::lemma_pop_until_popped(p1, Tag::Caption);
        let p2 = pop_until_popped(p1, Tag::Caption);
        super::helpers_tables::lemma_clear_to_last_marker(p2);
    }
}

/// The edges of the "in column group" mode are ranked.
pub proof fn lemma_in_column_group_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InColumnGroup), p),
    ensures
        edge_ok(Rules::Html(Mode::InColumnGroup), p, t, mode_in_column_group(env, p, t)),
{
    if t is Char && is_ascii_whitespace(t->Char_0) {
    } else if t is Comment || t is Pi || t is Doctype {
    } else if t is Start && (t->Start_0.tag == Tag::Html || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Template) {
    } else if t is End && (t->End_0.tag == Tag::Colgroup || t->End_0.tag == Tag::Col || t->End_0.tag == Tag::Template) {
    } else if t is Eof {
    } else if is_html(current_node(p), Tag::Colgroup) {
        // 11. Pop the colgroup and reprocess in table: G kept, L lower.
        if p.open.len() > 0 {
            super::helpers_tables::lemma_pop(p);
        }
    }
}

/// The edges of the "in table body" mode are ranked.
pub proof fn lemma_in_table_body_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableBody), p),
    ensures
        edge_ok(Rules::Html(Mode::InTableBody), p, t, mode_in_table_body(env, p, t)),
{
    super::helpers_tables::lemma_pop_while_all(p);
    let p1 = clear_stack_back_to_table_body_context(p);
    if t is Start && t->Start_0.tag == Tag::Tr {
    } else if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        // 2. Insert a tr and reprocess in row: G 3 to 2.
        super::helpers_tables::lemma_insert_html_element(p1, start_tag_named(name_tr()));
    } else if t is End && (t->End_0.tag == Tag::Tbody || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead) {
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead)) || (t is End
        && t->End_0.tag == Tag::Table) {
        // 4. Clear to the table section, pop it, reprocess in table: G kept,
        // L lower.
        if has_table_section_in_table_scope(p) {
            super::helpers_tables::lemma_scope_witness_all(p.open);
            let j = super::helpers_tables::scope_witness(
                p.open,
                p.open.len() as int,
                |e: Elem| is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot),
                Scope::Table,
            );
            assert(0 <= j < p.open.len());
            assert(p1.open.len() > j);
            super::helpers_tables::lemma_pop(p1);
        }
    }
}

/// The edges of the "in row" mode are ranked.
pub proof fn lemma_in_row_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InRow), p),
    ensures
        edge_ok(Rules::Html(Mode::InRow), p, t, mode_in_row(env, p, t)),
{
    super::helpers_tables::lemma_pop_while_all(p);
    let p1 = clear_stack_back_to_table_row_context(p);
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
    } else if t is End && t->End_0.tag == Tag::Tr {
    } else if ((t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
        == Tag::Tr)) || (t is End && t->End_0.tag == Tag::Table)) || (t is End && (t->End_0.tag == Tag::Tbody
        || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead)) {
        // 3., 4. Clear to the tr, pop it, reprocess in table body: G 1 to 0
        // or kept, L lower.
        if has_in_scope(p, Tag::Tr, Scope::Table) {
            super::helpers_tables::lemma_scope_witness_all(p.open);
            let j = super::helpers_tables::scope_witness(p.open, p.open.len() as int, |e: Elem| is_html(e, Tag::Tr), Scope::Table);
            assert(0 <= j < p.open.len());
            assert(p1.open.len() > j);
            super::helpers_tables::lemma_pop(p1);
        }
    }
}

/// The edges of the "in cell" mode are ranked.
pub proof fn lemma_in_cell_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InCell), p),
    ensures
        edge_ok(Rules::Html(Mode::InCell), p, t, mode_in_cell(env, p, t)),
{
    // 2., 4. Close the cell and reprocess in row: G kept, L kept or lower,
    // order 17 to 15.
    super::helpers_tables::lemma_close_the_cell(p);
}

/// The edges of the "in template" mode are ranked.
pub proof fn lemma_in_template_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTemplate), p),
    ensures
        edge_ok(Rules::Html(Mode::InTemplate), p, t, mode_in_template(env, p, t)),
{
    if t is Char || t is Comment || t is Pi || t is Doctype {
    } else if (t is Start && (t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag
        == Tag::Bgsound || t->Start_0.tag == Tag::Link || t->Start_0.tag == Tag::Meta || t->Start_0.tag == Tag::Noframes
        || t->Start_0.tag == Tag::Script || t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Template
        || t->Start_0.tag == Tag::Title)) || (t is End && t->End_0.tag == Tag::Template) {
    } else if t is Start {
        // 3. to 7. Switch the current template insertion mode: T kept, G
        // lower or kept with the order 19 to 15 or lower.
        // GAP: an empty stack of template insertion modes.
        assert(p.template_modes.len() > 0);
        let m = if t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Colgroup || t->Start_0.tag == Tag::Tbody
            || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead {
            Mode::InTable
        } else if t->Start_0.tag == Tag::Col {
            Mode::InColumnGroup
        } else if t->Start_0.tag == Tag::Tr {
            Mode::InTableBody
        } else if t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Th {
            Mode::InRow
        } else {
            Mode::InBody
        };
        assert(mode_in_template(env, p, t) == in_template_switch(p, t, m));
        let s = p.template_modes.drop_last().push(m);
        assert(s.len() == p.template_modes.len());
        assert forall|i: int| 0 <= i < s.len() implies template_mode_ok(#[trigger] s[i]) by {
            if i < s.len() - 1 {
                assert(s[i] == p.template_modes[i]);
            }
        }
    } else if t is End {
    } else if open_has_html(p, Tag::Template) {
        // 9. End of file: pop to the template and pop the template insertion
        // mode (T lower), reset.
        assert(p.open.len() > 0);
        // GAP: an empty stack of template insertion modes.
        assert(p.template_modes.len() > 0);
        super::helpers_tables::lemma_pop_until_popped(p, Tag::Template);
        let p1 = pop_until_popped(p, Tag::Template);
        super::helpers_tables::lemma_clear_to_last_marker(p1);
        let p2 = clear_to_last_marker(p1);
        let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
        let s = p3.template_modes;
        assert(s.len() == p.template_modes.len() - 1);
        assert forall|i: int| 0 <= i < s.len() implies template_mode_ok(#[trigger] s[i]) by {
            assert(s[i] == p.template_modes[i]);
        }
        // GAP: reset with an empty stack of template insertion modes.
        assert(super::helpers_tables::template_reset_ok(p3));
        super::helpers_tables::lemma_reset_from(p3, p3.open.len() - 1);
        lemma_components_bounded(Rules::Html(reset_insertion_mode(p3).mode), t);
    }
}

} // verus!
