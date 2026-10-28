//! The edges of the "in table", "in table text", "in caption", "in column group", "in table body", "in row", "in cell", "in template" modes are ranked
//! (see [`super`]).
//!
//! "Reset the insertion mode appropriately" reads the current template
//! insertion mode on reaching a `template` element (or a `template` context
//! element); [`modes_ok`]'s bound on [`template_count`] makes the stack of
//! template insertion modes non-empty there
//! ([`super::helpers_ranking::lemma_reset_from`]). The "in table text"
//! mode's "anything else" reprocesses each pending character with the "in
//! body" rules, whose reconstruction of the active formatting elements
//! pushes at most one element per entry of the list: the budget's
//! [`pending_growth`] pays for them
//! ([`super::helpers_ranking::lemma_reprocess_pending`]).

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
        let q = Parser { pending_table_text: seq![], original_mode: p.mode, mode: Mode::InTableText, ..p };
        assert(mode_in_table(env, p, t) == Outcome::Reprocess(q, t));
        super::helpers_ranking::lemma_modes_ok_from(p, q);
    } else if t is Comment || t is Pi || t is Doctype {
    } else if t is Start && t->Start_0.tag == Tag::Caption {
    } else if t is Start && t->Start_0.tag == Tag::Colgroup {
    } else if t is Start && t->Start_0.tag == Tag::Col {
        super::helpers_ranking::lemma_not_template(name_colgroup());
        lemma_in_table_insert_reprocess(p, t, start_tag_named(name_colgroup()), Mode::InColumnGroup);
    } else if t is Start && (t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead) {
    } else if t is Start && (t->Start_0.tag == Tag::Td || t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Tr) {
        super::helpers_ranking::lemma_not_template(name_tbody());
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
        tt.tag != Tag::Template,
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
    super::helpers_ranking::lemma_template_count_prefix(p, p1);
    super::helpers_ranking::lemma_insert_html_element(p1, tt);
    let q = Parser { mode: m, ..insert_html_element(p1, tt).0 };
    super::helpers_ranking::lemma_modes_ok_from(p, q);
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
    super::helpers_ranking::lemma_template_count_prefix(p, p1);
    assert(formatting_ok(p1));
    super::helpers_ranking::lemma_reset_modes_ok(p1);
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
    hide(insert_characters);
    if !(t is Char) {
        // 3. Anything else: reprocess in the original mode, G 5 to at most 4;
        // the pending characters push at most F elements each (`F × P` of
        // the budget), the stack of template modes is kept.
        assert(p.mode == Mode::InTableText);
        let pending = p.pending_table_text;
        super::helpers_tables::lemma_growth_le_4(p.original_mode, t);
        let p1 = if has_non_whitespace(pending) {
            reprocess_pending(env, p, pending, 0)
        } else if pending.len() == 0 {
            p
        } else {
            insert_characters(p, pending)
        };
        assert(p.formatting.len() * pending.len() >= 0) by (nonlinear_arith);
        if has_non_whitespace(pending) {
            super::helpers_ranking::lemma_reprocess_pending(env, p, pending, 0);
        } else if pending.len() != 0 {
            super::helpers_ranking::lemma_insert_characters_counts(p, pending);
        }
        assert(p1.open.len() <= p.open.len() + p.formatting.len() * pending.len());
        let q = Parser { mode: p1.original_mode, ..p1 };
        assert(mode_in_table_text(env, p, t) == Outcome::Reprocess(q, t));
        assert(template_count(q) <= template_count(p));
        super::helpers_ranking::lemma_modes_ok_from(p, q);
        assert(pending_growth(Rules::Html(Mode::InTableText), p, t) == p.formatting.len() * pending.len());
        assert(pending_growth(Rules::Html(q.mode), q, t) == 0);
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
        super::helpers_ranking::lemma_clear_to_last_marker(p2);
        super::helpers_ranking::lemma_template_count_prefix(p, p1);
        super::helpers_ranking::lemma_template_count_prefix(p1, p2);
        let p3 = clear_to_last_marker(p2);
        let q = Parser { mode: Mode::InTable, ..p3 };
        super::helpers_ranking::lemma_modes_ok_from(p, q);
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
        // 11. Pop the colgroup and reprocess in table: G kept, L lower (or
        // kept with the order 18 to 13).
        super::helpers_ranking::lemma_pop(p);
        let q = Parser { mode: Mode::InTable, ..pop(p) };
        super::helpers_ranking::lemma_modes_ok_from(p, q);
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
    if t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td) {
        lemma_in_table_body_cell(env, p, t);
    } else if (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead)) || (t is End
        && t->End_0.tag == Tag::Table) {
        lemma_in_table_body_section(env, p, t);
    } else {
        lemma_in_table_body_other(env, p, t);
    }
}

/// "in table body" case 2: insert a `tr` and reprocess in row: G 3 to 2.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_body_cell(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableBody), p),
        t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td),
    ensures
        edge_ok(Rules::Html(Mode::InTableBody), p, t, mode_in_table_body(env, p, t)),
{
    hide(insert_html_element);
    super::helpers_tables::lemma_pop_while_all(p);
    let p1 = clear_stack_back_to_table_body_context(p);
    super::helpers_ranking::lemma_template_count_prefix(p, p1);
    super::helpers_ranking::lemma_not_template(name_tr());
    super::helpers_ranking::lemma_insert_html_element(p1, start_tag_named(name_tr()));
    let q = Parser { mode: Mode::InRow, ..insert_html_element(p1, start_tag_named(name_tr())).0 };
    assert(mode_in_table_body(env, p, t) == Outcome::Reprocess(q, t));
    super::helpers_ranking::lemma_modes_ok_from(p, q);
}

/// "in table body" case 4: clear to the table section, pop it, reprocess in
/// table: G kept, L lower.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_body_section(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableBody), p),
        (t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead)) || (t is End
            && t->End_0.tag == Tag::Table),
    ensures
        edge_ok(Rules::Html(Mode::InTableBody), p, t, mode_in_table_body(env, p, t)),
{
    hide(insert_html_element);
    if has_table_section_in_table_scope(p) {
        super::helpers_tables::lemma_pop_while_all(p);
        let p1 = clear_stack_back_to_table_body_context(p);
        super::helpers_tables::lemma_scope_witness_all(p.open);
        let j = super::helpers_tables::scope_witness(
            p.open,
            p.open.len() as int,
            |e: Elem| is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot),
            Scope::Table,
        );
        assert(0 <= j < p.open.len());
        assert(p1.open.len() > j);
        super::helpers_ranking::lemma_template_count_prefix(p, p1);
        super::helpers_ranking::lemma_pop(p1);
        let q = Parser { mode: Mode::InTable, ..pop(p1) };
        assert(mode_in_table_body(env, p, t) == Outcome::Reprocess(q, t));
        super::helpers_ranking::lemma_modes_ok_from(p, q);
    }
}

/// The other "in table body" cases: handled, or using the "in table" rules.
#[verifier::spinoff_prover]
pub proof fn lemma_in_table_body_other(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableBody), p),
        !(t is Start && (t->Start_0.tag == Tag::Th || t->Start_0.tag == Tag::Td)),
        !((t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead)) || (t is End
            && t->End_0.tag == Tag::Table)),
    ensures
        edge_ok(Rules::Html(Mode::InTableBody), p, t, mode_in_table_body(env, p, t)),
{
    hide(insert_html_element);
    hide(clear_stack_back_to_table_body_context);
    hide(pop);
    let o = mode_in_table_body(env, p, t);
    assert(o is Done || o == Outcome::Using(Mode::InTable, p, t));
}

/// The edges of the "in row" mode are ranked.
pub proof fn lemma_in_row_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InRow), p),
    ensures
        edge_ok(Rules::Html(Mode::InRow), p, t, mode_in_row(env, p, t)),
{
    if ((t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
        || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
        == Tag::Tr)) || (t is End && t->End_0.tag == Tag::Table)) || (t is End && (t->End_0.tag == Tag::Tbody
        || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead)) {
        lemma_in_row_pop(env, p, t);
    } else {
        lemma_in_row_other(env, p, t);
    }
}

/// "in row" cases 3 and 4: clear to the `tr`, pop it, reprocess in table
/// body: G 1 to 0 or kept, L lower.
#[verifier::spinoff_prover]
pub proof fn lemma_in_row_pop(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InRow), p),
        ((t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
            == Tag::Tr)) || (t is End && t->End_0.tag == Tag::Table)) || (t is End && (t->End_0.tag == Tag::Tbody
            || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead)),
    ensures
        edge_ok(Rules::Html(Mode::InRow), p, t, mode_in_row(env, p, t)),
{
    hide(insert_html_element);
    hide(has_same_name_in_table_scope);
    if has_in_scope(p, Tag::Tr, Scope::Table) {
        super::helpers_tables::lemma_pop_while_all(p);
        let p1 = clear_stack_back_to_table_row_context(p);
        super::helpers_tables::lemma_scope_witness_all(p.open);
        let j = super::helpers_tables::scope_witness(p.open, p.open.len() as int, |e: Elem| is_html(e, Tag::Tr), Scope::Table);
        assert(0 <= j < p.open.len());
        assert(p1.open.len() > j);
        super::helpers_ranking::lemma_template_count_prefix(p, p1);
        super::helpers_ranking::lemma_pop(p1);
        let q = Parser { mode: Mode::InTableBody, ..pop(p1) };
        super::helpers_ranking::lemma_modes_ok_from(p, q);
        assert(mode_in_row(env, p, t) is Done || mode_in_row(env, p, t) == Outcome::Reprocess(q, t));
    }
}

/// The other "in row" cases: handled, or using the "in table" rules.
#[verifier::spinoff_prover]
pub proof fn lemma_in_row_other(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InRow), p),
        !(((t is Start && (t->Start_0.tag == Tag::Caption || t->Start_0.tag == Tag::Col || t->Start_0.tag == Tag::Colgroup
            || t->Start_0.tag == Tag::Tbody || t->Start_0.tag == Tag::Tfoot || t->Start_0.tag == Tag::Thead || t->Start_0.tag
            == Tag::Tr)) || (t is End && t->End_0.tag == Tag::Table)) || (t is End && (t->End_0.tag == Tag::Tbody
            || t->End_0.tag == Tag::Tfoot || t->End_0.tag == Tag::Thead))),
    ensures
        edge_ok(Rules::Html(Mode::InRow), p, t, mode_in_row(env, p, t)),
{
    hide(insert_html_element);
    hide(clear_stack_back_to_table_row_context);
    hide(pop);
    hide(push_marker);
    let o = mode_in_row(env, p, t);
    assert(o is Done || o == Outcome::Using(Mode::InTable, p, t));
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
    super::helpers_ranking::lemma_modes_ok_from(p, close_the_cell(p));
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
        lemma_in_template_switch(env, p, t);
    } else if t is End {
    } else if open_has_html(p, Tag::Template) {
        lemma_in_template_eof(env, p, t);
    }
}

/// "in template" cases 3 to 7: switch the current template insertion mode
/// (T kept, the stack of template modes non-empty by [`rules_ok`]), G
/// lower or kept with the order 19 to 15 or lower.
#[verifier::spinoff_prover]
pub proof fn lemma_in_template_switch(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTemplate), p),
        t is Start,
        !(t->Start_0.tag == Tag::Base || t->Start_0.tag == Tag::Basefont || t->Start_0.tag == Tag::Bgsound || t->Start_0.tag
            == Tag::Link || t->Start_0.tag == Tag::Meta || t->Start_0.tag == Tag::Noframes || t->Start_0.tag == Tag::Script
            || t->Start_0.tag == Tag::Style || t->Start_0.tag == Tag::Template || t->Start_0.tag == Tag::Title),
    ensures
        edge_ok(Rules::Html(Mode::InTemplate), p, t, mode_in_template(env, p, t)),
{
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
    let q = Parser { template_modes: s, mode: m, ..p };
    assert(s.len() == p.template_modes.len());
    assert forall|i: int| 0 <= i < s.len() implies template_mode_ok(#[trigger] s[i]) by {
        if i < s.len() - 1 {
            assert(s[i] == p.template_modes[i]);
        }
    }
    assert(template_count(q) == template_count(p));
    assert(formatting_ok(q));
    assert(modes_ok(q));
}

/// "in template" case 9, end of file with a `template` element on the
/// stack: pop to it (a `template` element fewer) and pop the template
/// insertion mode (T lower), then reset.
#[verifier::spinoff_prover]
pub proof fn lemma_in_template_eof(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTemplate), p),
        t is Eof,
        open_has_html(p, Tag::Template),
    ensures
        edge_ok(Rules::Html(Mode::InTemplate), p, t, mode_in_template(env, p, t)),
{
    assert(p.template_modes.len() > 0);
    let j = super::helpers_ranking::lemma_open_has_html(p, Tag::Template);
    super::helpers_ranking::lemma_pop_until_template(p, j);
    super::helpers_tables::lemma_pop_until_popped(p, Tag::Template);
    let p1 = pop_until_popped(p, Tag::Template);
    super::helpers_ranking::lemma_clear_to_last_marker(p1);
    let p2 = clear_to_last_marker(p1);
    let p3 = Parser { template_modes: p2.template_modes.drop_last(), ..p2 };
    let s = p3.template_modes;
    assert(s.len() == p.template_modes.len() - 1);
    assert forall|i: int| 0 <= i < s.len() implies template_mode_ok(#[trigger] s[i]) by {
        assert(s[i] == p.template_modes[i]);
    }
    assert(template_count(p3) + 1 <= template_count(p));
    assert(super::helpers_ranking::count_ok(p3));
    super::helpers_ranking::lemma_reset_modes_ok(p3);
    let q = reset_insertion_mode(p3);
    assert(mode_in_template(env, p, t) == Outcome::Reprocess(q, t));
    super::helpers_tables::lemma_growth_le_4(q.mode, t);
}

} // verus!
