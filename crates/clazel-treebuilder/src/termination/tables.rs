//! The edges of the "in table", "in table text", "in caption", "in column group", "in table body", "in row", "in cell", "in template" modes are ranked
//! (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The edges of the "in table" mode are ranked.
pub proof fn lemma_in_table_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTable), p),
    ensures
        edge_ok(Rules::Html(Mode::InTable), p, t, mode_in_table(env, p, t)),
{
}

/// The edges of the "in table text" mode are ranked.
pub proof fn lemma_in_table_text_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableText), p),
    ensures
        edge_ok(Rules::Html(Mode::InTableText), p, t, mode_in_table_text(env, p, t)),
{
}

/// The edges of the "in caption" mode are ranked.
pub proof fn lemma_in_caption_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InCaption), p),
    ensures
        edge_ok(Rules::Html(Mode::InCaption), p, t, mode_in_caption(env, p, t)),
{
}

/// The edges of the "in column group" mode are ranked.
pub proof fn lemma_in_column_group_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InColumnGroup), p),
    ensures
        edge_ok(Rules::Html(Mode::InColumnGroup), p, t, mode_in_column_group(env, p, t)),
{
}

/// The edges of the "in table body" mode are ranked.
pub proof fn lemma_in_table_body_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTableBody), p),
    ensures
        edge_ok(Rules::Html(Mode::InTableBody), p, t, mode_in_table_body(env, p, t)),
{
}

/// The edges of the "in row" mode are ranked.
pub proof fn lemma_in_row_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InRow), p),
    ensures
        edge_ok(Rules::Html(Mode::InRow), p, t, mode_in_row(env, p, t)),
{
}

/// The edges of the "in cell" mode are ranked.
pub proof fn lemma_in_cell_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InCell), p),
    ensures
        edge_ok(Rules::Html(Mode::InCell), p, t, mode_in_cell(env, p, t)),
{
}

/// The edges of the "in template" mode are ranked.
pub proof fn lemma_in_template_edges(env: EncFns, p: Parser, t: Tok)
    requires
        modes_ok(p),
        rules_ok(Rules::Html(Mode::InTemplate), p),
    ensures
        edge_ok(Rules::Html(Mode::InTemplate), p, t, mode_in_template(env, p, t)),
{
}

} // verus!
