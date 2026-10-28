//! HTML §13.2.6.4.14 the "in row" insertion mode ([`mode_in_row`]) and
//! "clear the stack back to a table row context" over [`ParserBuf`].

#[cfg(verus_only)]
use super::in_table::{lemma_pop_while_rooted, lemma_set_mode};
use super::in_table_body::has_same_name_in_table_scope_exec;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
use crate::exec::insert::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "clear the stack back to a table row context"
/// ([`clear_stack_back_to_table_row_context`]).
pub fn clear_stack_back_to_table_row_context_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == clear_stack_back_to_table_row_context(old(p)@),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == (Parser { open: final(p)@.open, ..old(p)@ }),
{
    let ghost f = |e: Elem| !(is_html(e, Tag::Tr) || is_html(e, Tag::Template) || is_html(e, Tag::Html));
    proof {
        lemma_pop_while_rooted(old(p)@, f);
    }
    pop_while_exec(p, &ElemPred::NotRowContext, Ghost(f));
}

/// "Clear the stack back to a table row context", pop the current node,
/// switch the insertion mode to "in table body" ("in row" cases 2 to 4).
fn row_pop_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == (Parser { mode: Mode::InTableBody, ..pop(clear_stack_back_to_table_row_context(old(p)@)) }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(pop);
    hide(clear_stack_back_to_table_row_context);
    clear_stack_back_to_table_row_context_exec(p);
    pop_exec(p);
    proof {
        lemma_set_mode(p@, Mode::InTableBody);
    }
    p.mode = Mode::InTableBody;
}

/// "In row" case 1: clear the stack back to a table row context, insert
/// the cell, switch to "in cell", insert a marker.
fn row_cell_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag == Tag::Th || tt@.tag == Tag::Td,
    ensures
        final(p)@ == push_marker(
            Parser { mode: Mode::InCell, ..insert_html_element(clear_stack_back_to_table_row_context(old(p)@), tt@).0 },
        ),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_row_context);
    hide(push_marker);
    clear_stack_back_to_table_row_context_exec(p);
    let _ = insert_html_element_exec(p, tt);
    proof {
        lemma_set_mode(p@, Mode::InCell);
    }
    p.mode = Mode::InCell;
    push_marker_exec(p);
}

/// §13.2.6.4.14 the "in row" insertion mode ([`mode_in_row`]).
pub fn mode_in_row_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        t@ is Start ==> tok_tagged(t@->Start_0),
        t@ is End ==> tok_tagged(t@->End_0),
    ensures
        outcome_view(o, final(p)@) == mode_in_row(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_row_context);
    hide(pop);
    hide(push_marker);
    hide(has_in_scope);
    hide(has_same_name_in_table_scope);
    match t {
        ExecTok::Start(tt) => match tt.tag {
            Tag::Th | Tag::Td => {
                // 1.
                row_cell_exec(p, &tt);
                ExecOutcome::Done
            },
            Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Tbody | Tag::Tfoot | Tag::Thead | Tag::Tr => {
                // 3.
                if !has_in_scope_exec(p, Tag::Tr, &Scope::Table) {
                    ExecOutcome::Done
                } else {
                    row_pop_exec(p);
                    ExecOutcome::Reprocess(ExecTok::Start(tt))
                }
            },
            _ => {
                // 6.
                ExecOutcome::Using(Mode::InTable, ExecTok::Start(tt))
            },
        },
        ExecTok::End(tt) => match tt.tag {
            Tag::Tr => {
                // 2.
                if has_in_scope_exec(p, Tag::Tr, &Scope::Table) {
                    row_pop_exec(p);
                }
                ExecOutcome::Done
            },
            Tag::Table => {
                // 3.
                if !has_in_scope_exec(p, Tag::Tr, &Scope::Table) {
                    ExecOutcome::Done
                } else {
                    row_pop_exec(p);
                    ExecOutcome::Reprocess(ExecTok::End(tt))
                }
            },
            Tag::Tbody | Tag::Tfoot | Tag::Thead => {
                // 4. (Both failed tests ignore the token: the first is a
                // parse error, the second is not.)
                if !has_same_name_in_table_scope_exec(p, &tt) || !has_in_scope_exec(p, Tag::Tr, &Scope::Table) {
                    ExecOutcome::Done
                } else {
                    row_pop_exec(p);
                    ExecOutcome::Reprocess(ExecTok::End(tt))
                }
            },
            Tag::Body | Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Html | Tag::Td | Tag::Th => {
                // 5.
                ExecOutcome::Done
            },
            _ => {
                // 6.
                ExecOutcome::Using(Mode::InTable, ExecTok::End(tt))
            },
        },
        _ => {
            // 6.
            ExecOutcome::Using(Mode::InTable, t)
        },
    }
}

} // verus!
