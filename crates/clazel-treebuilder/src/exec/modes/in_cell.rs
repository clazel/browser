//! HTML §13.2.6.4.15 the "in cell" insertion mode ([`mode_in_cell`]) and
//! "close the cell" ([`close_the_cell`]) over [`ParserBuf`].

#[cfg(verus_only)]
use super::in_table::lemma_set_mode;
use super::in_table_body::has_same_name_in_table_scope_exec;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
use crate::exec::insert::*;
use crate::exec::names::copy_tag;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Pop elements from the stack of open elements until a td element or a th
/// element has been popped from the stack" ([`pop_until_cell_popped`]).
pub fn pop_until_cell_popped_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop_until_cell_popped(old(p)@),
        parser_inv(final(p)@),
{
    loop
        invariant
            parser_inv(p@),
            pop_until_cell_popped(p@) == pop_until_cell_popped(old(p)@),
        decreases p@.open.len(),
    {
        if p.open.is_empty() {
            return ;
        }
        let cur = current_node_exec(p);
        let hit = is_html_exec(cur, &Tag::Td) || is_html_exec(cur, &Tag::Th);
        pop_exec(p);
        if hit {
            return ;
        }
    }
}

/// "close the cell" ([`close_the_cell`]).
pub fn close_the_cell_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == close_the_cell(old(p)@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(generate_implied_end_tags);
    hide(pop_until_cell_popped);
    hide(clear_to_last_marker);
    // 1.
    generate_implied_end_tags_exec(p, None);
    // 2., 3.
    pop_until_cell_popped_exec(p);
    // 4.
    clear_to_last_marker_exec(p);
    // 5.
    proof {
        lemma_set_mode(p@, Mode::InRow);
    }
    p.mode = Mode::InRow;
}

/// "In cell" case 1 with the cell in table scope.
fn end_cell_exec(p: &mut ParserBuf, tag: Tag)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == (Parser {
            mode: Mode::InRow,
            ..clear_to_last_marker(pop_until_popped(generate_implied_end_tags(old(p)@, None), tag))
        }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    // 1.
    generate_implied_end_tags_exec(p, None);
    // 2., 3.
    pop_until_popped_exec(p, tag);
    // 4.
    clear_to_last_marker_exec(p);
    // 5.
    proof {
        lemma_set_mode(p@, Mode::InRow);
    }
    p.mode = Mode::InRow;
}

/// §13.2.6.4.15 the "in cell" insertion mode ([`mode_in_cell`]).
pub fn mode_in_cell_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_in_cell(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    hide(close_the_cell);
    hide(has_same_name_in_table_scope);
    match t {
        ExecTok::Start(tt) => match tt.tag {
            Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => {
                // 2.
                close_the_cell_exec(p);
                ExecOutcome::Reprocess(ExecTok::Start(tt))
            },
            _ => {
                // 5.
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            },
        },
        ExecTok::End(tt) => match tt.tag {
            Tag::Td | Tag::Th => {
                // 1.
                if has_same_name_in_table_scope_exec(p, &tt) {
                    end_cell_exec(p, copy_tag(&tt.tag));
                }
                ExecOutcome::Done
            },
            Tag::Body | Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Html => {
                // 3.
                ExecOutcome::Done
            },
            Tag::Table | Tag::Tbody | Tag::Tfoot | Tag::Thead | Tag::Tr => {
                // 4.
                if !has_same_name_in_table_scope_exec(p, &tt) {
                    ExecOutcome::Done
                } else {
                    close_the_cell_exec(p);
                    ExecOutcome::Reprocess(ExecTok::End(tt))
                }
            },
            _ => {
                // 5.
                ExecOutcome::Using(Mode::InBody, ExecTok::End(tt))
            },
        },
        _ => {
            // 5.
            ExecOutcome::Using(Mode::InBody, t)
        },
    }
}

} // verus!
