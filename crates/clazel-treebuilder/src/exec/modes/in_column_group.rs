//! HTML §13.2.6.4.12 the "in column group" insertion mode
//! ([`mode_in_column_group`]) over [`ParserBuf`].

#[cfg(verus_only)]
use super::in_table::lemma_set_mode;
use super::in_table::{is_ascii_whitespace_exec, table_insert_and_pop_exec};
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::insert::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Pop the current node and switch the insertion mode to "in table" ("in
/// column group" cases 7 and 11).
fn pop_to_table_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == (Parser { mode: Mode::InTable, ..pop(old(p)@) }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(pop);
    pop_exec(p);
    proof {
        lemma_set_mode(p@, Mode::InTable);
    }
    p.mode = Mode::InTable;
}

/// §13.2.6.4.12 the "in column group" insertion mode
/// ([`mode_in_column_group`]).
pub fn mode_in_column_group_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        t@ is Start ==> tok_tagged(t@->Start_0),
        t@ is End ==> tok_tagged(t@->End_0),
    ensures
        outcome_view(o, final(p)@) == mode_in_column_group(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(insert_char);
    hide(insert_comment);
    hide(insert_pi);
    hide(insert_and_pop);
    hide(insert_html_element);
    hide(pop);
    match t {
        ExecTok::Char(c) => {
            if is_ascii_whitespace_exec(c) {
                // 1.
                insert_char_exec(p, c);
                return ExecOutcome::Done;
            }
        },
        ExecTok::Comment(data) => {
            // 2.
            insert_comment_exec(p, data, None);
            return ExecOutcome::Done;
        },
        ExecTok::Pi(target, data) => {
            // 3.
            insert_pi_exec(p, target, data, None);
            return ExecOutcome::Done;
        },
        ExecTok::Doctype { .. } => {
            // 4.
            return ExecOutcome::Done;
        },
        ExecTok::Start(tt) => {
            match tt.tag {
                Tag::Html => {
                    // 5.
                    return ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt));
                },
                Tag::Col => {
                    // 6.
                    proof {
                        reveal(insert_and_pop);
                    }
                    table_insert_and_pop_exec(p, &tt);
                    return ExecOutcome::Done;
                },
                Tag::Template => {
                    // 9.
                    return ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt));
                },
                _ => {
                    return in_column_group_else_exec(p, ExecTok::Start(tt));
                },
            }
        },
        ExecTok::End(tt) => {
            match tt.tag {
                Tag::Colgroup => {
                    // 7.
                    let cur = current_node_exec(p);
                    if is_html_exec(cur, &Tag::Colgroup) {
                        pop_to_table_exec(p);
                    }
                    return ExecOutcome::Done;
                },
                Tag::Col => {
                    // 8.
                    return ExecOutcome::Done;
                },
                Tag::Template => {
                    // 9.
                    return ExecOutcome::Using(Mode::InHead, ExecTok::End(tt));
                },
                _ => {
                    return in_column_group_else_exec(p, ExecTok::End(tt));
                },
            }
        },
        ExecTok::Eof => {
            // 10.
            return ExecOutcome::Using(Mode::InBody, ExecTok::Eof);
        },
    }
    // A character token that is not ASCII whitespace.
    proof {
        assert(t@ is Char);
    }
    in_column_group_else_exec(p, t)
}

/// "In column group" case 11, "Anything else".
fn in_column_group_else_exec(p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == (if !is_html(current_node(old(p)@), Tag::Colgroup) {
            Outcome::Done(old(p)@)
        } else {
            Outcome::Reprocess(Parser { mode: Mode::InTable, ..pop(old(p)@) }, t@)
        }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(pop);
    let cur = current_node_exec(p);
    if !is_html_exec(cur, &Tag::Colgroup) {
        ExecOutcome::Done
    } else {
        pop_to_table_exec(p);
        ExecOutcome::Reprocess(t)
    }
}

} // verus!
