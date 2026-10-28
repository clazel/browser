//! HTML §13.2.6.4.13 the "in table body" insertion mode
//! ([`mode_in_table_body`]) and "clear the stack back to a table body
//! context" over [`ParserBuf`].

use super::in_table::start_tag_named_exec;
#[cfg(verus_only)]
use super::in_table::{lemma_pop_while_rooted, lemma_set_mode};
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::insert::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "clear the stack back to a table body context"
/// ([`clear_stack_back_to_table_body_context`]).
pub fn clear_stack_back_to_table_body_context_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == clear_stack_back_to_table_body_context(old(p)@),
        parser_inv(final(p)@),
        stack_rooted(final(p)@),
        final(p)@ == (Parser { open: final(p)@.open, ..old(p)@ }),
{
    let ghost f = |e: Elem|
        !(is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(e, Tag::Template)
            || is_html(e, Tag::Html));
    proof {
        lemma_pop_while_rooted(old(p)@, f);
    }
    pop_while_exec(p, &ElemPred::NotTableBodyContext, Ghost(f));
}

/// [`has_same_name_in_table_scope`].
pub fn has_same_name_in_table_scope_exec(p: &ParserBuf, tt: &ExecTagTok) -> (r: bool)
    ensures
        r == has_same_name_in_table_scope(p@, tt@),
{
    let ghost f = |e: Elem| e.ns == clazel_dom::spec::Namespace::Html && e.name == tt@.name;
    let pr = ElemPred::HtmlName(tt.name.as_slice());
    in_scope_exec(p, &pr, Ghost(f), &Scope::Table)
}

/// [`has_table_section_in_table_scope`].
pub fn has_table_section_in_table_scope_exec(p: &ParserBuf) -> (r: bool)
    ensures
        r == has_table_section_in_table_scope(p@),
{
    let ghost f = |e: Elem| is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot);
    in_scope_exec(p, &ElemPred::TableSection, Ghost(f), &Scope::Table)
}

/// "tr".
fn name_tr_exec() -> (r: Vec<u32>)
    ensures
        r@ == name_tr(),
{
    let s: &[u32] = &[0x74u32, 0x72];
    proof {
        assert(s@ =~= name_tr());
    }
    crate::exec::types::copy_str(s)
}

/// "Clear the stack back to a table body context", "insert an HTML element
/// for" `tt`, switch the insertion mode to "in row" ("in table body" cases
/// 1 and 2).
fn table_body_insert_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Template,
    ensures
        final(p)@ == (Parser {
            mode: Mode::InRow,
            ..insert_html_element(clear_stack_back_to_table_body_context(old(p)@), tt@).0
        }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_body_context);
    clear_stack_back_to_table_body_context_exec(p);
    let _ = insert_html_element_exec(p, tt);
    proof {
        lemma_set_mode(p@, Mode::InRow);
    }
    p.mode = Mode::InRow;
}

/// "Clear the stack back to a table body context", pop the current node,
/// switch the insertion mode to "in table" ("in table body" cases 3 and 4).
fn table_body_pop_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
    ensures
        final(p)@ == (Parser { mode: Mode::InTable, ..pop(clear_stack_back_to_table_body_context(old(p)@)) }),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(pop);
    hide(clear_stack_back_to_table_body_context);
    clear_stack_back_to_table_body_context_exec(p);
    pop_exec(p);
    proof {
        lemma_set_mode(p@, Mode::InTable);
    }
    p.mode = Mode::InTable;
}

/// §13.2.6.4.13 the "in table body" insertion mode ([`mode_in_table_body`]).
pub fn mode_in_table_body_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        t@ is Start ==> tok_tagged(t@->Start_0),
        t@ is End ==> tok_tagged(t@->End_0),
    ensures
        outcome_view(o, final(p)@) == mode_in_table_body(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(insert_html_element);
    hide(clear_stack_back_to_table_body_context);
    hide(pop);
    hide(has_same_name_in_table_scope);
    hide(has_table_section_in_table_scope);
    match t {
        ExecTok::Start(tt) => match tt.tag {
            Tag::Tr => {
                // 1.
                table_body_insert_exec(p, &tt);
                ExecOutcome::Done
            },
            Tag::Th | Tag::Td => {
                // 2.
                let tr = start_tag_named_exec(name_tr_exec());
                proof {
                    crate::termination::helpers_ranking::lemma_not_template(name_tr());
                }
                table_body_insert_exec(p, &tr);
                ExecOutcome::Reprocess(ExecTok::Start(tt))
            },
            Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Tbody | Tag::Tfoot | Tag::Thead => {
                // 4.
                if !has_table_section_in_table_scope_exec(p) {
                    ExecOutcome::Done
                } else {
                    table_body_pop_exec(p);
                    ExecOutcome::Reprocess(ExecTok::Start(tt))
                }
            },
            _ => {
                // 6.
                ExecOutcome::Using(Mode::InTable, ExecTok::Start(tt))
            },
        },
        ExecTok::End(tt) => match tt.tag {
            Tag::Tbody | Tag::Tfoot | Tag::Thead => {
                // 3.
                if has_same_name_in_table_scope_exec(p, &tt) {
                    table_body_pop_exec(p);
                }
                ExecOutcome::Done
            },
            Tag::Table => {
                // 4.
                if !has_table_section_in_table_scope_exec(p) {
                    ExecOutcome::Done
                } else {
                    table_body_pop_exec(p);
                    ExecOutcome::Reprocess(ExecTok::End(tt))
                }
            },
            Tag::Body | Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Html | Tag::Td | Tag::Th | Tag::Tr => {
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
