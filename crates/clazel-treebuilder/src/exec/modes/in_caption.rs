//! HTML §13.2.6.4.11 the "in caption" insertion mode ([`mode_in_caption`])
//! over [`ParserBuf`].

#[cfg(verus_only)]
use super::in_table::lemma_set_mode;
#[allow(unused_imports)]
use super::spec::*;
use crate::exec::formatting::*;
use crate::exec::insert::*;
use crate::exec::stack::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "In caption" cases 1 and 2, with a caption in table scope: generate
/// implied end tags, pop until a caption has been popped, clear the list
/// of active formatting elements up to the last marker, switch to "in
/// table".
fn close_caption_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == (Parser {
            mode: Mode::InTable,
            ..clear_to_last_marker(pop_until_popped(generate_implied_end_tags(old(p)@, None), Tag::Caption))
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
    pop_until_popped_exec(p, Tag::Caption);
    // 4.
    clear_to_last_marker_exec(p);
    // 5.
    proof {
        lemma_set_mode(p@, Mode::InTable);
    }
    p.mode = Mode::InTable;
}

/// §13.2.6.4.11 the "in caption" insertion mode ([`mode_in_caption`]).
pub fn mode_in_caption_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_in_caption(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    hide(generate_implied_end_tags);
    hide(pop_until_popped);
    hide(clear_to_last_marker);
    hide(has_in_scope);
    let (start, end) = match &t {
        ExecTok::Start(tt) => (
            matches!(
                tt.tag,
                Tag::Caption | Tag::Col | Tag::Colgroup | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr
            ),
            false,
        ),
        ExecTok::End(tt) => (matches!(tt.tag, Tag::Table), matches!(tt.tag, Tag::Caption)),
        _ => (false, false),
    };
    if end {
        // 1.
        if has_in_scope_exec(p, Tag::Caption, &Scope::Table) {
            close_caption_exec(p);
        }
        return ExecOutcome::Done;
    }
    if start {
        // 2.
        if !has_in_scope_exec(p, Tag::Caption, &Scope::Table) {
            return ExecOutcome::Done;
        }
        close_caption_exec(p);
        // 6.
        return ExecOutcome::Reprocess(t);
    }
    let ignored = match &t {
        ExecTok::End(tt) => matches!(
            tt.tag,
            Tag::Body | Tag::Col | Tag::Colgroup | Tag::Html | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead
                | Tag::Tr
        ),
        _ => false,
    };
    if ignored {
        // 3.
        ExecOutcome::Done
    } else {
        // 4.
        ExecOutcome::Using(Mode::InBody, t)
    }
}

} // verus!
