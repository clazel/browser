//! HTML §13.2.6.4.8 the "text" insertion mode ([`mode_text`]) over
//! [`ParserBuf`].

use super::super::insert::*;
use super::super::stack::*;
use super::super::types::*;
#[cfg(verus_only)]
use super::initial::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.8 the "text" insertion mode ([`mode_text`]). Its rules are
/// only applied in the "text" mode (`termination::rules_ok`).
pub fn mode_text_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.mode == Mode::Text,
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_text(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(text_script_end);
    hide(parser_inv);
    match t {
        ExecTok::Char(c) => {
            // 1.
            insert_char_exec(p, c);
            ExecOutcome::Done
        },
        ExecTok::Eof => {
            // 2.
            pop_to_original_mode(p);
            ExecOutcome::Reprocess(ExecTok::Eof)
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Script) {
                // 3.
                text_script_end_exec(p);
            } else {
                // 4.
                pop_to_original_mode(p);
            }
            ExecOutcome::Done
        },
        _ => ExecOutcome::Done,
    }
}

/// "Pop the current node off the stack of open elements" and "switch the
/// insertion mode to the original insertion mode".
fn pop_to_original_mode(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        old(p)@.mode == Mode::Text,
    ensures
        final(p)@ == (Parser { mode: pop(old(p)@).original_mode, ..pop(old(p)@) }),
        parser_inv(final(p)@),
{
    pop_exec(p);
    proof {
        lemma_inv_mode(p@, p@.original_mode);
    }
    p.mode = copy_mode(&p.original_mode);
}

/// Case 3 of the "text" insertion mode ([`text_script_end`]).
pub fn text_script_end_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
        old(p)@.mode == Mode::Text,
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        final(p)@ == text_script_end(old(p)@),
        parser_inv(final(p)@),
{
    // "Let script be the current node."
    let script = if p.open.is_empty() {
        0
    } else {
        current_node_exec(p).id
    };
    pop_to_original_mode(p);
    // "Prepare the script element script."
    if !p.stopped {
        let ghost a = p.actions@;
        p.actions.push(ExecAction::ScriptReady(script));
        proof {
            assert(actions_view(p.actions@) =~= actions_view(a).push(Action::ScriptReady(script)));
        }
    }
}

} // verus!
