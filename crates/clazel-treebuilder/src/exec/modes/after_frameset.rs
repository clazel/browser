//! HTML §13.2.6.4.19 the "after frameset" insertion mode
//! ([`mode_after_frameset`]).

use super::super::insert::*;
use super::super::types::*;
use super::after_body::{is_ascii_whitespace_exec, set_mode_exec};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.19 the "after frameset" insertion mode
/// ([`mode_after_frameset`]).
pub fn mode_after_frameset_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_after_frameset(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    match t {
        ExecTok::Char(c) => {
            if is_ascii_whitespace_exec(c) {
                // 1. "Insert the character."
                insert_char_exec(p, c);
            }
            // 9. "Anything else": "Parse error. Ignore the token."
            ExecOutcome::Done
        },
        ExecTok::Comment(data) => {
            // 2. "Insert a comment."
            insert_comment_exec(p, data, None);
            ExecOutcome::Done
        },
        ExecTok::Pi(target, data) => {
            // 3. "Insert a processing instruction."
            insert_pi_exec(p, target, data, None);
            ExecOutcome::Done
        },
        // 4. "A DOCTYPE token": "Parse error. Ignore the token."
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 5. "Process the token using the rules for the "in body"
                // insertion mode."
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            } else if matches!(tt.tag, Tag::Noframes) {
                // 7. "Process the token using the rules for the "in head"
                // insertion mode."
                ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
            } else {
                // 9.
                ExecOutcome::Done
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 6. "Switch the insertion mode to "after after frameset"."
                set_mode_exec(p, Mode::AfterAfterFrameset);
            }
            // 9.
            ExecOutcome::Done
        },
        ExecTok::Eof => {
            // 8. "Stop parsing."
            stop_parsing_exec(p);
            ExecOutcome::Done
        },
    }
}

} // verus!
