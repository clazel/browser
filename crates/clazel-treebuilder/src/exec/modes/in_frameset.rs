//! HTML §13.2.6.4.18 the "in frameset" insertion mode
//! ([`mode_in_frameset`]).

use super::super::insert::*;
use super::super::stack::*;
use super::super::types::*;
use super::after_body::{is_ascii_whitespace_exec, set_mode_exec};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.18 the "in frameset" insertion mode ([`mode_in_frameset`]).
pub fn mode_in_frameset_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        t@ is Start ==> tok_tagged(t@->Start_0),
    ensures
        outcome_view(o, final(p)@) == mode_in_frameset(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    match t {
        ExecTok::Char(c) => {
            if is_ascii_whitespace_exec(c) {
                // 1. "Insert the character."
                insert_char_exec(p, c);
            }
            // 11. "Anything else": "Parse error. Ignore the token."
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
            } else if matches!(tt.tag, Tag::Frameset) {
                // 6. "Insert an HTML element for the token."
                let _ = insert_html_element_exec(p, &tt);
                ExecOutcome::Done
            } else if matches!(tt.tag, Tag::Frame) {
                // 8. "Insert an HTML element for the token. Immediately pop
                // the current node off the stack of open elements."
                let _ = insert_html_element_exec(p, &tt);
                if !p.stopped {
                    pop_exec(p);
                }
                ExecOutcome::Done
            } else if matches!(tt.tag, Tag::Noframes) {
                // 9. "Process the token using the rules for the "in head"
                // insertion mode."
                ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
            } else {
                // 11.
                ExecOutcome::Done
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Frameset) {
                // 7. "If the current node is the root html element, then this
                // is a parse error; ignore the token. (fragment case)"
                if p.open.len() <= 1 {
                    return ExecOutcome::Done;
                }
                // "Otherwise, pop the current node from the stack of open
                // elements."
                pop_exec(p);
                // "If the parser's fragment context element is null and the
                // current node is no longer a frameset element, then switch
                // the insertion mode to "after frameset"."
                if p.context.is_none() && !is_html_exec(current_node_exec(p), &Tag::Frameset) {
                    set_mode_exec(p, Mode::AfterFrameset);
                }
            }
            // 11.
            ExecOutcome::Done
        },
        ExecTok::Eof => {
            // 10. "Stop parsing."
            stop_parsing_exec(p);
            ExecOutcome::Done
        },
    }
}

} // verus!
