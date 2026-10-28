//! HTML §13.2.6.4.20 the "after after body" insertion mode
//! ([`mode_after_after_body`]).

use super::super::insert::*;
use super::super::types::*;
use super::after_body::{is_ascii_whitespace_exec, set_mode_exec};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.20 the "after after body" insertion mode
/// ([`mode_after_after_body`]).
pub fn mode_after_after_body_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_after_after_body(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(parser_inv);
    match t {
        ExecTok::Comment(data) => {
            // 1. "Insert a comment given (the Document object, null)."
            proof {
                lemma_document_location_ok(old(p)@);
            }
            insert_comment_exec(p, data, Some(document_location_exec()));
            ExecOutcome::Done
        },
        ExecTok::Pi(target, data) => {
            // 2. "Insert a processing instruction given (the Document object,
            // null)."
            proof {
                lemma_document_location_ok(old(p)@);
            }
            insert_pi_exec(p, target, data, Some(document_location_exec()));
            ExecOutcome::Done
        },
        // 3. "A DOCTYPE token": "Process the token using the rules for the
        // "in body" insertion mode."
        ExecTok::Doctype { name, public_id, system_id, force_quirks } => ExecOutcome::Using(
            Mode::InBody,
            ExecTok::Doctype { name, public_id, system_id, force_quirks },
        ),
        ExecTok::Char(c) => {
            if is_ascii_whitespace_exec(c) {
                // 3. "Process the token using the rules for the "in body"
                // insertion mode."
                ExecOutcome::Using(Mode::InBody, ExecTok::Char(c))
            } else {
                // 5. "Parse error. Switch the insertion mode to "in body" and
                // reprocess the token."
                set_mode_exec(p, Mode::InBody);
                ExecOutcome::Reprocess(ExecTok::Char(c))
            }
        },
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 3.
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            } else {
                // 5.
                set_mode_exec(p, Mode::InBody);
                ExecOutcome::Reprocess(ExecTok::Start(tt))
            }
        },
        ExecTok::End(tt) => {
            // 5.
            set_mode_exec(p, Mode::InBody);
            ExecOutcome::Reprocess(ExecTok::End(tt))
        },
        ExecTok::Eof => {
            // 4. "Stop parsing."
            stop_parsing_exec(p);
            ExecOutcome::Done
        },
    }
}

} // verus!
