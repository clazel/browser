//! HTML §13.2.6.4.21 the "after after frameset" insertion mode
//! ([`mode_after_after_frameset`]).

use super::super::insert::*;
use super::super::types::*;
use super::after_body::is_ascii_whitespace_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.21 the "after after frameset" insertion mode
/// ([`mode_after_after_frameset`]).
pub fn mode_after_after_frameset_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_after_after_frameset(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
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
                // 6. "Anything else": "Parse error. Ignore the token."
                ExecOutcome::Done
            }
        },
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 3.
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            } else if matches!(tt.tag, Tag::Noframes) {
                // 5. "Process the token using the rules for the "in head"
                // insertion mode."
                ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
            } else {
                // 6.
                ExecOutcome::Done
            }
        },
        // 6.
        ExecTok::End(_) => ExecOutcome::Done,
        ExecTok::Eof => {
            // 4. "Stop parsing."
            stop_parsing_exec(p);
            ExecOutcome::Done
        },
    }
}

} // verus!
