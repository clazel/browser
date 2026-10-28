//! HTML §13.2.6.4.17 the "after body" insertion mode
//! ([`mode_after_body`]), and two helpers the modes of this group share:
//! the ASCII whitespace test and switching the insertion mode.

#[cfg(verus_only)]
use super::super::frame::*;
use super::super::insert::*;
use super::super::types::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`is_ascii_whitespace`]: U+0009 TAB, U+000A LF, U+000C FF, U+000D CR or
/// U+0020 SPACE.
pub fn is_ascii_whitespace_exec(c: u32) -> (r: bool)
    ensures
        r == is_ascii_whitespace(c),
{
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// "Switch the insertion mode to `m`", for a mode other than "text", "in
/// table text" and "in template" (whose invariants need more).
pub fn set_mode_exec(p: &mut ParserBuf, m: Mode)
    requires
        parser_inv(old(p)@),
        m != Mode::Text && m != Mode::InTableText && m != Mode::InTemplate,
    ensures
        final(p)@ == (Parser { mode: m, ..old(p)@ }),
        parser_inv(final(p)@),
{
    proof {
        lemma_inv_iff(old(p)@);
    }
    p.mode = m;
    proof {
        assert(p@ == (Parser { mode: m, ..old(p)@ }));
        lemma_inv_iff(p@);
    }
}

/// The root `html` element of a rooted stack is a [`loc_ok`] parent.
pub proof fn lemma_root_loc_ok(p: Parser)
    requires
        parser_inv(p),
        stack_rooted(p),
    ensures
        loc_ok(p.doc, Location { parent: p.open[0].id, child: None }),
{
    lemma_inv_iff(p);
    assert(elem_ok(p.doc, p.open[0]));
}

/// The id of the root element of a rooted stack.
fn root_id_exec(p: &ParserBuf) -> (r: usize)
    requires
        stack_rooted(p@),
    ensures
        r == p@.open[0].id,
{
    let first: usize = 0;
    match p.open.get(first) {
        Some(e) => e.id,
        None => vstd::pervasive::unreached(),
    }
}

/// §13.2.6.4.17 the "after body" insertion mode ([`mode_after_body`]).
pub fn mode_after_body_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_after_body(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    match t {
        ExecTok::Char(c) => {
            if is_ascii_whitespace_exec(c) {
                // 1. "Process the token using the rules for the "in body"
                // insertion mode."
                ExecOutcome::Using(Mode::InBody, ExecTok::Char(c))
            } else {
                // 8. "Parse error. Switch the insertion mode to "in body" and
                // reprocess the token."
                set_mode_exec(p, Mode::InBody);
                ExecOutcome::Reprocess(ExecTok::Char(c))
            }
        },
        ExecTok::Comment(data) => {
            // 2. "Insert a comment given (the first element in the stack of
            // open elements (the html element), null)."
            if p.stopped {
                return ExecOutcome::Done;
            }
            let root = root_id_exec(p);
            proof {
                lemma_root_loc_ok(old(p)@);
            }
            insert_comment_exec(p, data, Some(Location { parent: root, child: None }));
            ExecOutcome::Done
        },
        ExecTok::Pi(target, data) => {
            // 3. "Insert a processing instruction given (the first element in
            // the stack of open elements (the html element), null)."
            if p.stopped {
                return ExecOutcome::Done;
            }
            let root = root_id_exec(p);
            proof {
                lemma_root_loc_ok(old(p)@);
            }
            insert_pi_exec(p, target, data, Some(Location { parent: root, child: None }));
            ExecOutcome::Done
        },
        // 4. "A DOCTYPE token": "Parse error. Ignore the token."
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 5. "Process the token using the rules for the "in body"
                // insertion mode."
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            } else {
                // 8.
                set_mode_exec(p, Mode::InBody);
                ExecOutcome::Reprocess(ExecTok::Start(tt))
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 6. "If the parser's fragment context element is non-null,
                // this is a parse error; ignore the token. (fragment case)
                // Otherwise, switch the insertion mode to "after after
                // body"."
                if p.context.is_none() {
                    set_mode_exec(p, Mode::AfterAfterBody);
                }
                ExecOutcome::Done
            } else {
                // 8.
                set_mode_exec(p, Mode::InBody);
                ExecOutcome::Reprocess(ExecTok::End(tt))
            }
        },
        ExecTok::Eof => {
            // 7. "Stop parsing."
            stop_parsing_exec(p);
            ExecOutcome::Done
        },
    }
}

} // verus!
