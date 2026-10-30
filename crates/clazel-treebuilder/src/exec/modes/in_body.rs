//! HTML §13.2.6.4.7 the "in body" insertion mode over [`ParserBuf`]
//! (`spec/modes/in_body.rs`, [`mode_in_body`]): the dispatch by token kind,
//! the character and end-of-file cases. The start tag cases are in
//! [`super::in_body_start`], the end tag cases in [`super::in_body_end`].

#[cfg(verus_only)]
use super::super::frame::*;
use super::super::insert::*;
use super::super::types::*;
use super::in_body_end::*;
use super::in_body_start::*;
use super::in_body_start_cases::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the "in body" rules need of a token: a tag token's tag is the
/// classification of its name.
pub open spec fn tok_ok(t: Tok) -> bool {
    match t {
        Tok::Start(tt) => tok_tagged(tt),
        Tok::End(tt) => tok_tagged(tt),
        _ => true,
    }
}

/// Cases 1 to 3, character tokens ([`in_body_char`]).
pub fn in_body_char_exec(p: &mut ParserBuf, c: u32)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
    ensures
        final(p)@ == in_body_char(old(p)@, c),
        parser_inv(final(p)@),
{
    if c == 0 {
        // 1. "Parse error. Ignore the token."
        return ;
    }
    // 2., 3. "Reconstruct the active formatting elements, if any. Insert the
    // token's character."
    reconstruct_formatting_exec(p);
    insert_char_exec(p, c);
    if !(c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20) {
        // 3. "Set the frameset-ok flag to "not ok"."
        frameset_not_ok_exec(p);
    }
}

/// Case 11, "An end-of-file token" ([`in_body_eof`]).
pub fn in_body_eof_exec(p: &mut ParserBuf) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == in_body_eof(old(p)@, Tok::Eof),
        parser_inv(final(p)@),
{
    if !p.template_modes.is_empty() {
        // "process the token using the rules for the "in template" insertion
        // mode."
        return ExecOutcome::Using(Mode::InTemplate, ExecTok::Eof);
    }
    // 2. "Stop parsing."
    stop_parsing_exec(p);
    ExecOutcome::Done
}

/// §13.2.6.4.7 the "in body" insertion mode ([`mode_in_body`]).
///
/// It needs a parser that has not stopped, with its stack rooted at the
/// `html` element (the "in body" rules insert at the appropriate place),
/// whose insertion mode is neither "text" nor "in table text"
/// (`termination::rules_ok` for the "in body" rules), and a tagged token.
pub fn mode_in_body_exec<E: EncFnsExec>(env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped,
        stack_rooted(old(p)@),
        old(p)@.mode != Mode::Text && old(p)@.mode != Mode::InTableText,
        tok_ok(t@),
    ensures
        outcome_view(o, final(p)@) == mode_in_body(env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(tag_of);
    hide(parser_inv);
    hide(in_body_start_tag);
    hide(in_body_end_tag);
    hide(in_body_char);
    hide(in_body_eof);
    hide(insert_comment);
    hide(insert_pi);
    match t {
        // 1. to 3.
        ExecTok::Char(c) => {
            in_body_char_exec(p, c);
            ExecOutcome::Done
        },
        // 4. "Insert a comment."
        ExecTok::Comment(data) => {
            insert_comment_exec(p, data, None);
            ExecOutcome::Done
        },
        // 5. "Insert a processing instruction."
        ExecTok::Pi(target, data) => {
            insert_pi_exec(p, target, data, None);
            ExecOutcome::Done
        },
        // 6. "Parse error. Ignore the token."
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        // Start tags.
        ExecTok::Start(tt) => in_body_start_tag_exec(env, p, tt),
        // 11.
        ExecTok::Eof => in_body_eof_exec(p),
        // End tags.
        ExecTok::End(tt) => in_body_end_tag_exec(env, p, tt),
    }
}

} // verus!
