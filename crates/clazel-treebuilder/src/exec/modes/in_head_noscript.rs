//! HTML §13.2.6.4.5 the "in head noscript" insertion mode
//! ([`mode_in_head_noscript`]) over [`ParserBuf`].

use super::super::stack::*;
use super::super::types::*;
use super::initial::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.5 the "in head noscript" insertion mode
/// ([`mode_in_head_noscript`]).
pub fn mode_in_head_noscript_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_in_head_noscript(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(in_head_noscript_anything_else);
    if is_whitespace_tok(&t) {
        // 4.
        return ExecOutcome::Using(Mode::InHead, t);
    }
    match t {
        // 1.
        ExecTok::Doctype { .. } => ExecOutcome::Done,
        ExecTok::Start(tt) => {
            if matches!(tt.tag, Tag::Html) {
                // 2.
                ExecOutcome::Using(Mode::InBody, ExecTok::Start(tt))
            } else if matches!(tt.tag, Tag::Basefont | Tag::Bgsound | Tag::Link | Tag::Meta | Tag::Noframes | Tag::Style) {
                // 4.
                ExecOutcome::Using(Mode::InHead, ExecTok::Start(tt))
            } else if matches!(tt.tag, Tag::Head | Tag::Noscript) {
                // 6.
                ExecOutcome::Done
            } else {
                // 7.
                in_head_noscript_anything_else_exec(p, ExecTok::Start(tt))
            }
        },
        ExecTok::End(tt) => {
            if matches!(tt.tag, Tag::Noscript) {
                // 3.
                pop_exec(p);
                proof {
                    lemma_inv_mode(p@, Mode::InHead);
                }
                p.mode = Mode::InHead;
                ExecOutcome::Done
            } else if matches!(tt.tag, Tag::Br) {
                // 5.
                in_head_noscript_anything_else_exec(p, ExecTok::End(tt))
            } else {
                // 6.
                ExecOutcome::Done
            }
        },
        // 4.
        ExecTok::Comment(d) => ExecOutcome::Using(Mode::InHead, ExecTok::Comment(d)),
        ExecTok::Pi(target, d) => ExecOutcome::Using(Mode::InHead, ExecTok::Pi(target, d)),
        // 7.
        t => in_head_noscript_anything_else_exec(p, t),
    }
}

/// The "anything else" entry of the "in head noscript" insertion mode
/// ([`in_head_noscript_anything_else`]).
pub fn in_head_noscript_anything_else_exec(p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
    ensures
        outcome_view(o, final(p)@) == in_head_noscript_anything_else(old(p)@, t@),
        parser_inv(final(p)@),
{
    pop_exec(p);
    proof {
        lemma_inv_mode(p@, Mode::InHead);
    }
    p.mode = Mode::InHead;
    ExecOutcome::Reprocess(t)
}

} // verus!
