//! HTML §13.2.6.4.10 the "in table text" insertion mode
//! ([`mode_in_table_text`]) over [`ParserBuf`], with the reprocessing of
//! the pending table character tokens ([`reprocess_pending`]) as a loop.

use super::in_table::{in_table_char_exec, is_ascii_whitespace_exec};
#[cfg(verus_only)]
use super::in_table::{lemma_in_table_anything_else_char, rooted_or_stopped};
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
use crate::exec::insert::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`has_non_whitespace`].
pub fn has_non_whitespace_exec(s: &[u32]) -> (r: bool)
    ensures
        r == has_non_whitespace(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_ascii_whitespace(#[trigger] s@[j]),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => vstd::pervasive::unreached(),
        };
        if !is_ascii_whitespace_exec(c) {
            proof {
                assert(!is_ascii_whitespace(s@[i as int]));
            }
            return true;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    false
}

/// [`reprocess_pending`] from index 0 of `s`: each character with the "in
/// table" "anything else" rules, in order.
pub fn reprocess_pending_exec(p: &mut ParserBuf, s: &[u32], Ghost(env): Ghost<EncFns>)
    requires
        parser_inv(old(p)@),
        rooted_or_stopped(old(p)@),
    ensures
        final(p)@ == reprocess_pending(env, old(p)@, s@, 0),
        parser_inv(final(p)@),
        rooted_or_stopped(final(p)@),
        final(p)@.mode == old(p)@.mode,
        final(p)@.original_mode == old(p)@.original_mode,
        final(p)@.template_modes == old(p)@.template_modes,
        final(p)@.pending_table_text == old(p)@.pending_table_text,
{
    hide(in_table_anything_else);
    hide(in_body_char);
    hide(parser_inv);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            parser_inv(p@),
            rooted_or_stopped(p@),
            reprocess_pending(env, p@, s@, i as int) == reprocess_pending(env, old(p)@, s@, 0),
            p@.mode == old(p)@.mode,
            p@.original_mode == old(p)@.original_mode,
            p@.template_modes == old(p)@.template_modes,
            p@.pending_table_text == old(p)@.pending_table_text,
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => vstd::pervasive::unreached(),
        };
        proof {
            lemma_in_table_anything_else_char(env, p@, c);
        }
        in_table_char_exec(p, c);
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
}

/// §13.2.6.4.10 the "in table text" insertion mode ([`mode_in_table_text`]).
pub fn mode_in_table_text_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, t: ExecTok) -> (o: ExecOutcome)
    requires
        parser_inv(old(p)@),
        stack_rooted(old(p)@),
        crate::termination::rules_ok(Rules::Html(Mode::InTableText), old(p)@),
    ensures
        outcome_view(o, final(p)@) == mode_in_table_text(_env.enc(), old(p)@, t@),
        parser_inv(final(p)@),
{
    hide(reprocess_pending);
    hide(insert_characters);
    hide(parser_inv);
    if let ExecTok::Char(c) = t {
        if c == 0 {
            // 1.
            return ExecOutcome::Done;
        }
        // 2.
        let ghost p0 = p@;
        p.pending_table_text.push(c);
        proof {
            reveal(parser_inv);
            lemma_inv_iff(p0);
            lemma_inv_iff(p@);
        }
        return ExecOutcome::Done;
    }
    // 3.
    let ghost p0 = p@;
    proof {
        reveal(parser_inv);
        lemma_inv_iff(p0);
    }
    let pending = copy_str(p.pending_table_text.as_slice());
    if has_non_whitespace_exec(pending.as_slice()) {
        reprocess_pending_exec(p, pending.as_slice(), Ghost(_env.enc()));
    } else if !pending.is_empty() {
        insert_characters_exec(p, pending.as_slice());
    }
    let ghost p1 = p@;
    p.mode = copy_mode(&p.original_mode);
    proof {
        reveal(parser_inv);
        lemma_inv_iff(p1);
        lemma_inv_iff(p@);
    }
    ExecOutcome::Reprocess(t)
}

} // verus!
