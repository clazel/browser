//! `theorem_actions_ordered` (Phase 4 item 4.9): in the actions of a whole
//! parse, `Action::StopParsing` occurs at most once and only as the last
//! action, and `Action::ChangeEncoding` occurs at most once, and never when
//! the confidence starts certain. Together they let the pipeline run the
//! parser at most twice.
//!
//! The proof. Only three steps of the transcription touch the parser's
//! `actions`, `tentative` and `stopped` fields: `stop_parsing` (which pushes
//! `StopParsing` and sets `stopped`, unless already stopped), the "in head"
//! `meta` rule's `change_the_encoding` (which pushes `ChangeEncoding` and
//! clears `tentative`, only when tentative) and the "text" mode's `script`
//! end tag (which pushes `ScriptReady`, unless stopped). Every other helper
//! and mode [`grows`]: it keeps those fields, or stops parsing
//! ([`frame_base`], [`frame_body`], [`frame_in_body`], [`frame_modes`]).
//! Every rule application, and so every run of the reprocessing loop and
//! every `dispatch` step, satisfies [`step_ok`] ([`frame_modes`],
//! [`actions`]), which composes, and [`theorem_actions_ordered`] follows by
//! induction over `parse_steps`.
//!
//! No hypothesis on the parser states is needed (in particular not
//! `modes_ok`): the property holds for whatever `run` returns, and for
//! `tree_construction`'s fallback.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

pub mod actions;
pub mod frame_base;
pub mod frame_body;
pub mod frame_in_body;
pub mod frame_modes;
pub mod nodes;
pub mod open_elements;

/// Every name of the transcription and of this module, for the ghost
/// imports of the submodules (`use super::spec::*;`).
mod spec {
    #[cfg(verus_only)]
    pub use super::*;
    #[cfg(verus_only)]
    pub use crate::spec::*;
}

verus! {

/// The parser `q` has the same actions, confidence and stopped flag as `p`.
pub open spec fn same_view(p: Parser, q: Parser) -> bool {
    q.actions == p.actions && q.tentative == p.tentative && q.stopped == p.stopped
}

/// `q` comes from `p` by steps that keep the actions, the confidence and
/// the stopped flag, or that also stop parsing once (§13.2.7, or the node
/// limit): what every helper of the transcription does except "change the
/// encoding" and the `script` end tag.
pub open spec fn grows(p: Parser, q: Parser) -> bool {
    same_view(p, q) || (!p.stopped && q.stopped && q.tentative == p.tentative && q.actions == p.actions.push(
        Action::StopParsing,
    ))
}

/// The actions `q` adds to `p`'s: `p`'s are a prefix of `q`'s; a stopped
/// parser adds none and stays stopped; the confidence never becomes
/// tentative again; a new `StopParsing` is the last action and `q` is
/// stopped; a new `ChangeEncoding` is the only new one, and changes the
/// confidence from tentative to certain.
pub open spec fn step_ok(p: Parser, q: Parser) -> bool {
    &&& p.actions.len() <= q.actions.len()
    &&& q.actions.subrange(0, p.actions.len() as int) == p.actions
    &&& p.stopped ==> q.actions == p.actions && q.stopped
    &&& q.tentative ==> p.tentative
    &&& forall|i: int|
        p.actions.len() <= i < q.actions.len() && (#[trigger] q.actions[i]) is StopParsing ==> i == q.actions.len() - 1
            && q.stopped
    &&& forall|i: int|
        p.actions.len() <= i < q.actions.len() && (#[trigger] q.actions[i]) is ChangeEncoding ==> p.tentative
            && !q.tentative
    &&& forall|i: int, j: int|
        p.actions.len() <= i < j < q.actions.len() && (#[trigger] q.actions[i]) is ChangeEncoding ==> !((#[trigger] q.actions[j]) is ChangeEncoding)
}

/// [`grows`] is transitive.
pub proof fn lemma_grows_trans(p: Parser, q: Parser, r: Parser)
    requires
        grows(p, q),
        grows(q, r),
    ensures
        grows(p, r),
{
}

/// [`grows`] implies [`step_ok`].
pub proof fn lemma_grows_step_ok(p: Parser, q: Parser)
    requires
        grows(p, q),
    ensures
        step_ok(p, q),
{
    if same_view(p, q) {
        assert(q.actions.subrange(0, p.actions.len() as int) =~= p.actions);
    } else {
        assert(q.actions.subrange(0, p.actions.len() as int) =~= p.actions);
        assert forall|i: int, j: int|
            p.actions.len() <= i < j < q.actions.len() && (#[trigger] q.actions[i]) is ChangeEncoding implies !((#[trigger] q.actions[j]) is ChangeEncoding) by {
            assert(i == p.actions.len());
        }
    }
}

/// [`step_ok`] is reflexive.
pub proof fn lemma_step_ok_refl(p: Parser)
    ensures
        step_ok(p, p),
{
    assert(p.actions.subrange(0, p.actions.len() as int) =~= p.actions);
}

/// [`step_ok`] is transitive.
pub proof fn lemma_step_ok_trans(p: Parser, q: Parser, r: Parser)
    requires
        step_ok(p, q),
        step_ok(q, r),
    ensures
        step_ok(p, r),
{
    let (a, b, c) = (p.actions, q.actions, r.actions);
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] c[i] == b[i] by {
        assert(c.subrange(0, b.len() as int)[i] == c[i]);
    }
    assert(c.subrange(0, a.len() as int) =~= a) by {
        assert forall|i: int| 0 <= i < a.len() implies c.subrange(0, a.len() as int)[i] == #[trigger] a[i] by {
            assert(b.subrange(0, a.len() as int)[i] == b[i]);
        }
    }
    assert forall|i: int| a.len() <= i < c.len() && (#[trigger] c[i]) is StopParsing implies i == c.len() - 1 && r.stopped by {
        if i < b.len() {
            assert(b[i] is StopParsing);
            assert(q.stopped);
        }
    }
    assert forall|i: int| a.len() <= i < c.len() && (#[trigger] c[i]) is ChangeEncoding implies p.tentative && !r.tentative by {
        if i < b.len() {
            assert(b[i] is ChangeEncoding);
        }
    }
    assert forall|i: int, j: int| a.len() <= i < j < c.len() && (#[trigger] c[i]) is ChangeEncoding implies !((#[trigger] c[j]) is ChangeEncoding) by {
        if j < b.len() {
            assert(b[i] is ChangeEncoding);
            assert(b[j] == c[j]);
        } else if i < b.len() {
            assert(b[i] is ChangeEncoding);
            assert(!q.tentative);
        } else {
        }
    }
}

/// [`step_ok`] followed by [`grows`].
pub proof fn lemma_step_ok_grows(p: Parser, q: Parser, r: Parser)
    requires
        step_ok(p, q),
        grows(q, r),
    ensures
        step_ok(p, r),
{
    lemma_grows_step_ok(q, r);
    lemma_step_ok_trans(p, q, r);
}

/// [`grows`] followed by [`step_ok`].
pub proof fn lemma_grows_step_ok_trans(p: Parser, q: Parser, r: Parser)
    requires
        grows(p, q),
        step_ok(q, r),
    ensures
        step_ok(p, r),
{
    lemma_grows_step_ok(p, q);
    lemma_step_ok_trans(p, q, r);
}

/// **The order of the actions** (Phase 4 item 4.9): in the actions of a
/// whole parse `parse(env, tf, s0, url, scripting, tentative, n)`,
/// - `Action::StopParsing` occurs at most once, and if it occurs it is the
///   last action (no hypothesis);
/// - `Action::ChangeEncoding` occurs at most once, and never if `tentative`
///   is false (no hypothesis).
///
/// No hypothesis at all: in particular not `modes_ok` of the states, since
/// every outcome of every rule (and `tree_construction`'s fallback) keeps
/// the order.
pub proof fn theorem_actions_ordered<S>(
    env: EncFns,
    tf: TokFns<S>,
    s0: S,
    url: Seq<u32>,
    scripting: bool,
    tentative: bool,
    n: nat,
)
    ensures
        ({
            let acts = parse(env, tf, s0, url, scripting, tentative, n).1;
            &&& forall|i: int| 0 <= i < acts.len() && (#[trigger] acts[i]) is StopParsing ==> i == acts.len() - 1
            &&& forall|i: int, j: int|
                0 <= i < j < acts.len() && (#[trigger] acts[i]) is ChangeEncoding ==> !((#[trigger] acts[j]) is ChangeEncoding)
            &&& !tentative ==> forall|i: int| 0 <= i < acts.len() ==> !((#[trigger] acts[i]) is ChangeEncoding)
        }),
{
    let p = new_parser(url, scripting, tentative);
    assert(actions::acts_ok(seq![], p, tentative));
    actions::lemma_parse_steps(env, tf, s0, p, seq![], n, tentative);
}

} // verus!
