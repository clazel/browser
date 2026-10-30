//! `invariant::parser_inv` of every reachable parser until it stops
//! (Phase 4 item 4.9): [`theorem_reachable_parser_inv`].
//!
//! The proof. `parser_inv` is `parser_wf`, `tags_wf`, `templates_wf` and
//! (until parsing stops) `head_ok`. `super::reachable::theorem_reachable_wf`
//! gives `parser_wf` and `head_ok` of a running reachable parser, and
//! `invariant::reachable_inv`, whose `reach_core` holds `tags_wf` and the
//! document facts `reachable::doc::dinv`; those give `templates_wf`
//! (`reachable::doc::lemma_dinv_templates_wf`). How `dinv` is kept: a
//! `template` element gets template contents by its token's tag
//! ("create an element for a token") and is recognised by its name; the
//! reachable-state proof creates elements only for tagged tokens, so the
//! record pushed has template contents if it is a `template`, and every
//! insertion's parent is computed from the stack's tagged records, so it
//! is never a `template` element without template contents (see
//! `reachable`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A running parser with `super::reachable::reach_wf` satisfies
/// `invariant::parser_inv`.
pub proof fn lemma_reach_wf_parser_inv(p: Parser)
    requires
        super::reachable::reach_wf(p),
        !p.stopped,
    ensures
        parser_inv(p),
{
    crate::reachable::doc::lemma_dinv_templates_wf(p);
}

/// **Every reachable parser satisfies `parser_inv` until it stops** (Phase
/// 4 item 4.9): for every parser reached from `new_parser` or from
/// `fragment_parser` by `dispatch` steps (any tokens, any encoding
/// functions) that has not stopped, `invariant::parser_inv` holds:
/// `parser_wf`, `tags_wf`, `templates_wf` (every HTML `template` on the
/// stack of open elements, and every `template` element with a child, has
/// template contents) and `head_ok`. No hypotheses.
pub proof fn theorem_reachable_parser_inv(
    env: EncFns,
    url: Seq<u32>,
    ctx: Context,
    scripting: bool,
    tentative: bool,
    tokens: Seq<Token>,
)
    ensures
        ({
            let q = crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens);
            !q.stopped ==> parser_inv(q)
        }),
        ({
            let q = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
            !q.stopped ==> parser_inv(q)
        }),
{
    super::reachable::theorem_reachable_wf(env, url, ctx, scripting, tentative, tokens);
    let q1 = crate::reachable::run::dispatch_steps(env, new_parser(url, scripting, tentative), tokens);
    let q2 = crate::reachable::run::dispatch_steps(env, fragment_parser(ctx, scripting).0, tokens);
    if !q1.stopped {
        lemma_reach_wf_parser_inv(q1);
    }
    if !q2.stopped {
        lemma_reach_wf_parser_inv(q2);
    }
}

} // verus!
