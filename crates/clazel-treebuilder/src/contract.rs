//! Contracts the executable tree builder must be proven to meet (Phase 4
//! items 4.9 and 4.10), stated over the spec: the exec step's `requires`
//! and `ensures` are exactly these predicates, over the views of its state.

#[allow(unused_imports)]
use crate::invariant::*;
#[allow(unused_imports)]
use crate::spec::dispatch::*;
#[allow(unused_imports)]
use crate::spec::state::*;
use clazel_dom::spec::{Document, NodeId};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of `step(&mut ParserBuf, Token)`: a reachable state.
pub open spec fn step_requires(p: Parser) -> bool {
    parser_wf(p)
}

/// Contract for `step`: the new state and the actions are those of the
/// spec's one-token step, for any encoding functions.
pub open spec fn step_ensures(env: EncFns, p: Parser, token: Token, out: Parser, actions: Seq<Action>) -> bool {
    (out, actions) == dispatch(env, p, token)
}

/// Contract for the whole parser `parse` over a tokenizer: the document and
/// the actions of the spec's `parse`, with `n` the tokenizer's bound on the
/// tokens it emits.
pub open spec fn parse_ensures<S>(
    env: EncFns,
    tf: TokFns<S>,
    s0: S,
    url: Seq<u32>,
    scripting: bool,
    tentative: bool,
    n: nat,
    doc: Document,
    actions: Seq<Action>,
) -> bool {
    (doc, actions) == parse(env, tf, s0, url, scripting, tentative, n)
}

/// Contract for the fragment parser `parse_fragment`.
pub open spec fn parse_fragment_ensures<S>(
    env: EncFns,
    tf: TokFns<S>,
    s0: S,
    ctx: Context,
    scripting: bool,
    n: nat,
    doc: Document,
    fragment: NodeId,
    actions: Seq<Action>,
) -> bool {
    (doc, fragment, actions) == parse_fragment(env, tf, s0, ctx, scripting, n)
}

} // verus!
