//! Contracts the executable tree builder must be proven to meet (Phase 4
//! items 4.9 and 4.10), stated over the spec: the exec step's `requires`
//! and `ensures` are exactly these predicates, over the views of its state.

#[allow(unused_imports)]
use super::spec::*;
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

/// From the bound `n` on, every bound gives the same whole parse:
/// `parse_steps` from parser `p` and tokenizer state `s` returns the
/// parser `q` and the actions `acts` for every bound `m >= n` (so the
/// bound never runs out: the parser stops by itself first).
pub open spec fn steps_settle<S>(env: EncFns, tf: TokFns<S>, s: S, p: Parser, q: Parser, acts: Seq<Action>, n: nat) -> bool {
    forall|m: nat| n <= m ==> #[trigger] parse_steps(env, tf, s, p, seq![], m) == (q, acts)
}

/// Contract for `exec::driver::parse_real(env, input, url, scripting,
/// tentative) -> (ParserBuf, Vec<ExecAction>)`: the document and the
/// actions are the spec's `parse` with `clazel-html`'s tokenizer
/// ([`join_fns`] over the preprocessed input, §13.2.3.5, from
/// [`join_start`]), for every bound on the tokens from some bound `n` on.
pub open spec fn parse_real_ensures(
    env: EncFns,
    input: Seq<u32>,
    url: Seq<u32>,
    scripting: bool,
    tentative: bool,
    doc: Document,
    actions: Seq<Action>,
) -> bool {
    exists|n: nat| parse_real_from(env, input, url, scripting, tentative, n, doc, actions)
}

/// [`parse_real_ensures`] from the bound `n` on.
pub open spec fn parse_real_from(
    env: EncFns,
    input: Seq<u32>,
    url: Seq<u32>,
    scripting: bool,
    tentative: bool,
    n: nat,
    doc: Document,
    actions: Seq<Action>,
) -> bool {
    forall|m: nat|
        n <= m ==> #[trigger] parse_ensures(
            env,
            join_fns(clazel_html::tokenizer::spec::preprocess(input)),
            join_start(),
            url,
            scripting,
            tentative,
            m,
            doc,
            actions,
        )
}

/// Contract for `exec::driver::parse_fragment_real(env, input, ctx,
/// scripting) -> (ParserBuf, usize, Vec<ExecAction>)`: the spec's
/// `parse_fragment` with `clazel-html`'s tokenizer, for every bound on the
/// tokens from some bound `n` on.
pub open spec fn parse_fragment_real_ensures(
    env: EncFns,
    input: Seq<u32>,
    ctx: Context,
    scripting: bool,
    doc: Document,
    fragment: NodeId,
    actions: Seq<Action>,
) -> bool {
    exists|n: nat| parse_fragment_real_from(env, input, ctx, scripting, n, doc, fragment, actions)
}

/// [`parse_fragment_real_ensures`] from the bound `n` on.
pub open spec fn parse_fragment_real_from(
    env: EncFns,
    input: Seq<u32>,
    ctx: Context,
    scripting: bool,
    n: nat,
    doc: Document,
    fragment: NodeId,
    actions: Seq<Action>,
) -> bool {
    forall|m: nat|
        n <= m ==> #[trigger] parse_fragment_ensures(
            env,
            join_fns(clazel_html::tokenizer::spec::preprocess(input)),
            join_start(),
            ctx,
            scripting,
            m,
            doc,
            fragment,
            actions,
        )
}

} // verus!
