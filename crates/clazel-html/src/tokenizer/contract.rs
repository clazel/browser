//! Contracts the executable tokenizer must be proven to meet. Each exec
//! function's `requires` and `ensures` are exactly these predicates, so
//! reviewing these and [`super::spec`] is enough to know what the
//! implementation guarantees.
//!
//! The exec tokenizer's state views as a spec [`Tokenizer`] with one
//! difference: it keeps the character reference code capped at 0x110000
//! (`crate::charref::contract::capped_code`), since the spec's code is
//! unbounded and every number above 0x10FFFF gives the same code point
//! (`crate::charref::lemmas::lemma_end_code_cap`). [`abstracts`] relates a
//! spec tokenizer to the exec one's view, and the contracts hold for every
//! spec tokenizer the exec one abstracts.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exec tokenizer's view `v` stands for the spec tokenizer `t`: the
/// same in every field, with the character reference code capped.
pub open spec fn abstracts(t: Tokenizer, v: Tokenizer) -> bool {
    v == Tokenizer { character_reference_code: crate::charref::contract::capped_code(t.character_reference_code), ..t }
}

/// What holds of the tokenizer between calls: its position is within the
/// input or at its end.
pub open spec fn wf(input: Seq<u32>, t: Tokenizer) -> bool {
    t.pos <= input.len()
}

/// Contract for `preprocess(&[u32]) -> Vec<u32>`: §13.2.3.5's newline
/// normalization.
pub open spec fn preprocess_ensures(input: Seq<u32>, output: Seq<u32>) -> bool {
    output == preprocess(input)
}

/// Contract for `ExecTokenizer::new(State, Option<Vec<u32>>) ->
/// ExecTokenizer`: the tokenizer before the first step.
pub open spec fn new_ensures(start_state: State, last_start_tag: Option<Seq<u32>>, output: Tokenizer) -> bool {
    output == initial(start_state, last_start_tag)
}

/// Precondition of `ExecTokenizer::next_token(&mut self, &[u32]) ->
/// Vec<ExecToken>`, for the spec tokenizer `t` the exec one stands for.
pub open spec fn next_token_requires(input: Seq<u32>, t: Tokenizer, before: Tokenizer) -> bool {
    wf(input, t) && abstracts(t, before)
}

/// Contract for `ExecTokenizer::next_token(&mut self, &[u32]) ->
/// Vec<ExecToken>`: the spec's one-token face from `t`. The exec tokenizer
/// after the call stands for the spec tokenizer after it, which is again
/// well formed.
pub open spec fn next_token_ensures(input: Seq<u32>, t: Tokenizer, after: Tokenizer, output: Seq<Token>) -> bool {
    output == next_token(input, t).1 && abstracts(next_token(input, t).0, after) && wf(
        input,
        next_token(input, t).0,
    )
}

/// Contract for `tokenize(&[u32], State, Option<Vec<u32>>) ->
/// Vec<ExecToken>`: the spec's whole-input face, computed as the fold of
/// `next_token` (`theorem_step_equals_whole`).
pub open spec fn tokenize_ensures(
    input: Seq<u32>,
    start_state: State,
    last_start_tag: Option<Seq<u32>>,
    output: Seq<Token>,
) -> bool {
    output == tokenize(input, start_state, last_start_tag)
}

/// The spec's whole-input face is the fold of its one-token face: the
/// tokens [`next_token`] gives, call after call, until the tokenizer
/// stops. `theorem_step_equals_whole` proves this equals [`run`], and the
/// exec `tokenize` computes it.
pub open spec fn fold_next_token(input: Seq<u32>, t: Tokenizer) -> Seq<Token>
    decreases super::termination::remaining(input, t), super::termination::rank(input, t) via fold_decreases
{
    if stopped(input, t) {
        seq![]
    } else {
        let (n, toks) = next_token(input, t);
        if stopped(input, n) {
            toks
        } else {
            toks + fold_next_token(input, n)
        }
    }
}

/// Termination of [`fold_next_token`]: a call of [`next_token`] runs at
/// least one step, and each lowers the measure.
#[via_fn]
pub proof fn fold_decreases(input: Seq<u32>, t: Tokenizer) {
    super::termination::lemma_next_token_decreases(input, t);
}

} // verus!
