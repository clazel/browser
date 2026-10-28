//! Facts proven about the tokenizer spec. They are evidence that the
//! transcription is right, and what the implementation's contract rests
//! on:
//! - `theorem_tokenizer_total` (in `termination.rs`, by the `decreases`
//!   of [`super::spec::run`]): the tokenizer is a total function;
//! - [`theorem_step_equals_whole`]: the whole-input face is the fold of
//!   the one-token face.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The two faces agree: calling [`next_token`] until the tokenizer stops
/// gives the tokens [`run`] gives.
pub proof fn theorem_step_equals_whole(input: Seq<u32>, t: Tokenizer)
    ensures
        super::contract::fold_next_token(input, t) == run(input, t),
    decreases super::termination::remaining(input, t), super::termination::rank(input, t),
{
    if !stopped(input, t) {
        super::termination::lemma_step_decreases(input, t);
        let (n, toks) = step(input, t);
        if toks.len() > 0 || stopped(input, n) {
            if !stopped(input, n) {
                theorem_step_equals_whole(input, n);
            }
        } else {
            theorem_step_equals_whole(input, n);
            assert(toks =~= Seq::<Token>::empty());
            if !stopped(input, n) {
                assert(run(input, t) == toks + run(input, n));
                assert(toks + run(input, n) =~= run(input, n));
            }
        }
    }
}

} // verus!
