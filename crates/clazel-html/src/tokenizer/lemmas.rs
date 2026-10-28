//! Facts proven about the tokenizer spec. They are evidence that the
//! transcription is right, and what the implementation's contract rests
//! on:
//! - [`theorem_tokenizer_total`]: the tokenizer is a total function (the
//!   `decreases` of [`super::spec::run`], proven state by state in
//!   `termination.rs`), and every run ends with exactly one end-of-file
//!   token, its last;
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

/// The tokenizer always finishes: from any position within the input (and
/// a current token that is not an end-of-file token, as in [`initial`] and
/// after every step), the tokens it emits end with an end-of-file token,
/// and hold no other.
pub proof fn theorem_tokenizer_total(input: Seq<u32>, t: Tokenizer)
    requires
        !stopped(input, t),
        !(t.current is EndOfFile),
    ensures
        run(input, t).len() > 0,
        run(input, t).last() is EndOfFile,
        forall|k: int| 0 <= k < run(input, t).len() - 1 ==> !(#[trigger] run(input, t)[k] is EndOfFile),
    decreases super::termination::remaining(input, t), super::termination::rank(input, t),
{
    super::termination::lemma_step_decreases(input, t);
    let (n, toks) = step(input, t);
    if !stopped(input, n) {
        theorem_tokenizer_total(input, n);
        let rest = run(input, n);
        assert(!(toks.len() > 0 && toks.last() is EndOfFile));
        assert forall|k: int| 0 <= k < toks.len() implies !(#[trigger] toks[k] is EndOfFile) by {
            if k == toks.len() - 1 {
                assert(toks.last() == toks[k]);
            }
        }
        assert(run(input, t) == toks + rest);
        assert forall|k: int| 0 <= k < (toks + rest).len() - 1 implies !(#[trigger] (toks + rest)[k] is EndOfFile) by {
            if k < toks.len() {
                assert((toks + rest)[k] == toks[k]);
            } else {
                assert((toks + rest)[k] == rest[k - toks.len()]);
            }
        }
    }
}

/// [`theorem_tokenizer_total`] for the whole-input face.
pub proof fn theorem_tokenize_ends_with_eof(input: Seq<u32>, start_state: State, last_start_tag: Option<Seq<u32>>)
    ensures
        tokenize(input, start_state, last_start_tag).len() > 0,
        tokenize(input, start_state, last_start_tag).last() is EndOfFile,
{
    theorem_tokenizer_total(input, initial(start_state, last_start_tag));
}

} // verus!
