//! Theorems about the tokenizer's spec. They are evidence that the transcription is
//! right, and what the parser relies on, not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Each call of "consume a token" consumes a code point or returns the EOF token, so
/// tokenization ends on every input.
pub proof fn theorem_tokenizer_total(input: Seq<u32>, pos: int, unicode_ranges_allowed: bool)
    ensures
        consume_a_token(input, pos, unicode_ranges_allowed).0 is Eof || consume_a_token(
            input,
            pos,
            unicode_ranges_allowed,
        ).1 > pos,
{
    super::termination::lemma_token_advances(input, pos, unicode_ranges_allowed);
}

/// [`tokenize_loop`] adds at most one token per code point left, and the EOF token, and
/// keeps what it was given.
pub proof fn lemma_loop_bounded(input: Seq<u32>, pos: int, flag: bool, tokens: Seq<Token>)
    ensures
        tokenize_loop(input, pos, flag, tokens).len() <= tokens.len() + remaining(input, pos) + 1,
        tokenize_loop(input, pos, flag, tokens).len() > tokens.len(),
        tokenize_loop(input, pos, flag, tokens).subrange(0, tokens.len() as int) == tokens,
        tokenize_loop(input, pos, flag, tokens).last() is Eof,
    decreases remaining(input, pos),
{
    super::termination::lemma_token_advances(input, pos, flag);
    let (token, next) = consume_a_token(input, pos, flag);
    if token is Eof {
        assert(tokens.push(token).subrange(0, tokens.len() as int) =~= tokens);
    } else {
        let pushed = tokens.push(token);
        lemma_loop_bounded(input, next, flag, pushed);
        let all = tokenize_loop(input, next, flag, pushed);
        assert(all.subrange(0, tokens.len() as int) =~= all.subrange(
            0,
            pushed.len() as int,
        ).subrange(0, tokens.len() as int));
        assert(pushed.subrange(0, tokens.len() as int) =~= tokens);
    }
}

/// Tokenizing gives at most one token per code point, and the EOF token, so everything
/// that walks the tokens is linear in the sheet.
pub proof fn theorem_tokens_bounded(input: Seq<u32>)
    ensures
        tokenize(input).len() <= input.len() + 1,
{
    lemma_loop_bounded(input, 0, false, Seq::empty());
}

/// The tokens always end in the EOF token, which the parser reads as the end.
pub proof fn theorem_tokens_end_in_eof(input: Seq<u32>)
    ensures
        tokenize(input).len() > 0,
        tokenize(input).last() is Eof,
{
    lemma_loop_bounded(input, 0, false, Seq::empty());
}

/// The two faces of the tokenizer agree: one step of "consume a token" and then the rest
/// is the whole, so a parser can call it "on-demand" (§4's note).
pub proof fn theorem_step_equals_whole(
    input: Seq<u32>,
    pos: int,
    unicode_ranges_allowed: bool,
    tokens: Seq<Token>,
)
    ensures
        tokenize_loop(input, pos, unicode_ranges_allowed, tokens) == ({
            let (token, next) = consume_a_token(input, pos, unicode_ranges_allowed);
            if token is Eof {
                tokens.push(token)
            } else {
                tokenize_loop(input, next, unicode_ranges_allowed, tokens.push(token))
            }
        }),
{
}

} // verus!
