//! Contracts the executable tokenizer must be proven to meet, and the theorems proven
//! about the spec. Each exec function's `ensures` clause is one of these predicates, so
//! reading these and [`super::spec`] is enough to know what the implementation
//! guarantees.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `filter_code_points(&[u32]) -> Vec<u32>`.
pub open spec fn filter_ensures(input: Seq<u32>, output: Seq<u32>) -> bool {
    output == filter_code_points(input)
}

/// What the exec functions need of the input: positions and a few code points past one
/// fit in a `usize`.
pub open spec fn input_requires(input: Seq<u32>) -> bool {
    input.len() + 8 <= usize::MAX
}

/// Contract for `next_token`: the spec's "consume a token" at `pos`.
pub open spec fn next_token_ensures(
    input: Seq<u32>,
    pos: int,
    unicode_ranges_allowed: bool,
    token: Token,
    next: int,
) -> bool {
    (token, next) == consume_a_token(input, pos, unicode_ranges_allowed)
}

/// Contract for `tokenize`: the spec's "tokenize".
pub open spec fn tokenize_ensures(input: Seq<u32>, tokens: Seq<Token>) -> bool {
    tokens == tokenize(input)
}

} // verus!
