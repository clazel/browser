//! The contract-only API of the encoder and the decoder: a trait with no
//! implementation, so Verus accepts it with no escape hatch (CLAUDE.md rule
//! 4), the pattern of `clazel-js-lexer`'s `api.rs`. The implementation (the
//! second half of J.3) implements it, or replaces it with free functions
//! whose `requires` and `ensures` are the same predicates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Encoder and decoder of the subset, with their contracts.
pub trait X64Codec {
    /// The canonical encoding of `i` (see [`crate::spec::encode`]).
    fn encode_instr(i: &Instr) -> (out: Vec<u8>)
        requires
            crate::contract::encode_requires(*i),
        ensures
            crate::contract::encode_ensures(*i, out@),
    ;

    /// Decodes one instruction at the start of `bytes`: the instruction and
    /// its length, or `None` if the bytes do not begin with the canonical
    /// encoding of an instruction of the subset.
    fn decode_instr(bytes: &[u8]) -> (r: Option<(Instr, usize)>)
        requires
            crate::contract::decode_requires(bytes@),
        ensures
            crate::contract::decode_ensures(bytes@, r),
    ;
}

} // verus!
