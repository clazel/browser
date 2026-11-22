//! The contract-only API of the encoder and the decoder: a trait with no
//! implementation, so Verus accepts it with no escape hatch (CLAUDE.md rule
//! 4), the pattern of `clazel-x64`'s `api.rs`. The implementation (the
//! second half of J.4) implements it, or replaces it with free functions
//! whose `requires` and `ensures` are the same predicates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Encoder and decoder of the subset, with their contracts.
pub trait A64Codec {
    /// The canonical encoding of `i` (see [`crate::spec::encode`]).
    fn encode_instr(i: &Instr) -> (out: u32)
        requires
            crate::contract::encode_requires(*i),
        ensures
            crate::contract::encode_ensures(*i, out),
    ;

    /// Decodes one instruction word: the instruction, or `None` if the word
    /// is not the canonical encoding of an instruction of the subset.
    fn decode_instr(w: u32) -> (r: Option<Instr>)
        requires
            crate::contract::decode_requires(w),
        ensures
            crate::contract::decode_ensures(w, r),
    ;
}

} // verus!
