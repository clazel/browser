//! The contract-only API of the second x86-64 validator: a trait with no
//! implementation, so Verus accepts it with no escape hatch (CLAUDE.md rule
//! 4), the pattern of [`crate::api`]. The implementation (the next commit)
//! replaces it with a free function whose `requires` and `ensures` are the
//! same predicates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The second x86-64 validator, with its contract.
pub trait DataflowValidator {
    /// Whether `blob`, entered at the byte offsets `entries`, is accepted,
    /// by the dataflow analysis. A `true` answer implies
    /// [`crate::spec::accepted`]; a `false` one implies nothing. Never
    /// panics, whatever the bytes are.
    fn validate(blob: &[u8], entries: &[usize]) -> (ok: bool)
        requires
            super::contract::df_requires(blob@, entries@),
        ensures
            super::contract::df_ensures(blob@, entries@, ok),
    ;
}

} // verus!
