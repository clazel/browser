//! The contract-only API of the A64 validator: a trait with no implementation,
//! so Verus accepts it with no escape hatch (CLAUDE.md rule 4), the pattern of
//! [`crate::api`]. The implementation (a later commit of J.6) implements it,
//! or replaces it with a free function whose `requires` and `ensures` are the
//! same predicates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The A64 validator, with its contract.
pub trait A64Validator {
    /// Whether `blob`, entered at the byte offsets `entries`, is accepted
    /// (see [`crate::a64::spec::accepted`]). Reads the bytes once, left to
    /// right, and never panics, whatever the bytes are.
    fn validate(blob: &[u8], entries: &[usize]) -> (ok: bool)
        requires
            crate::a64::contract::validate_requires(blob@, entries@),
        ensures
            crate::a64::contract::validate_ensures(blob@, entries@, ok),
    ;
}

} // verus!
