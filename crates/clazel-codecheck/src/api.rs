//! The contract-only API of the validator: a trait with no implementation,
//! so Verus accepts it with no escape hatch (CLAUDE.md rule 4), the pattern
//! of `clazel-x64`'s `api.rs`. The implementation (a later commit of J.6)
//! implements it, or replaces it with a free function whose `requires` and
//! `ensures` are the same predicates.
//!
//! jit.md J.0(a) has a `Validated` value that only this crate can build and
//! `clazel-sys`'s `enter` takes. Building it from a `true` result is a later
//! step, with the implementation: it is a wrapper around a blob for which
//! this function answered yes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The x86-64 validator, with its contract.
pub trait Validator {
    /// Whether `blob`, entered at the byte offsets `entries`, is accepted
    /// (see [`crate::spec::accepted`]). Reads the bytes once, left to right,
    /// and never panics, whatever the bytes are.
    fn validate(blob: &[u8], entries: &[usize]) -> (ok: bool)
        requires
            crate::contract::validate_requires(blob@, entries@),
        ensures
            crate::contract::validate_ensures(blob@, entries@, ok),
    ;
}

} // verus!
