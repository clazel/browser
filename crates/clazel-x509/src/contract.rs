//! Contracts for RFC 9525 service identity matching.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The matcher returns exactly the decision specified for the typed
/// reference and presented identifiers.
pub open spec fn identity_match_ensures(
    reference: ReferenceIdentity,
    presented: PresentedIdentity,
    result: bool,
) -> bool {
    result == service_identity_match(reference, presented)
}

} // verus!
