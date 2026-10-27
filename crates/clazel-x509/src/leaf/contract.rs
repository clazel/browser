//! Refinement contracts for partial leaf-certificate checks.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The executable result is exactly the composed partial-check model.
pub open spec fn check_leaf_certificate_ensures(
    input: Seq<u8>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime, policy: LeafPolicy,
    output: Option<PartialLeafChecks>,
) -> bool {
    super::spec::check_leaf_certificate(input, reference, now, policy) == output
}

} // verus!
