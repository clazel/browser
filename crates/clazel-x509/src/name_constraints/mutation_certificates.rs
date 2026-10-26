//! Separate module host for NameConstraints mutation certificates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Marker function gives the mutation runner a selectable verifier module.
pub open spec fn certificate_host() -> bool { true }

}
