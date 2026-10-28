//! Separate host module for leaf-check mutation certificates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Marker that gives the mutation runner a verifier module to select.
pub open spec fn certificate_host() -> bool { true }

}
