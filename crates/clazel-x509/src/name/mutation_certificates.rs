//! Separate module host for Name DER mutation certificates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Marker makes this host module selectable by the mutation verifier.
pub open spec fn certificate_host() -> bool { true }

}
