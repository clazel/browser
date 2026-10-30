//! Separate host for injected legacy ServerHello kill certificates.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// Keeps this separate module available as the injected certificate host.
pub open spec fn mutation_certificate_host() -> bool { true }
}
