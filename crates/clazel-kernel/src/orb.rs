//! Opaque-response blocking for the kernel (phase-7.md item 7.16): whether
//! `clazel_fetch::orb`'s check lets a response through.
//!
//! [`orb_allows`] is part of the kernel's spec (`crate::spec` reads it in
//! `api_end` and `orb_end`). It is a `closed` function in a module of its
//! own so that no proof elsewhere carries the definitions of MIME type
//! parsing and sniffing it rests on: the solver never needs them to prove a
//! kernel theorem, and carrying them made the noninterference proofs run
//! out of time. [`lemma_orb_allows`] states its definition for the proofs
//! that do read it (the exec twin, the mutation lemmas).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// ORB lets `response` through: the opaque-response-safelist check
/// (`clazel_fetch::orb`) returns true. The check's last step, "determine if
/// response is JavaScript and not JSON", is not run: a response that reaches
/// it (`Verdict::JavaScriptCheck`) is blocked (listed in `crate::spec`).
pub closed spec fn orb_allows(response: clazel_http::message::spec::Response) -> bool {
    clazel_fetch::orb::spec::opaque_response_safelist_check(response) is Allowed
}

/// The definition of [`orb_allows`].
pub proof fn lemma_orb_allows(response: clazel_http::message::spec::Response)
    ensures
        orb_allows(response) == (clazel_fetch::orb::spec::opaque_response_safelist_check(response) is Allowed),
{
}

} // verus!
