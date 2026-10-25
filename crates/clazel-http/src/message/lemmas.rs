//! Facts proven about the message spec. They are evidence that the
//! transcription is right (docs/SPEC-STYLE.md), and the two properties
//! [`super::contract`] states for an incremental parser:
//!
//! - [`theorem_monotone`]: more bytes never take back a decision, and a
//!   finished response stays the same response with the extra bytes after
//!   it ([`super::contract::monotone`]).
//! - [`theorem_no_early_decision`]: every proper prefix of the octets a
//!   response was parsed from is `Incomplete`
//!   ([`super::contract::no_early_decision`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Monotonicity of [`parse_response`] (`super::contract::monotone`).
pub proof fn theorem_monotone(input: Seq<u8>, more: Seq<u8>, request_is_head: bool)
    ensures
        super::contract::monotone(input, more, request_is_head),
{
}

/// No decision before the data (`super::contract::no_early_decision`).
pub proof fn theorem_no_early_decision(input: Seq<u8>, request_is_head: bool)
    ensures
        super::contract::no_early_decision(input, request_is_head),
{
}

} // verus!
