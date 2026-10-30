//! Contracts for the executable search (`exec.rs`), in terms of `spec.rs`
//! and P7's `verifier.rs`.
//!
//! - `search_ensures`: the executable search returns exactly
//!   `spec::search`, and the steps it examined, recorded as it examines
//!   them, are exactly `spec::examined_steps`: a prefix of
//!   `spec::search_order`, in order. This is the obligation P7 left to P9,
//!   that the search examines the order the budget is judged on.
//! - `verify_server_chain_ensures`: the executable verifier returns exactly
//!   `spec::verify_server_chain`, which meets P7's
//!   `verifier::verify_server_chain_ensures` on `spec::server_chain_order`
//!   (`theorems::meets_verifier_contract`).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The search with `budget` on the leaf and pool of a chain: `out` is
/// `spec::search`, and `examined`, the steps examined, is
/// `spec::examined_steps`.
pub open spec fn search_ensures(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
    out: Result<super::super::verifier::Validated, super::super::spec::PathError>, examined: Seq<super::super::verifier::IssuerStep>,
) -> bool {
    &&& out == super::spec::search(environment, anchors, pool, leaf, reference, now, budget)
    &&& examined == super::spec::examined_steps(environment, anchors, pool, leaf, reference, now, budget)
}

/// The top-level verifier: `spec::verify_server_chain`, and P7's contract
/// with `spec::server_chain_order`.
pub open spec fn verify_server_chain_ensures(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64, out: Result<super::super::verifier::Validated, super::super::spec::PathError>,
) -> bool {
    &&& out == super::spec::verify_server_chain(environment, anchors, presented, reference, now)
    &&& super::super::contract::verify_server_chain_contract(environment, anchors, presented, reference, now,
        super::spec::server_chain_order(environment, anchors, presented, now), out)
}

} // verus!
