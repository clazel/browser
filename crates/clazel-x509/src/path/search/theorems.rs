//! The theorems about the search (design §3.5), **stated**: each is a spec
//! predicate that holds for every input, proven in `lemmas.rs` as
//! `lemma_<name>`. They were written with the spec, before the proofs.
//!
//! - `candidates_complete` (the design's `lemma_candidates_complete`):
//!   every name-chained simple path within the depth is completed by a step
//!   of `spec::search_order`, the order before the budget truncates it.
//! - `order_well_formed`: the order is one `verifier::verify_server_chain_ensures`
//!   accepts (every step name-chained, none twice).
//! - `thm_first_valid`: `Ok(v)` is a valid candidate completed by a step
//!   within the budget, and no earlier step completes a valid one;
//!   `BuildBudgetExhausted` means the budget ran out on the order; any other
//!   error means no candidate is valid at all.
//! - `meets_verifier_contract`: `spec::verify_server_chain` meets P7's
//!   `verifier::verify_server_chain_ensures` with `spec::server_chain_order`.
//!
//! Termination is not a predicate here: `spec::steps_from` and the
//! executable search carry `decreases` clauses (the depth still available,
//! then the candidate issuers still to examine), which Verus checks.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A candidate is name-chained (§6.1 (a), (b), by name): certificate 1's
/// issuer is the anchor's subject, and each later certificate's issuer is
/// the previous one's subject. (The part of `theorems::thm_anchored` that
/// does not mention signatures.)
pub open spec fn candidate_name_chained(
    anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert, candidate: super::super::verifier::Candidate,
) -> bool {
    let certs = super::super::verifier::candidate_certificates(pool, leaf, candidate);
    &&& certs[0].tbs.issuer_der == anchors[candidate.anchor as int].subject_der
    &&& forall|i: int| 0 < i < certs.len() ==> #[trigger] certs[i].tbs.issuer_der == certs[i - 1].tbs.subject_der
}

/// The step that completes `candidate`: its anchor, examined for its path.
pub open spec fn completing_step(candidate: super::super::verifier::Candidate) -> super::super::verifier::IssuerStep {
    super::super::verifier::IssuerStep { path: candidate.path, issuer: super::super::verifier::Issuer::Anchor(candidate.anchor) }
}

/// `lemma_candidates_complete`: every well-formed (within the depth, usable,
/// no index twice) name-chained candidate is completed by a step of the
/// whole order.
pub open spec fn candidates_complete(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    candidate: super::super::verifier::Candidate,
) -> bool {
    (super::super::verifier::candidate_well_formed(anchors, pool, candidate, environment.max_intermediates)
        && candidate_name_chained(anchors, pool, leaf, candidate)) ==>
        super::spec::search_order(environment, anchors, pool, leaf).contains(completing_step(candidate))
}

/// The order is well formed in P7's sense.
pub open spec fn order_well_formed(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
) -> bool {
    super::super::verifier::search_order_well_formed_from(environment, anchors, pool, leaf,
        super::spec::search_order(environment, anchors, pool, leaf), 0)
}

/// `thm_first_valid`, for every budget.
pub open spec fn thm_first_valid(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
) -> bool {
    let order = super::spec::search_order(environment, anchors, pool, leaf);
    match super::spec::search(environment, anchors, pool, leaf, reference, now, budget) {
        Ok(v) => exists|k: int| {
            &&& 0 <= k < order.len() && k < budget
            &&& #[trigger] order[k] == completing_step(super::super::verifier::Candidate { anchor: v.anchor, path: v.path })
            &&& super::super::verifier::candidate_verdict(environment, anchors, pool, leaf,
                    super::super::verifier::Candidate { anchor: v.anchor, path: v.path }, reference, now) == Ok::<Seq<u8>, super::super::spec::PathError>(v.leaf_spki)
            &&& super::super::verifier::no_valid_step_between(environment, anchors, pool, leaf, order, 0, k, reference, now)
        },
        Err(super::super::spec::PathError::BuildBudgetExhausted) =>
            super::super::verifier::budget_exhausted_at(environment, anchors, pool, leaf, order, budget, reference, now),
        Err(_) => forall|candidate: super::super::verifier::Candidate|
            !super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
    }
}

/// `spec::verify_server_chain` meets P7's contract on `spec::server_chain_order`.
pub open spec fn meets_verifier_contract(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64,
) -> bool {
    super::super::verifier::verify_server_chain_ensures(environment, anchors, presented, reference, now,
        super::spec::server_chain_order(environment, anchors, presented, now),
        super::spec::verify_server_chain(environment, anchors, presented, reference, now))
}

} // verus!
