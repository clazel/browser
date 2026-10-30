//! Chain building (design §2.6): the order in which the search examines
//! candidate issuers, the candidate it returns, and the verdict on a
//! presented chain. This is the `order` that P7's
//! `verifier::verify_server_chain_ensures` leaves as a parameter.
//!
//! Sources: RFC 4158 (Internet X.509 PKI: Certification Path Building,
//! September 2005, informational; guidance only, it states no
//! requirement), <https://www.rfc-editor.org/rfc/rfc4158>; mozilla::pkix
//! `lib/mozpkix/lib/pkixbuild.cpp` (NSS `master`, read 2026-10-29), as in
//! `verifier.rs`; BoringSSL `pki/path_builder.cc` (`main`, read 2026-10-29),
//! the path builder Chrome uses.
//!
//! The search, in one paragraph: a depth-first search upward from the leaf,
//! on names only. At each node (the pool indices chosen so far, the top
//! first) it examines every candidate issuer of the top certificate, anchors
//! in table order and then pool certificates in message order. A
//! name-chained anchor completes a candidate; a name-chained pool
//! certificate is pushed and searched above, before the next issuer is
//! examined. The result is the first candidate, in that order, that
//! `verifier::candidate_verdict` accepts, among the first `budget` steps.
//!
//! Modelling choices, each marked (=) where both browsers do the same, (R)
//! where it is stricter or more restrictive than one of them, and (I) where
//! it is our choice:
//! - **Depth first, from the target (=).** RFC 4158 §1.3 calls this forward
//!   path building, "from the target certificate to a trust anchor", and
//!   §1.2 suggests "a depth first tree traversal". mozilla::pkix's
//!   `BuildForward` recurses on each potential issuer before trying the
//!   next; BoringSSL's `CertPathIter` keeps a stack of per-certificate issuer
//!   iterators, which is the same traversal.
//! - **Anchors before pool certificates at each node (=).** RFC 4158 §3.5.15:
//!   "Certificates whose issuer exactly matches a trust anchor subject DN
//!   have priority." BoringSSL sorts trusted issuers first
//!   (`TrustAndKeyIdentifierMatchToOrder`); Firefox's trust domain returns
//!   root candidates before intermediates. So a server that sends a copy of
//!   its root gets the short path (anchor -> ...) before the long one
//!   (anchor -> root copy -> ...).
//! - **Anchors in table order, pool certificates in message order (I).**
//!   BoringSSL sorts the remaining issuers by key-identifier match, then
//!   self-issued, then validity dates; Firefox takes its trust domain's
//!   order. Neither changes *whether* a valid path is found (both, and this
//!   search, examine every name-chained issuer until the budget runs out),
//!   only which one is found first and which chains exhaust the budget. We
//!   use the inputs' own orders, which need no extra ranking rule.
//! - **A step is P7's `verifier::step_name_chained` (=, R as there).** The
//!   loop check is by pool index: a certificate already on the path is not
//!   examined again. RFC 4158 §2.4.2 suggests disallowing "the same public
//!   key and subject name pair from being repeated", and both browsers'
//!   loop checks compare names and keys, not indices (BoringSSL: subject,
//!   subjectAltName and SubjectPublicKeyInfo). Those checks would prune
//!   candidates that `verifier::some_candidate_valid` counts, so this search
//!   does not make them; a path through two certificates with the same DER
//!   is refused by `spec::process` ("A certificate MUST NOT appear more than
//!   once"). Listed for Alex in the P9 report.
//! - **No de-duplication of candidate issuers (I).** BoringSSL drops a
//!   candidate issuer whose DER equals an earlier one; design §2.6 proposed
//!   the same. Here a duplicate is a further step, counted by the budget, so
//!   that every name-chained path is reached (`theorems::candidates_complete`).
//! - **The budget counts steps (=).** `verifier::build_budget()`, checked
//!   before each step (mozilla::pkix's "if (buildForwardCallBudget == 0)").
//!   `search` takes the budget as a parameter so that examples can use a
//!   small one; `verify_server_chain` uses `verifier::build_budget()`.
//! - **First valid (=).** The search stops at the first candidate that is
//!   valid. Both browsers return the first path that verifies in their order.
//! - **The error when no candidate is valid (I).** The first candidate's
//!   error, or `UnknownIssuer` when the order completes no candidate at all
//!   (design §2.6 step 6). This is the most specific diagnosis in the
//!   common single-path case (an expired intermediate reports `Expired`, as
//!   Firefox's `SEC_ERROR_EXPIRED_ISSUER_CERTIFICATE` does).
//! - **Work.** Name chaining checks no signature. `verifier::candidate_verdict`
//!   checks the profile and the comparison bound before §6.1, and §6.1
//!   checks the links from the anchor down and stops at the first that
//!   fails, so a link is verified only when every link above it verified
//!   (Firefox's own order: `VerifySignedData` after the recursive
//!   `BuildForward` succeeds).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The order (design §2.6)
// ---------------------------------------------------------------------------

/// The `i`-th candidate issuer at every node: the anchors in table order,
/// then the pool certificates in message order.
pub open spec fn issuer_at(anchors: Seq<super::super::parsed::spec::Anchor>, i: nat) -> super::super::verifier::Issuer {
    if i < anchors.len() { super::super::verifier::Issuer::Anchor(i) } else { super::super::verifier::Issuer::Pool((i - anchors.len()) as nat) }
}

/// The steps the search examines at the node `path` (the pool indices
/// chosen so far, the top first, as in `verifier::IssuerStep`), from the
/// `i`-th candidate issuer on, in order.
pub open spec fn steps_from(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    path: Seq<nat>, i: nat,
) -> Seq<super::super::verifier::IssuerStep>
    decreases environment.max_intermediates - path.len(), anchors.len() + pool.len() - i
{
    if path.len() > environment.max_intermediates || i >= anchors.len() + pool.len() { seq![] }
    else {
        let step = super::super::verifier::IssuerStep { path, issuer: issuer_at(anchors, i) };
        // The remaining candidate issuers of this node.
        let rest = steps_from(environment, anchors, pool, leaf, path, i + 1);
        // A candidate issuer that is not name-chained is not a step.
        if !super::super::verifier::step_name_chained(environment, anchors, pool, leaf, step) { rest }
        else { match step.issuer {
            // An anchor completes the candidate `(a, path)`.
            super::super::verifier::Issuer::Anchor(_) => seq![step] + rest,
            // A pool certificate is pushed, and its issuers are searched
            // before the next candidate issuer of this node (depth first).
            super::super::verifier::Issuer::Pool(j) => seq![step] + steps_from(environment, anchors, pool, leaf, seq![j] + path, 0) + rest,
        }}
    }
}

/// The whole order: every step of the search from the leaf, before the
/// budget truncates it.
pub open spec fn search_order(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
) -> Seq<super::super::verifier::IssuerStep> {
    steps_from(environment, anchors, pool, leaf, seq![], 0)
}

// ---------------------------------------------------------------------------
// The first valid candidate
// ---------------------------------------------------------------------------

/// `step` completes a candidate that `verifier::candidate_verdict` accepts.
pub open spec fn step_valid(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    step: super::super::verifier::IssuerStep, reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> bool {
    match super::super::verifier::step_candidate(step) {
        Some(candidate) => super::super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
        None => false,
    }
}

/// The index of the first step of `order[from..to]` that completes a valid
/// candidate.
pub open spec fn first_valid_from(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, from: int, to: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> Option<nat>
    decreases to - from
{
    if from < 0 || from >= to || from >= order.len() { None }
    else if step_valid(environment, anchors, pool, leaf, order[from], reference, now) { Some(from as nat) }
    else { first_valid_from(environment, anchors, pool, leaf, order, from + 1, to, reference, now) }
}

/// The error of the first candidate that `order[from..]` completes.
pub open spec fn first_candidate_error(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    order: Seq<super::super::verifier::IssuerStep>, from: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> Option<super::super::spec::PathError>
    decreases order.len() - from
{
    if from < 0 || from >= order.len() { None }
    else { match super::super::verifier::step_candidate(order[from]) {
        Some(candidate) => match super::super::verifier::candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now) {
            Err(e) => Some(e),
            Ok(_) => first_candidate_error(environment, anchors, pool, leaf, order, from + 1, reference, now),
        },
        None => first_candidate_error(environment, anchors, pool, leaf, order, from + 1, reference, now),
    }}
}

/// The search with at most `budget` steps: the first valid candidate among
/// the first `budget` steps of `search_order`; else `BuildBudgetExhausted`
/// when the order has more steps than that; else the first candidate's
/// error, or `UnknownIssuer` when there is no candidate.
pub open spec fn search(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
) -> Result<super::super::verifier::Validated, super::super::spec::PathError> {
    let order = search_order(environment, anchors, pool, leaf);
    match first_valid_from(environment, anchors, pool, leaf, order, 0, budget as int, reference, now) {
        Some(k) => match super::super::verifier::step_candidate(order[k as int]) {
            Some(candidate) => match super::super::verifier::candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now) {
                Ok(key) => Ok(super::super::verifier::Validated { anchor: candidate.anchor, path: candidate.path, leaf_spki: key }),
                // Not reached: `step_valid` holds of `order[k]`.
                Err(e) => Err(e),
            },
            // Not reached: `step_valid` holds of `order[k]`.
            None => Err(super::super::spec::PathError::UnknownIssuer),
        },
        None => if order.len() > budget { Err(super::super::spec::PathError::BuildBudgetExhausted) }
            else { match first_candidate_error(environment, anchors, pool, leaf, order, 0, reference, now) {
                Some(e) => Err(e),
                None => Err(super::super::spec::PathError::UnknownIssuer),
            }},
    }
}

/// How many steps the search with `budget` examines: up to and including
/// the first valid one, or all of them up to the budget.
pub open spec fn examined_count(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
) -> nat {
    let order = search_order(environment, anchors, pool, leaf);
    match first_valid_from(environment, anchors, pool, leaf, order, 0, budget as int, reference, now) {
        Some(k) => k + 1,
        None => if order.len() > budget { budget } else { order.len() },
    }
}

/// The steps the search with `budget` examines, in order: a prefix of
/// `search_order`.
pub open spec fn examined_steps(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, pool: Seq<Option<super::super::parsed::spec::PathCert>>, leaf: super::super::parsed::spec::PathCert,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime, budget: nat,
) -> Seq<super::super::verifier::IssuerStep> {
    search_order(environment, anchors, pool, leaf)
        .take(examined_count(environment, anchors, pool, leaf, reference, now, budget) as int)
}

// ---------------------------------------------------------------------------
// The presented chain
// ---------------------------------------------------------------------------

/// The verdict on a presented chain (design §2.6): its inputs
/// (`verifier::chain_inputs`), then the search with the production budget.
pub open spec fn verify_server_chain(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64,
) -> Result<super::super::verifier::Validated, super::super::spec::PathError> {
    match super::super::verifier::chain_inputs(presented, now) {
        Err(e) => Err(e),
        Ok(inputs) => search(environment, anchors, inputs.pool, inputs.leaf, reference, inputs.now,
            super::super::verifier::build_budget()),
    }
}

/// The order `verifier::verify_server_chain_ensures` judges the budget on:
/// `search_order` of the chain's inputs (empty when they are refused).
pub open spec fn server_chain_order(
    environment: super::super::verifier::Environment, anchors: Seq<super::super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>, now: u64,
) -> Seq<super::super::verifier::IssuerStep> {
    match super::super::verifier::chain_inputs(presented, now) {
        Err(_) => seq![],
        Ok(inputs) => search_order(environment, anchors, inputs.pool, inputs.leaf),
    }
}

} // verus!
