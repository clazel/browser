//! Chain building (design §2.6, P9): the deterministic, bounded search over
//! candidate paths that turns the verdict on one candidate
//! (`verifier::candidate_verdict`) into the verdict on a presented chain.
//!
//! - `spec`: the search order, the first-valid rule and the budget;
//! - `theorems`: what is claimed of them (completeness, first valid, the
//!   order is one `verifier::verify_server_chain_ensures` accepts), stated;
//! - `contract`: what the executable search is proven to meet;
//! - `lemmas`: the proofs of `theorems`, and the facts `exec` uses.

pub mod contract;
pub mod lemmas;
pub mod spec;
pub mod theorems;
