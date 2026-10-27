//! ECDSA signature verification over NIST P-384, FIPS 186-5 §6.4.2.
//!
//! **Specification only so far.** This crate has no executable code: no
//! field arithmetic, no point code and no `verify` function exist yet. What
//! is here is the part a person reviews, the meaning of "a valid ECDSA
//! P-384 signature", written in Verus, and the contract the later
//! implementation must meet.
//!
//! This is public-key *verification* only: the key, the signature and the
//! digest are all public, so there is no constant-time requirement and no
//! side-channel claim. Signing and any private-key operation are out of
//! scope.
//!
//! - [`spec`]: a step-by-step transcription of FIPS 186-5 §6.4.2, with the
//!   routines it defers to (SP 800-186 Appendices D.1 and F.1, SEC 1
//!   §2.2.1, §2.3, §3.2.2.1 and §4.1.4), the P-384 domain parameters, and a
//!   toy curve for evaluated examples.
//! - [`contract`]: what the executable `verify` will be proven to satisfy.
//! - [`examples`]: known answers, proven by evaluating the spec.
//! - [`axioms`]: the six calls into fiat-crypto, each an axiom.
//! - [`field`]: the field arithmetic over fiat-crypto, and its contracts.
//! - [`certificates`]: the host module for mutation kill certificates
//!   (empty until `mutations.json` exists).

pub mod axioms;
pub mod certificates;
pub mod contract;
pub mod examples;
pub mod field;
pub mod spec;
