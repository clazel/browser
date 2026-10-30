//! ECDSA signature verification over NIST P-384, FIPS 186-5 §6.4.2.
//!
//! **Specification, field arithmetic, point arithmetic and `verify`.** What
//! is here is the part a person reviews, the meaning of "a valid ECDSA P-384
//! signature", written in Verus, the contract the implementation is proven
//! to meet, the field arithmetic modulo p and n (fiat-crypto's Montgomery
//! code behind six axioms, with the rest proven over them), and on top of
//! that the affine group law, the scalar product, the key decoding and
//! [`verify::verify`], each proven against [`spec`] over those six axioms and
//! nothing else. An independent transcription from SEC 1
//! ([`independent`]) is proven to accept exactly what [`spec`] accepts
//! ([`equivalence`]). The crate is still at tier 0: the mutations (53, all
//! certified), the conformance tests and the equivalence proof are in place,
//! and the tier is raised only after CI's full verification is green.
//! Conformance tests (Wycheproof, NIST CAVP) and a differential against
//! `ring` run in `tests/`.
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
//! - [`contract`]: what the executable `verify` is proven to satisfy, and
//!   [`point_contract`], the same for the group law, the scalar product, the
//!   key decoding and the digest's reduction.
//! - [`examples`]: known answers, proven by evaluating the spec.
//! - [`field`]: the field arithmetic, over fiat-crypto, with its contracts.
//! - [`point`]: affine points and SEC 1 §2.2.1's group law, and the key
//!   decoding (SEC 1 §2.3.4, SP 800-186 D.1.1.1).
//! - [`scalar`]: MSB-first double-and-add against `spec::scalar_mul`, and the
//!   digest's step 3 and reduction mod n.
//! - [`verify`]: FIPS 186-5 §6.4.2.
//! - [`independent`]: SEC 1 §4.1.4 transcribed without reading [`spec`], and
//!   [`equivalence`], the proof that the two accept the same signatures
//!   ([`equivalence::lemma_independent_equals_spec`]).
//! - [`primality`]: P-384's p is prime, by Pocklington certificates proven
//!   in Verus (the equivalence needs it).
//! - [`convert`] and [`lemmas`]: small conversions and the facts the proofs
//!   above use.
//! - [`axioms`]: the six calls into fiat-crypto, each an axiom.
//! - [`certificates`]: the host module for mutation kill certificates
//!   (empty until `mutations.json` exists).

pub mod axioms;
pub mod certificates;
pub mod contract;
pub mod convert;
pub mod equivalence;
pub mod examples;
pub mod field;
pub mod independent;
pub mod lemmas;
pub mod point;
pub mod point_contract;
pub mod primality;
pub mod scalar;
pub mod spec;
pub mod verify;
