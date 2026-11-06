//! An independent transcription of how an X.509 certificate is decoded and
//! how a host name is matched against it, written from the standards alone,
//! as evidence for this crate's other transcription (docs/VERIFICATION.md,
//! "Trust without reviewers"). A different session proved it equal to the
//! crate's decoders on a stated domain: `equivalence.rs`. This module has no
//! exec code.
//!
//! Sources, each pinned at the top of the file that uses it: ITU-T X.509
//! (10/2019), X.501 (10/2019), X.520 (10/2019), X.680, X.681 and X.690
//! (02/2021), and RFC 6125 with RFC 4985 for one object identifier. X.519,
//! X.411 and ISO 8601 were not read; the files say where that matters.
//!
//! **Not read while writing this module.** In `crates/clazel-x509/src`: every
//! `spec.rs`, `contract.rs`, `lemmas.rs`, `exec.rs`, `examples.rs`,
//! `matcher.rs`, `certificates.rs` and `theorems.rs` outside this directory,
//! and everything under `certificate/`, `tbs/`, `extensions/`, `name/`,
//! `name_constraints/`, `constraints/`, `policy_constraints/`, `spki/`,
//! `signature_algorithm/`, `time/`, `leaf/` and `path/`. Also
//! `crates/clazel-x509/mutations.json`, `crates/clazel-x509/README.md`,
//! `crates/clazel-x509/tests/`, `crates/clazel-crypto/src/chain/`,
//! `crates/clazel-crypto/src/join/`, `crates/clazel-der/src/`, and sections
//! 3.5a and 3.5b of `docs/phases/phase-3.md`. The author did read this
//! crate's `lib.rs`, whose header names RFC 5280, RFC 9525 and the absence of
//! a Common Name fallback.
//!
//! Nothing in the transcription imports another module of this crate, or
//! `clazel-der`; only `vstd`. The `equivalence*` files are the exception by
//! nature: they name both sides, and were written after it, by another
//! author.
//!
//! - `der`: X.690 and the X.680 types.
//! - `structures`: `Certificate` and what it holds.
//! - `extensions`: the standard extensions.
//! - `requirements`: the prose's "shall" clauses.
//! - `matching`: RFC 6125.
//! - `examples`: sanity checks that Verus evaluates.
//! - `equivalence`: the proof, with its domain and what it leaves unproven.
//!   `equivalence_der`, `_time`, `_name`, `_structures`, `_extensions` and
//!   `_tbs` are its layers, `_signature` compares the two signature
//!   algorithms, `_matching` compares `dns_match`, and `_examples` gives an
//!   input for each disagreement and one certificate inside the domain.
//! - `equivalence_values`, `_name_constraints`: the value decoders of
//!   `constraints/`, `policy_constraints/` and `name_constraints/`.
//! - `equivalence_frame`, `_path`: what `parse_path_cert` runs on every
//!   certificate, in both directions.
//! - `equivalence_requirements`: `requirements.rs`, predicate by predicate.
//! - `equivalence_host`: `certificate_matches_host` and every `MatchChoices`.
//! - `equivalence_exclusions`: what narrows `equivalence.rs`'s exclusions.
//! - `equivalence_coverage_examples`: an input for each of those differences.

pub mod der;
pub mod equivalence;
pub mod equivalence_coverage_examples;
pub mod equivalence_der;
pub mod equivalence_examples;
pub mod equivalence_exclusions;
pub mod equivalence_extensions;
pub mod equivalence_frame;
pub mod equivalence_host;
pub mod equivalence_matching;
pub mod equivalence_name;
pub mod equivalence_name_constraints;
pub mod equivalence_path;
pub mod equivalence_requirements;
pub mod equivalence_signature;
pub mod equivalence_structures;
pub mod equivalence_tbs;
pub mod equivalence_time;
pub mod equivalence_values;
pub mod examples;
pub mod extensions;
pub mod matching;
pub mod requirements;
pub mod structures;
