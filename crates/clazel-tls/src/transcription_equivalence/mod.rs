//! The clean-room transcription of RFC 8446 ([`crate::transcription`],
//! written by a session that never read this crate's spec) **proven equal**
//! to the crate's behaviour specs, one spec area per file. This is the
//! second half of the independent transcription that Tier 2 requires
//! (docs/VERIFICATION.md, "Trust without reviewers"); the first is
//! `transcription/` itself. Written by a third author, who read both.
//!
//! Every theorem is a `forall` over all inputs, under hypotheses that say
//! how the two sides' abstract primitives correspond. Where the two sides
//! disagree, the disagreement is a finding: it is either resolved (one side
//! fixed, with the reason at the spot, or an entry in `docs/ERRATA.md`), or
//! it is stated as a domain condition of the theorem with the reason, as
//! `clazel-x509`'s `path/independent_equivalence.rs` does. Nothing here
//! changes what either side means.
//!
//! How the transcription's modelling choices (its `mod.rs`, and #138) are
//! mapped:
//! - **Primitives are `spec_fn` fields** of `Primitives`. Each theorem takes
//!   the crate's parameters (`schedule::spec::Crypto`, `traffic::spec::Cipher`,
//!   ...) and a `Primitives`, and requires that the fields the two share are
//!   the same functions ([`schedule::crypto_agrees`] and the like).
//! - **Rejections are lists of failures.** A crate rejection with alert `a`
//!   matches a transcription rejection when `a` is `required_alert` of some
//!   failure in the list; acceptance is compared exactly.
//! - **`ClientError` carries `required_alert`.** The crate's results are
//!   alert bytes, so a transcription error is compared through
//!   `required_alert`.
//! - **Alerts chosen where the RFC names none** are compared as alerts like
//!   any other; where the two sides chose differently, the theorem's domain
//!   says so.
//!
//! Coverage, by crate spec area (status as of this commit):
//!
//! | Crate spec | Theorem | Status |
//! |------------|---------|--------|
//! | `schedule/spec.rs` | [`schedule::theorem_schedule_equivalence`] | proven |

pub mod schedule;
