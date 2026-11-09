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
//! | `transcript/spec.rs` | [`transcript::theorem_transcript_equivalence`] | proven (accepted steps; the crate's size caps are policy) |
//! | `traffic/spec.rs`, record protection in `spec.rs` (TLSCiphertext, inner plaintext, nonce) | [`record::theorem_record_protection_equivalence`] | proven (live epoch; accepted sends; the header is the connection's) |
//! | `Certificate` and the `select` on `msg_type` in `spec.rs` (with vectors, extension blocks, the handshake header) | [`messages::theorem_certificate_select_equivalence`] | proven (syntax; the entries' extension rules are authentication's) |
//! | `hello/join_spec.rs` `derive`; `auth/spec.rs` Finished values; `dispatcher_spec.rs` `acknowledge` secrets | [`keys::theorem_handshake_keys_equivalence`] | proven (the key values; the state machines around them are not) |
//! | `auth/spec.rs` `step`, CertificateVerify and Finished | [`auth::theorem_auth_verify_finished_equivalence`] | proven |
//! | `auth/spec.rs` `step`, EncryptedExtensions, CertificateRequest, Certificate | [`auth_flight::theorem_auth_flight_equivalence`] | proven for the expected message type, extension bodies included ([`bodies`]); offers are the client's profile |
//! | `spec.rs` §4.2 extension-block rules | [`extensions::theorem_extension_rules_equivalence`] | proven |
//! | `spec.rs` `ext_body_ok`, `auth/spec.rs` `request_filters_distinct` | [`bodies::lemma_cr_bodies`], [`bodies::lemma_ee_bodies`] | proven for CertificateRequest (every block) and EncryptedExtensions (the profile's offers); ServerHello and HelloRetryRequest bodies with the hello, NewSessionTicket's with post-handshake |
//! | Appendix D.4 client CCS: `bootstrap_spec` before ClientHello2, `handshake_spec::needs_ccs`, `dispatcher_spec` `compatibility_ccs_record`/`protect_client_flight` | [`ccs::theorem_compatibility_ccs`] | partial: the bytes and the placement (once; before ClientHello2 after a retry, else before the encrypted flight), mode = non-empty session ID; not yet tied to the connection streams |
//! | `hello/spec.rs` (`validate`) | none | not started |
//! | `hello/client_spec.rs` (the ClientHello sent) | none | not started |
//! | `hello/bootstrap_spec.rs` | none | not started |
//! | `traffic/handshake_spec.rs` (`start`) | none | not started (its parts: `keys` and `record` above) |
//! | `connection/framing_spec.rs` | none | not started |
//! | `connection/dispatcher_spec.rs` (`feed`, `acknowledge`) | none | not started (its values: `keys` above) |
//! | `connection/post_handshake_spec.rs` | none | not started |
//! | `connection/driver_spec.rs` | none | not started |
//! | `host/spec.rs`; the server_name of `hello/client_spec.rs` `extensions` | [`host::theorem_host_equivalence`] | proven for every host and every text naming it; domain: a `Dns` name is a hostname by the transcription's LDH grammar (the two differ outside it, [`host::lemma_names_outside_the_grammar`]; open) |
//!
//! The disagreements found so far, and the coverage gaps, are listed in the
//! pull request that added this module.

pub mod auth;
pub mod auth_flight;
pub mod bodies;
pub mod ccs;
pub mod extensions;
pub mod host;
pub mod keys;
pub mod messages;
pub mod record;
pub mod schedule;
pub mod transcript;
