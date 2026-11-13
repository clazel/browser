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
//! | `spec.rs` `ext_body_ok`, `auth/spec.rs` `request_filters_distinct` | [`bodies::lemma_cr_bodies`], [`bodies::lemma_ee_bodies`], [`hello::lemma_sh_bodies`], [`hello::lemma_hrr_bodies`] | proven for CertificateRequest (every block), EncryptedExtensions (the profile's offers), ServerHello and HelloRetryRequest (every block, inside the hello theorem); NewSessionTicket (every block, [`post_handshake::lemma_nst_bodies`]) |
//! | Appendix D.4 client CCS: `bootstrap_spec` before ClientHello2, `handshake_spec::needs_ccs`, `dispatcher_spec` `compatibility_ccs_record`/`protect_client_flight` | [`ccs::theorem_compatibility_ccs`] | partial: the bytes and the placement (once; before ClientHello2 after a retry, else before the encrypted flight), mode = non-empty session ID; tied to the transcription's stream (`middlebox::client_receive_stream`) before ClientHello2 by [`bootstrap::theorem_bootstrap_equivalence`]; and before the encrypted flight by [`dispatcher::theorem_dispatcher_equivalence`] (the crate's flight is D.4's record when owed and its sealed flight, the server's CCS dropped at a boundary on both sides) |
//! | `hello/spec.rs` (`validate`); `spec.rs` `read_server_hello` and the legacy preflight | [`hello::theorem_hello_equivalence`] | proven for every body, under the hypotheses that the transcription's ClientHello and retry record are the crate's profile ([`hello::sent_is_profile`], [`hello::retry_is_profile`]; both discharged for every state the crate's negotiation controller reaches, by [`client`] and [`negotiation`]); the two crate differences found are fixed (the HelloRetryRequest Random is examined first; the extensions floor of 6) |
//! | `hello/client_spec.rs` (the ClientHello sent) | [`client::theorem_client_hello_equivalence`] | proven: for every accepted configuration, the first ClientHello is the transcription's `build_client_hello` of the same inputs and meets `client_hello_conforms`; every ClientHello sent (any cookie) meets [`hello::sent_is_profile`] with the crate's own offers, discharging that hypothesis; and after every first HelloRetryRequest the crate accepts, the transcription accepts it, keeps [`hello::profile_retry_record`], and the crate's ClientHello2 is `second_client_hello` and meets `second_client_hello_conforms` ([`client::retry_agrees`]) |
//! | `hello/client_spec.rs` negotiation controller (`start`, `receive`: `validate`, `retry`, `established` and the transcript steps) | [`negotiation::theorem_negotiation_equivalence`] | proven: `start` agrees with `start_handshake` and sends its ClientHello; from agreeing states, on every body, the crate rejects exactly when the transcription aborts (alert in its list), retries exactly when it accepts a HelloRetryRequest (same ClientHello2, record version 0x0303, agreeing states again), and establishes exactly when it accepts the ServerHello (same share, transcripts agree); domain: the crate's resource policies (body, 4 MiB transcript, 4096-octet cookie: `internal_error`) |
//! | `hello/bootstrap_spec.rs` (the record layer around the controller: acknowledgement gate, CCS, fragments, alerts) | [`bootstrap::theorem_bootstrap_equivalence`] | proven for every whole record (`record_step`, which is `feed` on every framed record) against `middlebox::client_receive_stream`, from agreeing states: the start record (0x0301) and its acknowledgement, CCS, alerts, fragments, the ServerHello and HelloRetryRequest through the negotiation theorem, the CCS and ClientHello2 flight and its acknowledgement, which processes the messages coalesced after a HelloRetryRequest (`buffer_agrees`); stated differences: two faults in one record, the crate's caps (`internal_error`), the all-zero shared secret (crate refuses in `join`; with bytes after the ServerHello, each side names a different fault), ClientHello2 sent before a coalesced message's failure; streams in any chunks by [`framing::theorem_boot_stream`]; not covered: transport EOF |
//! | `traffic/handshake_spec.rs` (`start`) | [`dispatcher::lemma_start`] | proven: the handoff agrees with the transcription after it accepts the same ServerHello ([`dispatcher::accepts_server_hello`]; the ClientHello's signature schemes and the unset WAIT_EE fields are hypotheses until the driver) |
//! | `connection/framing_spec.rs` (with `spec.rs` `read_record`) | [`framing::theorem_framing_equivalence`] | proven for every stream and every chunking: the framer's caller is a function of the bytes ([`framing::frames`]), whose records are the first whole records of `receive_stream`'s division ([`framing::split`]), byte for byte; it waits exactly when the transcription waits on the same bytes; it fails on a whole record with its whole-record alert, or on a header alone ([`framing::early_reject`]: a type the mode does not allow; every completion is rejected by both with that alert, or [`framing::header_two_faults`]); lifted to the bootstrap, dispatcher and post-handshake machines over any chunking ([`framing::theorem_boot_stream`], [`framing::theorem_disp_stream`], [`framing::theorem_post_stream`]) |
//! | `connection/dispatcher_spec.rs` (`feed`, `acknowledge`) | [`dispatcher::theorem_dispatcher_equivalence`] | proven from agreeing states for every whole record (`receive_record`, which `feed` runs on each completed record): header, CCS, deprotection, alerts, application data, every handshake message of the server's flight (rejections by membership), the client's flight with D.4's CCS, and `acknowledge`, which reaches `post_handshake::post_agrees` (the theorems compose); domain: the key cap, the profile's offers, `chain_agrees`; stated differences: a message of the wrong type, a Finished out of place, two faults in a header, the 2^18 cap, the 4 MiB transcript cap refusing a message the transcription accepts (`dispatcher::transcript_cap`), the flight coalesced into one record, the peer's close_notify; streams in any chunks by [`framing::theorem_disp_stream`] (every record); not covered: transport EOF |
//! | `connection/post_handshake_spec.rs` | [`post_handshake::theorem_post_handshake_equivalence`] | proven from agreeing states for every whole record (NewSessionTicket, KeyUpdate, every other message type, application data, alerts, deprotection), `send_application` (at most 2^14 octets), `update_keys` and `close`, and the start; stated differences: the `update_requested` answer sent at once (`settle`), two faults in one record header, an exhausted receive epoch, the 2^18 handshake cap, application data above 2^14 octets; a stream composes record by record, and in any chunks by [`framing::theorem_post_stream`] (up to the first KeyUpdate the transcription owes, `settle`); not covered: the write-closed state (no transcription counterpart), transport EOF |
//! | `connection/driver_spec.rs` (with `driver_contract.rs`, which fixes `driver_exec::Driver`) | [`driver::theorem_driver_equivalence`] | proven end to end: from the configuration (the first ClientHello record against `start_client`), over any stream in any chunks with sends and closes interleaved, each operation's bytes sent, data delivered and status agree with the transcription's, across both handoffs; rejections compared by the record-level theorems; discharges `accepts_server_hello`'s start inputs, the all-zero shared secret and the profile offers; an owed KeyUpdate is carried through reads (the frame lemma) until the caller's next send, where the transcription catches up (`catches_up`); stated differences: early header rejection, the server's close_notify, ClientHello2 before a later failure, the coalesced client flight, the immediate KeyUpdate answer (`settles`, the comparison going on in the lag), a second `update_requested`, a failure or a close_notify while a KeyUpdate is owed (keys a generation apart), an exhausted epoch, data above 2^14 octets, a close during the handshake; the crate's caps (the 4 MiB transcript cap included) are rejections under `rejects_record`, so every record is compared; domain: the validators (with the 16 KiB key cap); not covered: transport EOF |
//! | `host/spec.rs`; the server_name of `hello/client_spec.rs` `extensions` | [`host::theorem_host_equivalence`] | proven for every host and every text naming it, no domain; and the crate accepts a `Dns` name exactly when the transcription calls it a hostname (RFC 2181 §11 labels since #139) |
//!
//! The disagreements found so far, and the coverage gaps, are listed in the
//! pull request that added this module.

pub mod auth;
pub mod auth_flight;
pub mod bodies;
pub mod bootstrap;
pub mod ccs;
pub mod client;
pub mod dispatcher;
pub mod driver;
pub mod extensions;
pub mod framing;
pub mod hello;
pub mod host;
pub mod keys;
pub mod messages;
pub mod negotiation;
pub mod post_handshake;
pub mod record;
pub mod schedule;
pub mod transcript;
