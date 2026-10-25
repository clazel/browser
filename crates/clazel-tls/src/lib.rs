//! TLS 1.3 record layer and handshake message formats.
//!
//! Spec: RFC 8446 "The Transport Layer Security (TLS) Protocol Version
//! 1.3", August 2018 (<https://www.rfc-editor.org/rfc/rfc8446>), with
//! RFC 6066 §3 for `server_name`. Tier: see `[package.metadata.clazel]` in
//! `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! This crate is phase-3.md item 3.5d. It reads and writes bytes: the
//! presentation language, records, handshake messages, extensions and
//! alerts. [`schedule`] adds the SHA-256 key schedule over abstract crypto
//! parameters (part of 3.5e). [`transcript`] constructs the transcript and
//! CertificateVerify signature inputs. [`auth`] implements the initial
//! authentication flight and application-delivery gate. [`hello`] validates
//! ServerHello/HRR selections for the fixed TLS 1.3/X25519 profile, generates
//! ClientHello, retains retry/transcript state, and joins explicit key-exchange
//! providers to authentication. [`traffic`] installs handshake secrets in the
//! correct record directions and owns non-wrapping send/receive epochs. The
//! connection-I/O driver, production cryptography (3.5f), entropy sourcing and
//! X.509 validation remain to be built.
//!
//! - [`spec`]: a step-by-step transcription of the standard. Its header
//!   lists every modelling choice.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`reader`] and [`writer`]: the presentation language, executable.
//! - [`record`] and [`reassemble`]: the record layer (`read_record`, the
//!   nonce, padding, protecting and unprotecting a record over an
//!   [`record::Aead`]) and the reassembly of handshake messages.
//! - [`types`], [`extension`], [`handshake`] and [`encode`]: the messages
//!   and extensions, read and checked, and the messages written.
//! - [`lemmas_pl`], [`lemmas_record`], [`lemmas_ext`], [`lemmas_hs`],
//!   [`examples`] and [`examples_hs`]: facts proven about the spec: round
//!   trips in both directions, no over-read, bounded reservation, the
//!   reassembler's bound and prefix lemmas, and one concrete lemma per
//!   rule and per row of the §4.2 table.
//! - [`independent`]: a second transcription, of RFC 8446 Appendix B,
//!   proven to accept the same bytes on the class it states.

pub mod auth;
pub mod certificates;
pub mod contract;
pub mod encode;
pub mod examples;
pub mod examples_hs;
pub mod extension;
pub mod handshake;
pub mod hello;
pub mod independent;
pub mod lemmas_ext;
pub mod lemmas_hs;
pub mod lemmas_pl;
pub mod lemmas_record;
pub mod reader;
pub mod reassemble;
pub mod record;
pub mod schedule;
pub mod spec;
pub mod traffic;
pub mod transcript;
pub mod types;
pub mod writer;
