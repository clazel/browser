//! DEFLATE (RFC 1951) and zlib (RFC 1950) decoding.
//!
//! Specs: RFC 1951, "DEFLATE Compressed Data Format Specification version
//! 1.3", May 1996 (<https://www.rfc-editor.org/rfc/rfc1951>), and RFC 1950,
//! "ZLIB Compressed Data Format Specification version 3.3", May 1996
//! (<https://www.rfc-editor.org/rfc/rfc1950>). Both are fixed documents, so
//! the pin is the RFC number; SHA-256 of the plain-text files as served by
//! rfc-editor.org on 2026-11-16: RFC 1951
//! `5ebf4b5b7fe1c3a0c0ab9aa3ac8c0f3853a7dc484905e76e03b0b0f301350009`, RFC 1950
//! `8f0475a5c984657bf26277f73df9456c9b97f175084f0c1748f1eb1f0b9b10b9`.
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a transcription of the two RFCs as pure functions of the whole
//!   input. This is the part a human must check against the standards.
//! - [`contract`]: what each executable function is meant to satisfy.
//! - [`lemmas`]: facts proven about the spec; [`examples`]: the RFC's own
//!   worked examples, evaluated.

pub mod adler;
pub mod adler_proofs;
pub mod contract;
pub mod examples;
pub mod huffman;
pub mod lemmas;
pub mod lemmas_bounded;
pub mod lemmas_usable;
pub mod oneshot;
pub mod spec;
pub mod stream;
