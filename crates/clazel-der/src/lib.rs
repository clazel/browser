//! ASN.1 Distinguished Encoding Rules: the decoder and encoder that X.509
//! certificates (item 3.5b) and PKCS#1 signatures (item 3.5c) are built on.
//!
//! Spec: ITU-T X.690 (08/2015), "Information technology - ASN.1 encoding
//! rules: Specification of Basic Encoding Rules (BER), Canonical Encoding
//! Rules (CER) and Distinguished Encoding Rules (DER)", clause 8 as
//! restricted by clauses 10 and 11
//! (<https://www.itu.int/rec/T-REC-X.690-201508-I/en>).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.
//!
//! Strings are `Seq<u8>` in the spec and `&[u8]` in the executable code.
//! The decoder is a cursor: every reader takes the input, a position and an
//! end, reads one value at the position and returns where it ended.

pub mod contract;
pub mod decode;
pub mod encode;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod lemmas_oid;
pub mod lemmas_overread;
pub mod lemmas_tlv;
pub mod lemmas_typed;
pub mod spec;
pub mod termination;
