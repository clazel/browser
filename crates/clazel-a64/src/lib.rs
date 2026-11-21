//! The A64 (64-bit Arm) instruction-set subset the JIT emits (docs/phases/jit.md item J.4).
//!
//! This is the first half of item J.4: the primary spec, written before any
//! encoder or decoder (CLAUDE.md rule 3).
//!
//! - [`spec`]: the **primary transcription**, from the Sail Arm model
//!   (`tests/data/sail-arm`, itself translated from Arm's ASL): the machine
//!   state, the semantics of every instruction of the subset, and the
//!   canonical encoding.
//! - [`examples`]: encodings and results evaluated against the spec.
//! - [`contract`]: what the encoder and decoder must be proven to satisfy.
//! - [`api`]: the contract-only trait [`api::A64Codec`] (no implementation).
//!
//! The independent transcription, from the Arm Architecture Reference
//! Manual's prose, is written by another session that does not read
//! [`spec`]; it is not here yet.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod api;
pub mod contract;
pub mod examples;
pub mod spec;
