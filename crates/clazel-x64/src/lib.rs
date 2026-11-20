//! The x86-64 instruction-set subset the JIT emits (docs/phases/jit.md item J.3).
//!
//! This is the first half of item J.3: the primary spec, written before any
//! encoder or decoder (CLAUDE.md rule 3).
//!
//! - [`spec`]: the **primary transcription**, from the ACL2 `x86isa` model
//!   (`tests/data/acl2-x86isa`): the machine state, the semantics of every
//!   instruction of the subset, and the canonical encoding.
//!
//! - [`contract`]: what the encoder and decoder must be proven to satisfy.
//! - [`api`]: the contract-only trait [`api::X64Codec`] (no implementation).
//!
//! The independent transcription, from Intel's SDM, is written by another
//! session that does not read [`spec`]; it is not here yet.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod api;
pub mod contract;
pub mod decoder;
pub mod decoder_exec;
pub mod decoder_proofs;
pub mod encoder;
pub mod examples;
pub mod spec;
