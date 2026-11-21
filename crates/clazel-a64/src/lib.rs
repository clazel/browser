//! The A64 (64-bit Arm) instruction-set subset the JIT emits (docs/phases/jit.md item J.4).
//!
//! The primary spec and the contracts were written first (CLAUDE.md rule 3);
//! this is the encoder and decoder that meet them, with their proofs.
//!
//! - [`spec`]: the **primary transcription**, from the Sail Arm model
//!   (`tests/data/sail-arm`, itself translated from Arm's ASL): the machine
//!   state, the semantics of every instruction of the subset, and the
//!   canonical encoding.
//! - [`examples`]: encodings and results evaluated against the spec.
//! - [`contract`]: what the encoder and decoder must be proven to satisfy.
//! - [`api`]: the contract-only trait [`api::A64Codec`], implemented by
//!   [`inverse::A64`].
//! - [`encoder`]: [`encoder::encode_instr`], proven to give the canonical
//!   encoding.
//! - [`classes`] and [`decoder`]: [`decoder::decode_instr`], proven to accept
//!   exactly the canonical encodings of the subset (a word's variant is found
//!   from its fixed bits, its fields are read, and the instruction is accepted
//!   only if it is valid and encodes back to the word).
//! - [`inverse`]: the encoder and decoder are inverse on the subset's 4-byte
//!   words, and the proofs that the canonical encoding is injective and fits
//!   32 bits (the two facts `contract.rs` leaves to this half).
//!
//! The independent transcription, from the Arm Architecture Reference
//! Manual's prose, is written by another session that does not read
//! [`spec`]; it is not here yet. The mutation tests of the encoder and
//! decoder are not here yet either, so the crate's `tier` stays 0.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod api;
pub mod classes;
pub mod contract;
pub mod decoder;
pub mod encoder;
pub mod examples;
pub mod inverse;
pub mod spec;
