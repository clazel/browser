//! The JIT's code validators (docs/phases/jit.md item J.6), the x86-64 one
//! first. The A64 validator and the second, independent x86-64 validator are
//! later work.
//!
//! This is the first part of item J.6: the specification of what the
//! validator accepts and the contract of its entry point, written before any
//! validator (CLAUDE.md rule 3).
//!
//! - [`spec`]: **what an accepted blob is.** The checks of jit.md J.6 as spec
//!   functions over the instruction subset of `clazel-x64`. Read its header
//!   first: it lists the modelling choices and the ABI the validator fixes
//!   (the context register, the region table, the bounds-check and exit
//!   sequences).
//! - [`contract`]: what the validator must be proven to satisfy.
//! - [`api`]: the contract-only trait [`api::Validator`] (no implementation).
//! - [`examples`]: instruction sequences (and one byte sequence) that are
//!   accepted and refused, proven by evaluating the spec.
//! - [`lemmas`]: general facts proven about the spec (a region access is a
//!   checked access, the region table is never written, ...). They are what
//!   the kill certificates of `mutations.json` cite.
//!
//! The decoder of untrusted bytes will be this crate's own (CLAUDE.md rule
//! 8); the only thing shared with `clazel-x64` is its specification of the
//! subset and its canonical encoding.
//!
//! # Status
//!
//! Tier 0. [`exec`] is an executable validator, but **unverified**: plain
//! Rust that follows the spec, tested (`tests/validator.rs`) and not proven
//! against [`contract`]. What is proven is in `clazel-x64`: the encoding is a
//! prefix code and its specification-level decoder is complete, which is what
//! the contract's completeness half assumes. The spec, the contract,
//! examples, lemmas and mutations are proven as before. The theorem of jit.md exit criterion 2 (an accepted blob
//! is confined) is not stated or proven here; see the end of [`spec`]'s
//! header.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod api;
pub mod contract;
pub mod examples;
pub mod exec;
pub mod lemmas;
pub mod spec;
