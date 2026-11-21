//! The JavaScript lexer for Clazel's Phase 7 browser (phase-7.md item 7.2).
//!
//! Spec: ECMA-262, 2026 edition, §11.1, §12 and Annex B.1.1, at commit
//! `0248456c758431e4bb8e5d26333ff1865123c9cd` (`SPEC-PIN.md`).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! This is the first half of item 7.2: the spec and the contracts, with no
//! implementation (CLAUDE.md rule 3).
//!
//! - [`spec`]: a transcription of the lexical grammar, the goal symbol a
//!   parameter, and the longest-input-element rule.
//! - [`contract`]: what the executable lexer must be proven to satisfy.
//! - [`api`]: the token types and the contract-only trait [`api::JsLexer`].

pub mod api;
pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod spec;
