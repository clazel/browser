//! The JavaScript lexer for Clazel's Phase 7 browser (phase-7.md item 7.2).
//!
//! Spec: ECMA-262, 2026 edition, §11.1, §12 and Annex B.1.1, at commit
//! `0248456c758431e4bb8e5d26333ff1865123c9cd` (`SPEC-PIN.md`).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a transcription of the lexical grammar, the goal symbol a
//!   parameter, and the longest-input-element rule.
//! - [`contract`]: what the executable lexer must be proven to satisfy.
//! - [`api`]: the token types and the contract-only trait [`api::JsLexer`].
//! - [`exec`]: the executable lexer. Its totality and span coverage are
//!   proven; its agreement with [`spec`] (the rest of [`contract`]) is
//!   tested, not proven, so it does not implement [`api::JsLexer`] yet
//!   (see the module's header for exactly what is proven).
//! - [`independent`]: a second transcription of part of the lexical grammar
//!   from UAX #31 and ECMA-262 Annex A in closed form; [`equivalence`] proves
//!   it equal to [`spec`] on every input it covers.
//! - [`unicode`], [`unicode_data`]: `ID_Start` and `ID_Continue` above
//!   U+007F, from a table generated from Unicode 18.0.0. The spec leaves
//!   them uninterpreted, and nothing ties the two.

pub mod api;
pub mod contract;
pub mod equivalence;
pub mod examples;
pub mod exec;
pub mod independent;
pub mod lemmas;
pub mod scan_proofs;
pub mod spec;
pub mod string_proofs;
pub mod unicode;
pub mod unicode_data;
