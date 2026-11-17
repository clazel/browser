//! The JavaScript parser for Clazel's Phase 7 browser (phase-7.md item 7.3): the
//! AST, the specification of what a correct parse is, and the parser's contract.
//!
//! Spec: ECMA-262, 2026 edition, §12.10 and §13 to §16 (and the early errors and
//! Annex B.3 syntax they bring), at commit
//! `0248456c758431e4bb8e5d26333ff1865123c9cd` (`SPEC-PIN.md` of
//! `clazel-js-lexer`). Tier: see `[package.metadata.clazel]` in `Cargo.toml`
//! and `docs/VERIFICATION.md`.
//!
//! This is the first half of item 7.3 (CLAUDE.md rule 3, contracts before code):
//! there is no parser yet.
//!
//! - [`ast`]: the arena AST, with spans, its node kinds named after the
//!   productions of the standard.
//! - [`spec`]: a transcription of the syntactic grammar as a relation between an
//!   AST and a token stream, automatic semicolon insertion, the early errors, and the
//!   recursion limit. What it covers and leaves out is listed at the top of the
//!   file.
//! - [`contract`]: what the executable parser must be proven to satisfy.
//! - [`api`]: the contract-only trait [`api::JsParser`].
//! - [`examples`]: a few small proven facts about the spec.

pub mod api;
pub mod ast;
pub mod contract;
pub mod examples;
pub mod spec;
