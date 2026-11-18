//! The JavaScript parser for Clazel's Phase 7 browser (phase-7.md item 7.3): the
//! AST, the specification of what a correct parse is, the parser's contract,
//! and the parser.
//!
//! Spec: ECMA-262, 2026 edition, §12.10 and §13 to §16 (and the early errors and
//! Annex B.3 syntax they bring), at commit
//! `0248456c758431e4bb8e5d26333ff1865123c9cd` (`SPEC-PIN.md` of
//! `clazel-js-lexer`). Tier: see `[package.metadata.clazel]` in `Cargo.toml`
//! and `docs/VERIFICATION.md`.
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
//! - [`exec`]: [`exec::parse`], the executable parser; [`parser`], [`expr`],
//!   [`stmt`], [`module`], [`cover`] and [`token`] are its recursive-descent
//!   grammar over `clazel-js-lexer`; [`early`] its early errors; [`check`] the
//!   arena check that is proven.

pub mod api;
pub mod ast;
pub mod check;
pub mod contract;
pub mod cover;
pub mod early;
pub mod examples;
pub mod exec;
pub mod expr;
pub mod module;
pub mod parser;
pub mod spec;
pub mod stmt;
pub mod token;
