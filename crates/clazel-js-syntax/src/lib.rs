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
//!
//! # What is proven, and what is not
//!
//! The recursive-descent parser and the early errors are plain Rust that
//! *proposes* an arena; [`check::finish`] is the only way out, and Verus proves
//! that it returns an [`ast::Ast`] only if the arena is well formed
//! ([`spec::ast_wf`]: the root is last, children come first, only the root is a
//! `Script` or `Module`, no node is garbage), every span is inside the source
//! text and every child's span inside its parent's ([`spec::spans_wf`]), and its
//! height is at most [`spec::MAX_DEPTH`]. [`check::finish`] runs in linear time
//! and cannot panic or overflow.
//!
//! Not proven, only tested (`tests/`): that an `Ok` arena is a derivation of a
//! token stream of the source text by the grammar of [`spec`] with no early
//! error ([`spec::is_valid_parse`]), and that an `Err` means there is no such
//! parse ([`contract::parse_ensures`]). So [`exec::parse`] does not implement
//! [`api::JsParser`], and the crate stays at Tier 0. The first steps towards
//! that proof are in [`arena_d`], a proven check of `spec::d` over the whole arena
//! against the tokens the parser consumed, for the productions it covers (every
//! statement and nearly every expression, function, class and pattern; the list is
//! at the top of the module, and 1568 of the 1568 vendored positive Test262 runs
//! are covered end to end), run by [`exec::parse_checked`]; and in [`derive`]: rule
//! lemmas that a node of the shape the parser builds is derived by [`spec::d`].
//! The check assumes the tokens are the lexer specification's, which the
//! executable lexer does not meet yet, and that inserted `;` are justified.
//! [`arena_e`] and [`arena_m`] cover the rest of the script grammar and every
//! `import` and `export` form. [`arena_early`] is the same for the early errors:
//! a proven check of `spec::early` over the arena for a growing set of rules (the
//! list is at the top of the module), run by [`exec::parse_checked_early`]; where
//! both checks say `Verified`, `spec::is_valid_parse` holds, modulo the assumptions.
//!
//! Where the parser differs from the specification, on purpose or not:
//!
//! - **Regular expression literals** are taken as valid
//!   (`IsValidRegularExpressionLiteral`, §13.2.7.1): `clazel-js-regexp` (item
//!   7.10) is not written. Test262 has 167 negative tests of their contents; they
//!   are the only vendored negative tests the parser does not reject.

pub mod api;
pub mod arena_d;
pub mod arena_e;
pub mod arena_early;
pub mod arena_m;
pub mod ast;
pub mod check;
pub mod contract;
pub mod cover;
pub mod derive;
pub mod early;
pub mod examples;
pub mod exec;
pub mod expr;
pub mod module;
pub mod parser;
pub mod spec;
pub mod stmt;
pub mod token;
