//! ECMA-404 JSON text to values, as ECMA-262 `JSON.parse` constructs them,
//! and `JSON.stringify`'s string quoting.
//!
//! Specs: ECMA-404 (The JSON Data Interchange Syntax) and ECMA-262 §25.5†
//! (a section number marked † is written from memory, not read at a pinned
//! commit; `docs/phases/phase-7.md` explains the mark).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a transcription of the grammar, the value construction and
//!   QuoteJSONString. This is the part a human must check.
//! - [`tree`]: the executable value tree and its mathematical meaning.
//! - [`contract`]: what the executable parser and quoter are proven to
//!   satisfy.
//! - [`parse`] and [`quote`]: the executable parser and quoter, and their
//!   proofs.
//! - [`examples`]: a few cases evaluated on the spec; [`lemmas`]: facts
//!   about the spec (and the home of the mutation certificates).

pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod parse;
pub mod quote;
pub mod spec;
pub mod tree;
