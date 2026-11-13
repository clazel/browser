//! CSS parsing for Clazel's Phase 5 browser (phase-5.md items 5.2 to 5.7).
//!
//! [`input`] is how a style sheet's bytes become code points, [`tokenizer`] is the CSS
//! tokenizer and [`parser`] the CSS parser, each proven equal to its spec. The crate also
//! holds the vendored test data of item 5.1, under `tests/data/`.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod input;
pub mod parser;
pub mod tokenizer;
