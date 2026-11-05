//! CSS parsing for Clazel's Phase 5 browser (phase-5.md items 5.2 to 5.7).
//!
//! [`tokenizer`] is the CSS tokenizer, proven equal to its spec. The parser is still to
//! come. The crate
//! also holds the vendored test data of item 5.1, under `tests/data/`.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod tokenizer;
