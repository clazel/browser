//! CSS style for Clazel's Phase 5 browser (phase-5.md items 5.6 and 5.7).
//!
//! [`values`] reads a declaration's component values, as `clazel-css` parsed them, into
//! the typed values of the properties of the subset, expands shorthands, and serializes
//! them as CSSOM does. Item 5.7's cascade will be the module `cascade`.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod values;
