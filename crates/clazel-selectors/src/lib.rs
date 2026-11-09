//! CSS selectors for Clazel's Phase 5 browser (phase-5.md item 5.5): Selectors Level 4
//! parsing from `clazel-css`'s component values, matching against an element of a
//! `clazel-dom` arena, specificity, and CSSOM serialization.
//!
//! - [`spec`]: the transcription of the standards.
//! - [`algorithm`]: the matching algorithm the exec code runs, as spec functions.
//! - [`contract`]: what the exec code is proven to satisfy, and the statements of the
//!   theorems about the spec.
//! - [`lemmas`]: the theorems, proven.
//! - [`exec_types`]: the parsed selectors in memory, and what they mean.
//! - [`exec_match`]: matching, with [`exec_element`] and [`exec_strings`] for what it asks
//!   of one element; [`exec_specificity`]: specificity.
//!
//! The crate also holds the vendored test data of item 5.1, under `tests/data/`.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod algorithm;
pub mod contract;
pub mod exec_element;
pub mod exec_match;
pub mod exec_specificity;
pub mod exec_strings;
pub mod exec_types;
pub mod lemmas;
pub mod spec;
