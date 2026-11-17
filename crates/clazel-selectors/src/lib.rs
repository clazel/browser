//! CSS selectors for Clazel's Phase 5 browser (phase-5.md item 5.5): Selectors Level 4
//! parsing from `clazel-css`'s component values, matching against an element of a
//! `clazel-dom` arena, specificity, and CSSOM serialization.
//!
//! - [`spec`]: the transcription of the standards.
//! - [`algorithm`]: the matching algorithm the exec code runs, as spec functions.
//! - [`contract`]: what the exec code is proven to satisfy, and the statements of the
//!   theorems about the spec.
//! - [`lemmas`]: the theorems, proven.
//! - [`examples`]: concrete selectors on a concrete document, evaluated on the spec; the
//!   kill certificates of `mutations.json`.
//! - [`exec_types`]: the parsed selectors in memory, and what they mean.
//! - [`exec_match`]: matching, with [`exec_element`] and [`exec_strings`] for what it asks
//!   of one element; [`exec_specificity`]: specificity. Both proven equal to the spec.
//! - [`exec_parse`]: "parse a selector", over the component values [`exec_items`] reads
//!   from `clazel-css`: checked by Verus for panics, overflow and termination only, **not
//!   yet proven equal to the spec**; its output passes [`exec_check`], which is proven,
//!   before it is returned. [`exec_serialize`]: CSSOM serialization, proven equal to the
//!   spec.
//!
//! - [`independent`]: a second transcription of parsing, matching and specificity, from the
//!   standard alone. [`independent_equivalence`] (specificity), [`independent_match`] (with
//!   [`independent_attr`]) and [`independent_parse`] prove it equal to [`spec`] on the
//!   selectors the two share.
//!
//! The crate also holds the vendored test data of item 5.1, under `tests/data/`.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod algorithm;
pub mod axioms;
pub mod contract;
pub mod examples;
pub mod exec_anb;
pub mod exec_check;
pub mod exec_element;
pub mod exec_grow;
pub mod exec_items;
pub mod exec_match;
pub mod exec_numbers;
pub mod exec_parse;
pub mod exec_serialize;
pub mod exec_specificity;
pub mod exec_steps;
pub mod exec_strings;
pub mod exec_types;
pub mod independent;
pub mod independent_attr;
pub mod independent_equivalence;
pub mod independent_match;
pub mod independent_parse;
pub mod lemmas;
pub mod spec;
