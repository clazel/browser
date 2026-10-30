//! The DOM node tree as an arena (Phase 4 item 4.8): the tree the HTML
//! parser builds and every later phase reads.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: nodes, the arena, `wf`, and the DOM §4.2.3 mutation
//!   algorithms the parser calls.
//! - [`contract`]: what the executable arena is proven to satisfy.
//! - [`exec`]: the executable arena, `Arena`, proven to meet the contracts.
//! - [`lemmas`]: the acyclicity witness is the ancestor chain, and every
//!   operation keeps `wf` and does what its DOM steps say.
//! - [`mutation_lemmas`]: the theorems on small concrete arenas, the kill
//!   certificates of `mutations.json`.
//! - [`independent`], [`independent_equivalence`]: a second, same-text
//!   transcription of DOM §4.2.3 "insert" and "remove", proven equal to the
//!   spec's on the parser's calls.

pub mod contract;
pub mod exec;
pub mod independent;
pub mod independent_equivalence;
pub mod lemmas;
pub mod mutation_lemmas;
pub mod spec;
