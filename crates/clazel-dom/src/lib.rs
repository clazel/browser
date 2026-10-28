//! The DOM node tree as an arena (Phase 4 item 4.8): the tree the HTML
//! parser builds and every later phase reads.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: nodes, the arena, `wf`, and the DOM §4.2.3 mutation
//!   algorithms the parser calls.
//! - [`contract`]: what the executable arena is proven to satisfy.

pub mod contract;
pub mod spec;
