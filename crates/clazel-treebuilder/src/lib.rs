//! The HTML tree builder (Phase 4 items 4.9 to 4.11): HTML §13.2.6's tree
//! construction as a one-token step over a `clazel-dom` arena, with the
//! tokenizer as a parameter.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: the transcription, split by section and insertion mode.
//! - [`invariant`]: `parser_wf`, the invariant of reachable parser states.
//! - [`contract`]: what the executable parser is proven to satisfy.
//! - [`independent`]: a second transcription of the insertion modes, from
//!   the W3C's HTML 5.2, proven equal where the documents agree.
//! - [`termination`]: `theorem_dispatch_total`, reprocessing ends.
//! - [`theorems`]: `theorem_actions_ordered`, the order of the actions; the
//!   document theorems, and `theorem_reachable_wf`, the document facts of
//!   every reachable parser.
//! - [`mutation_lemmas`]: concrete instances of the theorems, the kill
//!   certificates of `mutations.json`.
//! - [`reachable`]: `theorem_reachable`, the reachable-state invariant, and
//!   `theorem_reachable_stopped`, the modes of a stopped reachable parser.

pub mod contract;
pub mod exec;
pub mod independent;
pub mod invariant;
pub mod mutation_lemmas;
pub mod reachable;
pub mod spec;
pub mod termination;
pub mod theorems;
