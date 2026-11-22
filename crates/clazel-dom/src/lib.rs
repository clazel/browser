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
//! - [`ops_lemmas`]: the same for Phase 7 item 7.13's operations (validity,
//!   pre-insert, replace, replace all, clone, attribute changes).
//! - [`validity_lemmas`]: steps 5 and 6 of the validity checks enforce the
//!   children rules exactly.
//! - [`deep_clone_lemmas`]: deep "clone a node" (a worklist) meets its
//!   relational spec; what the relation says.
//! - [`deep_clone_size_lemmas`]: a deep clone adds exactly the subtree's size,
//!   and is refused only if the copy does not fit.
//! - [`host_acyclic_contract`]: what the raw insert and reparent need to keep
//!   `host_acyclic`.
//! - [`host_acyclic_lemmas`]: every operation keeps `host_acyclic`, the one
//!   thing `wf` does not say (no cycle through a template's host).
//! - [`host_acyclic_mutation_lemmas`]: the kill certificates of the
//!   mutations of the host-including ancestor check.
//! - [`deep_clone_size_mutation_lemmas`]: the kill certificates of the
//!   mutations of the size and refusal specs.
//! - [`ops_mutation_lemmas`]: the kill certificates of the mutations of those.
//! - [`mutation_lemmas`]: the theorems on small concrete arenas, the kill
//!   certificates of `mutations.json`.
//! - [`independent`], [`independent_equivalence`]: a second, same-text
//!   transcription of DOM §4.2.3 "insert" and "remove", proven equal to the
//!   spec's on the parser's calls.

pub mod contract;
pub mod deep_clone_lemmas;
pub mod deep_clone_mutation_lemmas;
pub mod deep_clone_size_lemmas;
pub mod deep_clone_size_mutation_lemmas;
pub mod exec;
pub mod independent;
pub mod independent_equivalence;
pub mod lemmas;
pub mod mutation_lemmas;
pub mod ops_lemmas;
pub mod ops_mutation_lemmas;
pub mod spec;
pub mod validity_lemmas;
pub mod validity_mutation_lemmas;
// Declared after every other module on purpose: the solver's behavior on the
// failing proofs of the validity mutations (mutations.json) depends on where
// these modules are declared, and they are slow to refute if these come first.
pub mod host_acyclic_contract;
pub mod host_acyclic_lemmas;
pub mod host_acyclic_mutation_lemmas;
