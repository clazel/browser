//! The **second x86-64 validator** (jit.md item J.6, "Independent
//! transcription"): a dataflow analysis, to be proven to accept only what the
//! first validator ([`crate::validate`]) accepts.
//!
//! This commit is the contract only (CLAUDE.md rule 3): the theorem
//! statement, in [`contract`], and the contract-only trait, in [`api`]. The
//! implementation is the next commit.
//!
//! - [`contract`]: the second validator's `requires` and `ensures`, and the
//!   lemma that the `ensures` means "accepts only what the first accepts".
//! - [`api`]: the contract-only trait [`api::DataflowValidator`].

/// The x86-64 acceptance spec, re-exported under the name `spec` so that the
/// modules of this directory import it as `use super::spec::*` (the one
/// ghost import CLAUDE.md allows next to `vstd::prelude::*`).
pub mod spec {
    pub use crate::spec::*;
}

pub mod api;
pub mod contract;
