//! The **second x86-64 validator** (jit.md item J.6, "Independent
//! transcription"): a dataflow analysis, proven to accept only what the first
//! validator ([`crate::validate`]) accepts.
//!
//! The contract ([`contract`], [`api`]) was committed first (CLAUDE.md rule
//! 3). The implementation, [`validate::validate`], is a different algorithm
//! from the first validator's single scan with per-unit facts:
//!
//! 1. [`targets`] flags every entry and jump target (the non-fall-through
//!    edges of the control-flow graph), verified.
//! 2. [`solve`] builds the **control-flow graph of basic blocks** and runs a
//!    **forward dataflow fixpoint** over a lattice of register facts (`Bot`,
//!    `Base(k)`, `Idx(k, n)`, `Top`; join at merges). It is *untrusted*: Verus
//!    proves only that it cannot panic or overflow and that it terminates.
//! 3. [`check`] **verifies the solver's answer as a certificate** against the
//!    spec: that it is a post-fixpoint, and that every memory access, branch
//!    target and reserved-register write is permitted by it. This is where
//!    the proof is, so a wrong solver can only make the validator refuse.
//!
//! # What is shared with the first validator
//!
//! The specification ([`crate::spec::accepted`], so the two cannot disagree
//! about *what* is accepted), the decoder (`crate::decode_all`, over
//! `clazel-x64`'s proven decoder), `crate::unit_exec`'s syntactic recognizers
//! (each proven equal to its spec function), and spec-level lemmas. Not shared:
//! `crate::validate`, `crate::scan_exec`, or the policy code of
//! `crate::unit_exec` (`plain_ok_e`, `access_ok_e`).
//!
//! # What is proven
//!
//! **Soundness**: [`validate::validate`] returns `true` only if the blob is
//! `accepted`, hence only if the first validator accepts it
//! ([`contract::lemma_accepts_only_what_first_accepts`]). **Not** completeness:
//! see [`contract`]. Tier is unchanged (CLAUDE.md rule 7).
//!
//! # Why the fixpoint is shallow
//!
//! The spec forgets every fact at an entry or jump target, so no fact flows
//! along a branch edge; the only edges that carry facts are fall-through
//! ones, and they form a chain. One pass settles it and the next confirms. A
//! solver that carried facts along jumps would be more precise than the spec,
//! and the checker would refuse its certificate.

/// The x86-64 acceptance spec, re-exported under the name `spec` so that the
/// modules of this directory import it as `use super::spec::*` (the one
/// ghost import CLAUDE.md allows next to `vstd::prelude::*`).
pub mod spec {
    pub use crate::spec::*;
}

pub mod api;
pub mod check;
pub mod contract;
pub mod solve;
pub mod targets;
pub mod validate;
