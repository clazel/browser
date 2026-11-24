//! **The A64 instance of the confinement theorem** (jit.md exit criterion 2,
//! item J.6, for A64): the same statement as `super::machine::confinement`,
//! over `clazel-a64`'s semantics and `crate::a64`'s acceptance spec.
//!
//! - [`instance`]: the A64 machine: configuration, machine-level invariant,
//!   observations, and the [`super::machine::Machine`] instance. Statement
//!   only (CLAUDE.md rule 3: it is committed before the proof).
//!
//! The A64 proof, complete for every case, is in the other modules: [`frame`]
//! (what `execute` leaves alone, and `mem_set`/`mem_read`), [`reads`] (a
//! step's outcome depends only on the read area), [`flags`] (carry and zero
//! after `adds` and `cmp`), [`chain`] (the units the scan reaches), [`infra`]
//! (the invariant under a step), [`steps`] (the exit sequence and single
//! instructions) and [`check`] (the bounds check); [`proof`] puts them
//! together ([`proof::theorem_a64`], [`proof::theorem_a64_runs`]), and
//! [`sanity`] shows the hypotheses are satisfiable. See `instance`'s header
//! for the A64 modelling choices. No axiom is used.

/// The A64 acceptance spec, `clazel-a64`'s semantics and every module of this
/// directory, re-exported under the name `spec` so that the modules import all
/// of it as `use super::spec::*` (the one ghost import CLAUDE.md allows next
/// to `vstd::prelude::*`). The modules that hold only ghost code are
/// re-exported under `cfg(verus_only)`, the cfg the workspace lets guard ghost
/// imports.
pub mod spec {
    pub use crate::a64::spec::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::chain::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::check::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::flags::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::frame::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::infra::*;
    pub use crate::confine::a64::instance::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::proof::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::reads::*;
    #[cfg(verus_only)]
    pub use crate::confine::a64::steps::*;
    pub use crate::confine::machine::*;
}

pub mod chain;
pub mod check;
pub mod flags;
pub mod frame;
pub mod infra;
pub mod instance;
pub mod proof;
pub mod reads;
pub mod sanity;
pub mod steps;
