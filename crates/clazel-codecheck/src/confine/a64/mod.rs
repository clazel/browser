//! **The A64 instance of the confinement theorem** (jit.md exit criterion 2,
//! item J.6, for A64): the same statement as `super::machine::confinement`,
//! over `clazel-a64`'s semantics and `crate::a64`'s acceptance spec.
//!
//! - [`instance`]: the A64 machine: configuration, machine-level invariant,
//!   observations, and the [`super::machine::Machine`] instance. Statement
//!   only (CLAUDE.md rule 3: it is committed before the proof).
//!
//! The A64 proof (when present) is in the other modules; see `instance`'s
//! header for the A64 modelling choices.

/// The A64 acceptance spec, `clazel-a64`'s semantics and every module of this
/// directory, re-exported under the name `spec` so that the modules import all
/// of it as `use super::spec::*` (the one ghost import CLAUDE.md allows next
/// to `vstd::prelude::*`). The modules that hold only ghost code are
/// re-exported under `cfg(verus_only)`, the cfg the workspace lets guard ghost
/// imports.
pub mod spec {
    pub use crate::a64::spec::*;
    pub use crate::confine::a64::instance::*;
    pub use crate::confine::machine::*;
}

pub mod instance;
