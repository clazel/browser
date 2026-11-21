//! **The validator's theorem** (jit.md exit criterion 2, item J.6): every
//! execution of an accepted blob, started at an accepted entry with the
//! context invariant, only loads and stores inside the regions it was handed,
//! leaves only through the exit sequence, executes no system instruction and
//! does not write the reserved registers.
//!
//! - [`machine`]: the statement, once, over an abstract [`machine::Machine`].
//! - [`x64`]: the x86-64 instance: configuration, machine-level invariant,
//!   observations. Statement only.
//!
//! The statement was committed before the proof (CLAUDE.md rule 3). Read
//! [`machine`]'s header for exactly what it says and does not say. Nothing is
//! claimed verified until the proof modules exist and CI's full verification
//! is green; the crate's tier is unchanged.

/// The x86-64 acceptance spec, re-exported under the name `spec` so that the
/// modules of this directory import it as `use super::spec::*` (the one
/// ghost import CLAUDE.md allows next to `vstd::prelude::*`).
pub mod spec {
    pub use crate::spec::*;
}

pub mod machine;
pub mod x64;
