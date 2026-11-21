//! **The validator's theorem** (jit.md exit criterion 2, item J.6): every
//! execution of an accepted blob, started at an accepted entry with the
//! context invariant, only loads and stores inside the regions it was handed,
//! leaves only through the exit sequence, executes no system instruction and
//! does not write the reserved registers.
//!
//! - [`machine`]: the statement, once, over an abstract [`machine::Machine`].
//! - [`a64`]: the A64 instance of the same statement (its own module tree).
//! - [`x64`]: the x86-64 instance: configuration, machine-level invariant,
//!   observations. Statement only.
//! - The x86-64 proof, [`x64proof`], from: [`frame`] (what `effect` leaves
//!   alone), [`reads`] (a step's outcome depends only on the read area),
//!   [`flags`] (carry and zero after `add` and `cmp`), [`chain`] (the units
//!   the scan reaches), [`infra`] and [`pos`] (the invariant under a step),
//!   [`steps`] (the exit sequence and single instructions) and [`check`] (the
//!   bounds check). [`sanity`] shows the hypotheses are satisfiable.
//!
//! The statement was committed before the proof (CLAUDE.md rule 3). Read
//! [`machine`]'s header for exactly what it says and does not say, and
//! [`x64`]'s for the x86-64 modelling choices. The proof is complete for
//! x86-64: [`x64proof::theorem_x64`] and [`x64proof::theorem_x64_runs`]. It
//! uses no axiom. A64's, over the same statement, is in [`a64`]
//! ([`a64::proof::theorem_a64`] and [`a64::proof::theorem_a64_runs`]), also
//! with no axiom. The crate's tier is unchanged: nothing
//! here counts toward a tier until CI's full verification is green
//! (CLAUDE.md rule 7).

/// The x86-64 acceptance spec and every module of this directory, re-exported
/// under the name `spec` so that the modules import all of it as
/// `use super::spec::*` (the one ghost import CLAUDE.md allows next to
/// `vstd::prelude::*`: ghost items look unused to a normal build). The modules
/// that hold only ghost code are re-exported under `cfg(verus_only)`, the cfg
/// the workspace lets guard ghost imports.
pub mod spec {
    #[cfg(verus_only)]
    pub use crate::confine::chain::*;
    #[cfg(verus_only)]
    pub use crate::confine::check::*;
    #[cfg(verus_only)]
    pub use crate::confine::flags::*;
    #[cfg(verus_only)]
    pub use crate::confine::frame::*;
    #[cfg(verus_only)]
    pub use crate::confine::infra::*;
    pub use crate::confine::machine::*;
    #[cfg(verus_only)]
    pub use crate::confine::pos::*;
    #[cfg(verus_only)]
    pub use crate::confine::reads::*;
    #[cfg(verus_only)]
    pub use crate::confine::steps::*;
    pub use crate::confine::x64::*;
    pub use crate::spec::*;
}

pub mod a64;
pub mod chain;
pub mod check;
pub mod flags;
pub mod frame;
pub mod infra;
pub mod machine;
pub mod pos;
pub mod reads;
pub mod sanity;
pub mod steps;
pub mod x64;
pub mod x64proof;
