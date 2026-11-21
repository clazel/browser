//! The **A64 validator** (jit.md item J.6), the counterpart of the x86-64 one
//! in the crate root. Its modules mirror the root's, with the same names:
//!
//! - [`spec`]: **what an accepted blob is.** The checks of jit.md J.6 as spec
//!   functions over the instruction subset of `clazel-a64`. Read its header
//!   first: it lists where A64 differs from x86-64 and fixes the A64 ABI (the
//!   reserved registers, the context register, the region table, the
//!   bounds-check and exit sequences).
//! - [`contract`]: what the validator must be proven to satisfy.
//! - [`api`]: the contract-only trait [`api::A64Validator`] (no
//!   implementation).
//! - [`examples`]: instruction sequences (and one byte sequence) that are
//!   accepted and refused, proven by evaluating the spec.
//! - [`lemmas`]: general facts proven about the spec. They are what the kill
//!   certificates of `mutations.json` cite.

pub mod api;
pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod spec;
