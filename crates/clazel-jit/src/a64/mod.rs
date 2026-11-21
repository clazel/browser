//! The LIR → A64 back end (docs/phases/jit.md item J.9, second half). It
//! mirrors the x86-64 back end in the crate root, module for module, with the
//! A64 differences listed in [`spec`]'s header. Like the root, it was written
//! contract first (CLAUDE.md rule 3): [`spec`], [`contract`] and [`api`] came
//! in their own commit, before any template.
//!
//! - [`spec`]: **what the back end is about.** The state relation between a
//!   LIR state and an A64 machine state, the frame layout (the A64 ABI of
//!   `clazel-codecheck` fixes where the code may write), the exit sequence.
//!   Read its header first: it lists the modelling choices.
//! - [`contract`]: the refinement statements (a template's A64 code, run under
//!   `clazel-a64`'s `step` from a related state, reaches a state related to
//!   LIR's `eval`), and the emitter's contracts.
//! - [`api`]: the contract-only trait [`api::Backend`].
//!
//! The templates and their proofs follow in the next commit; this module's
//! documentation then says what is proven and what is not.

pub mod api;
pub mod contract;
pub mod spec;
