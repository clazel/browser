//! The JIT's back ends (docs/phases/jit.md item J.9), the x86-64 one first:
//! LIR → x86-64 with **no register allocation**. Every LIR local, and every
//! element of LIR's operand stack, is a frame slot; each LIR instruction is a
//! fixed template over the scratch registers `rax`, `rcx` and `rdx`, so each
//! template's proof is local.
//!
//! This is the first slice of J.9, and it is written contract first (CLAUDE.md
//! rule 3).
//!
//! - [`spec`]: **what the back end is about.** The state relation between a
//!   LIR state and an x86-64 machine state, the frame layout (the codecheck
//!   ABI fixes where the code may write), the straight-line source subset
//!   [`spec::Op`]. Read its header first: it lists the modelling choices.
//! - [`contract`]: the refinement statements (a template's x86-64 code,
//!   run under `clazel-x64`'s `step` from a related state, reaches a state
//!   related to LIR's `eval`), and the emitter's contracts.
//! - [`api`]: the contract-only trait [`api::Backend`].
//!
//! # Status
//!
//! Tier 0, and nothing is proven yet: this commit holds the statements only.
//! The templates, their proofs, the emitter and the validator test follow.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod api;
pub mod contract;
pub mod spec;
