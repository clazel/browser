//! The JIT's back ends (docs/phases/jit.md item J.9), the x86-64 one first:
//! LIR → x86-64 with **no register allocation**. Every LIR local, and every
//! element of LIR's operand stack, is a frame slot; each LIR instruction is a
//! fixed template over the scratch registers `rax`, `rcx` and `rdx`, so each
//! template's proof is local.
//!
//! This is the first slice of J.9: straight-line integer code. It was written
//! contract first (CLAUDE.md rule 3): [`spec`], [`contract`] and [`api`] came
//! in their own commit, before any template.
//!
//! **The A64 back end is [`a64`]**: the same design and the same slice over
//! `clazel-a64`'s machine, module for module (its header says what is proven
//! there and what differs). The rest of this header, and the modules below,
//! are the x86-64 one.
//!
//! # The statements
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
//! # The templates and their proofs
//!
//! - [`templates`]: the templates, as spec functions (`tmpl`, `code_of`).
//! - [`emit`]: the executable back end, [`emit::X64Backend`], proven equal to
//!   the templates and, through `clazel-x64`'s encoder, to their bytes.
//! - Proofs, bottom up: [`memlemmas`] (byte memory), [`steps`], [`alu`] and
//!   [`flags`] (one `x64::step` of each instruction form the templates use),
//!   [`runseq`] (running a list), [`mid`] (each template's register-only
//!   middle computes LIR's result), [`rel`], [`skel`] and [`agree`] (the
//!   loads-middle-store skeleton preserves the state relation), [`proofs`]
//!   (the refinement of each template, `lemma_op_refines`), [`compose`] (the
//!   program, `lemma_prog_refines`), [`exit`] (the exit sequence),
//!   [`tlemmas`] (templates are in the subset, and are what the emitter
//!   pushes).
//!
//! # What is proven (Verus, no axiom, no assumption)
//!
//! - **Each template refines its LIR instruction** ([`contract::refines`]),
//!   for: `nop`, `drop`, `t.const`, `local.get`, `local.set`, `local.tee`,
//!   `select`; `i32` and `i64` `add`, `sub`, `mul`, `and`, `or`, `xor`,
//!   `shl`, `shr_s`, `shr_u`, and the ten comparisons; `i32.eqz`,
//!   `i64.eqz`, `i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u`,
//!   `f64.neg`, `f64.abs` and the two `reinterpret`s (the last four are bit
//!   operations).
//! - **A straight-line program of them refines** the left-nested `then`
//!   chain ([`compose::lemma_prog_refines`]).
//! - **The exit sequence refines `exit c`** with no operands
//!   ([`contract::exit_refines`], [`exit::lemma_exit_refines`]).
//! - **The emitter returns exactly the template code, and its encoding**
//!   ([`contract::emit_body_ensures`], [`contract::emit_blob_ensures`]),
//!   and refuses (`None`) exactly the programs [`spec::prog_ok`] refuses.
//!
//! # What is not
//!
//! - **That the validator accepts every blob** is checked by
//!   `tests/validator.rs` (every template, 3000 generated programs), not
//!   proven.
//! - **Not covered by any template:** the memory instructions
//!   (`bounds_check`, `load`, `store`); structured control flow (`block`,
//!   `loop`, `if`, `br`, `br_if`, `br_table`) and so composition over it;
//!   `exit` with operands; `f64` arithmetic, comparison and conversion
//!   (LIR's `f64` operators are uninterpreted functions, so a refinement to
//!   SSE would need an axiom this crate does not add); rotates (the subset
//!   has no rotate instruction); a frame beyond 31 slots (it needs the
//!   region frame and the bounds-check sequence on every access).
//! - **No tier is claimed.** `tier` stays 0 until CI's full verification of
//!   this crate is green (CLAUDE.md rule 7), and the crate has no mutation
//!   file, no independent transcription and no conformance suite, which
//!   tier 2 requires. The proofs are about the spec of `clazel-x64` and the
//!   semantics of `clazel-lir`, whose faithfulness is their crates' claim.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod a64;
pub mod agree;
pub mod alu;
pub mod api;
pub mod cfalg;
pub mod cfblock;
pub mod cfcompose;
pub mod cfcontract;
pub mod cfheight;
pub mod cflens;
pub mod cfspec;
pub mod cfsteps;
pub mod cftemplates;
pub mod compose;
pub mod contract;
pub mod emit;
pub mod exit;
pub mod flags;
pub mod memlemmas;
pub mod mid;
pub mod proofs;
pub mod rel;
pub mod runseq;
pub mod skel;
pub mod spec;
pub mod steps;
pub mod templates;
pub mod tlemmas;
