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
//! # The templates and their proofs
//!
//! - [`templates`]: the templates, as spec functions (`tmpl`, `code_of`).
//! - [`emit`]: the executable back end, [`emit::A64Backend`], proven equal to
//!   the templates and, through `clazel-a64`'s encoder, to their bytes.
//! - Proofs, bottom up: [`memlemmas`] (byte memory), [`steps`] (the load and
//!   store of a frame slot), [`alu`], [`intops`], [`flags`] and [`bitfield`]
//!   (one `isa::step` of each instruction form the middles use, as numbers),
//!   [`runseq`] (running a list), [`mid`] and [`bitmid`] (each template's
//!   register-only middle computes LIR's result), [`rel`] and [`skel`] (the
//!   loads-middle-store skeleton preserves the state relation), [`proofs`] (the
//!   refinement of each template, `lemma_op_refines`), [`compose`] (the
//!   program, `lemma_prog_refines`), [`exit`] (the exit sequence), [`tlemmas`]
//!   (templates are in the subset, and are what the emitter pushes).
//!
//! # What is proven (Verus, no axiom, no assumption)
//!
//! - **Each template refines its LIR instruction** ([`contract::refines`]),
//!   for: `nop`, `drop`, `t.const`, `local.get`, `local.set`, `local.tee`,
//!   `select`; `i32` and `i64` `add`, `sub`, `mul`, `and`, `or`, `xor`,
//!   `shl`, `shr_s`, `shr_u`, and the ten comparisons; `i32.eqz`,
//!   `i64.eqz`, `i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u`,
//!   `f64.neg`, `f64.abs` and the two `reinterpret`s (the last four are bit
//!   operations). The same list as the x86-64 back end.
//! - **A straight-line program of them refines** the left-nested `then` chain
//!   ([`compose::lemma_prog_refines`]).
//! - **The exit sequence refines `exit c`** with no operands
//!   ([`contract::exit_refines`], [`exit::lemma_exit_refines`]).
//! - **The emitter returns exactly the template code, and its encoding**
//!   ([`contract::emit_body_ensures`], [`contract::emit_blob_ensures`]), and
//!   refuses (`None`) exactly the programs [`spec::prog_ok`] refuses.
//!
//! # Control flow and memory (the second slice)
//!
//! The A64 counterpart of the x86-64 second slice, written contract first
//! ([`cfspec`], [`cfcontract`], [`cftemplates`] in their own commit); the
//! source language [`crate::cfspec::Node`] and its analysis
//! ([`crate::cfspec::cf_flow`], sound for LIR's `eval`: [`crate::cfheight`])
//! are shared with x86-64. Differences: a branch is relative to its own
//! address and in words, so a label offset is a multiple of 4 and a
//! conditional branch reaches 1 MiB each way ([`cffit`]; the translation
//! refuses code above [`cftemplates::max_size`] bytes, `2^19`); exit codes are
//! 16 bits; there is no native stack word and no `create_undef`.
//!
//! - **Proven, no axiom, no assumption:**
//!   - composition over `then`, `block`, `loop` and `if` ([`cfcompose`],
//!     [`cfblock`], [`cfif`]) and the leaves `br` (`b`), `br_if` (`cbnz`),
//!     `exit` **with operands** and a straight-line instruction ([`cfleaf`],
//!     [`cfexit`], [`cfop`]);
//!   - **the memory instructions** `bounds_check`, `load` and `store`
//!     ([`cfmemops`]): the code is the validator's own bounds-check sequence
//!     (`clazel_codecheck::a64::spec::check_seq`, run by [`cfchk`]) around the
//!     access, with the two exits going to a stub after the access; the check
//!     fails exactly when LIR's `bounds_check` exits (where a `load` or
//!     `store` is `Stuck` nothing is claimed);
//!   - **`br_table`** ([`cfbrt`]): a `movz`, `cmp`, `b.eq` chain and a `b` to
//!     the default;
//!   - by induction over the program, **every templated node's code refines
//!     it, is in the subset, and every displacement fits its field**
//!     ([`cfproofs::lemma_ctmpl_refines`], [`cffit::labels_fit`]);
//!   - **the emitter** [`cfemit::emit_cf_blob`] is proven equal to the
//!     templates ([`cfcontract::emit_cf_blob_ensures`]); positions are words,
//!     displacements are formed without signed arithmetic;
//!   - the validator's access rule admits the access a memory instruction
//!     makes ([`cfmemvalid::lemma_load_access_accepted`]).
//!     `tests/validator_a64_cf.rs` checks that the A64 validator accepts every
//!     memory template, `br_table`, and 1500 generated programs with control
//!     flow and memory.
//! - **The validator accepts every emitted blob (proven)**
//!   ([`cfblobacc::theorem_blob_accepted`], carried by `emit_cf_blob` as a
//!   postcondition, with the exactness of its instructions
//!   [`cfblobacc::emitted_ins`]): for every program with a translation,
//!   `clazel_codecheck::a64::spec::accepted(blob, [0])`. The A64 counterpart
//!   of the x86-64 proof (see `crate::cfblobacc`): units ([`cfunits`],
//!   [`cfaccept`]: an exit sequence of 3, the bounds-check sequence of 7,
//!   single instructions), the scan over them ([`cfuacc`], [`cfuacc2`],
//!   [`cfsimple`]), and where branches land ([`cfjt`], [`cfbs`]).
//! - **Not done:** blocks with parameters or results; `f64` arithmetic;
//!   rotates; a frame beyond 31 slots.
//!
//! # What is not (of the first slice)
//!
//! - **That the A64 validator accepts every blob of the first slice's own
//!   emitter** is checked by `tests/validator_a64.rs` (every template, 3000
//!   generated programs), not proven; the control-flow emitter is proven
//!   above.
//! - **Not covered by any template:** `f64` arithmetic, comparison and
//!   conversion (LIR's `f64` operators are uninterpreted functions, so a
//!   refinement to `FADD` and the rest would need an axiom this crate does not
//!   add); rotates (`clazel-a64`'s subset has no `RORV`); a frame beyond 31
//!   slots (it needs the region frame and the bounds-check sequence on every
//!   access).
//! - **No tier is claimed** (`tier` stays 0): the crate has no independent
//!   transcription or conformance suite. The proofs are about the spec of
//!   `clazel-a64` and the semantics of `clazel-lir`, whose faithfulness is
//!   their crates' claim.

pub mod alu;
pub mod api;
pub mod bitfield;
pub mod bitmid;
pub mod cfaccept;
pub mod cfalg;
pub mod cfblobacc;
pub mod cfblock;
pub mod cfbrt;
pub mod cfbs;
pub mod cfchk;
pub mod cfcompose;
pub mod cfcontract;
pub mod cfemit;
pub mod cfexit;
pub mod cffit;
pub mod cfif;
pub mod cfjt;
pub mod cfleaf;
pub mod cflens;
pub mod cfmemops;
pub mod cfmemrel;
pub mod cfmemsteps;
pub mod cfmemvalid;
pub mod cfop;
pub mod cfproofs;
pub mod cfsimple;
pub mod cfspec;
pub mod cfsteps;
pub mod cftemplates;
pub mod cfuacc;
pub mod cfuacc2;
pub mod cfunits;
pub mod cfvalid;
pub mod compose;
pub mod contract;
pub mod emit;
pub mod exit;
pub mod flags;
pub mod intops;
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
