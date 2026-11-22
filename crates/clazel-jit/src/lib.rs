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
//! **The JS front end is [`front`]** (item J.10): bytecode → LIR, a proof per
//! op that the LIR refines `clazel-js-vm`'s `step`. It stops at LIR, so it
//! holds for both back ends. Its header says which ops are lowered and proven
//! and which are not.
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
//! # Control flow (the second slice, x86-64 only)
//!
//! Written contract first like the first ([`cfspec`], [`cfcontract`] in
//! their own commit; the statement was refined while proving, see the PR).
//! The source language is [`cfspec::Node`] (void blocks only), the statement
//! is [`cfcontract::cf_refines`] (a forward simulation over a run with jumps,
//! [`cfspec::reaches`]: `Normal`, `Branch` to a label's address, `Exit`).
//!
//! - **Proven, no axiom, no assumption:**
//!   - the static analysis [`cfspec::cf_flow`] is sound for LIR's `eval`
//!     ([`cfheight`]);
//!   - composition over `then`, `block`, `loop` and `if`
//!     ([`cfcompose::lemma_then`], [`cfblock::lemma_block`],
//!     [`cfblock::lemma_loop`], [`cfif::lemma_if`]), and the leaves `br`
//!     (a `jmp`), `br_if` (condition test and `jcc`), `exit` **with
//!     operands** and a straight-line instruction ([`cfleaf`], [`cfexit`],
//!     [`cfop`]);
//!   - by induction over the program, **every templated node's code refines
//!     it** ([`cfproofs::lemma_ctmpl_refines`]), with every `jmp` and `jcc`
//!     displacement a 32-bit number ([`cfproofs::labels_fit`]) and every
//!     instruction in the subset ([`cfvalid`]);
//!   - **the memory instructions** `bounds_check`, `load` and `store`
//!     ([`cfmem`], [`cfmemops`]): the code is the validator's own
//!     bounds-check sequence (`clazel_codecheck::spec::check_seq`, run by
//!     [`cfcheckrun`]) around the access, with the two exits going to a stub
//!     after the access ([`cftemplates::mem_code`]); the access reads and
//!     writes through `mem_rel` ([`cfmemrel`], [`cfmemacc`]); the check
//!     fails exactly when LIR's `bounds_check` exits (and where a load or
//!     store is `Stuck` nothing is claimed);
//!   - **`br_table`** ([`cfbrt`]): a compare-and-`je` chain and a `jmp` to
//!     the default, by induction on the entry;
//!   - that the validator's access rule admits the access the template
//!     makes ([`cfmemvalid::lemma_access_accepted`]).
//! - **The emitter** [`cfemit::emit_cf_blob`] is **proven equal to the
//!   templates**: [`cfcontract::emit_cf_blob_ensures`] is its postcondition.
//!   The bytes are the encoding of [`cftemplates::ctmpl`] (with the return
//!   label at the end) and the exit sequence, and it answers `None` exactly
//!   when [`cftemplates::cf_prog_ok`] refuses, so every emitted blob refines
//!   its program ([`cfemit::lemma_emitted_refines`], with
//!   [`cfproofs::lemma_ctmpl_refines`]). No signed arithmetic is needed:
//!   positions are `usize`, a backward displacement is `!(end - target - 1)`
//!   on a `u32`. `tests/validator_cf.rs` additionally checks that the
//!   validator accepts every memory template, `br_table`, and 1500 generated
//!   programs with control flow and memory.
//! - **The validator accepts every emitted blob (proven)**
//!   ([`cfblobacc::theorem_blob_accepted`], carried by `emit_cf_blob` as a
//!   postcondition, with the exactness of its bytes
//!   [`cfblobacc::emitted_bytes`]): for every program with a translation,
//!   `clazel_codecheck::spec::accepted(blob, [0])`. The proof ([`cfblobacc`]'s
//!   header): the code is cut into the validator's units ([`cfunits`],
//!   [`cfaccept::utmpl`]: an exit sequence, the bounds-check sequence as
//!   `check_unit_at` recognizes it, single instructions that are neither a
//!   `ret` nor a `jcc 2`), the scan walks exactly those units
//!   ([`cfunits::lemma_scan_units`]) and accepts them whatever it knew
//!   ([`cfuacc`], [`cfuacc2`], with [`cfsimple`] for the straight-line
//!   templates): the access of a `load` or `store` is admitted because the
//!   base was loaded and the index checked just before, and no jump lands
//!   between ([`cfaccept::prot`]); every jump lands on a label or on a unit
//!   start ([`cfjt`], [`cfbs`]).
//! - **Not done:**
//!   - the corollary with `clazel-codecheck`'s confinement theorem (every
//!     emitted blob, run from an accepted entry with the context invariant,
//!     stays in its regions and leaves only through the exit): that theorem is
//!     not in this stack's base, so it is not stated here;
//!   - blocks with parameters or results (modelling choice 8 of [`cfspec`]).
//!
//! The A64 back end's control flow, memory and emitter are the same slice
//! over `clazel-a64`, proven likewise: see [`a64`].
//!
//! # The code cache and the page's bounds (J.11, first slice)
//!
//! Pure safe Rust, with nothing mapped and nothing entered (that waits for
//! `clazel-sys`'s code regions, open PR #272).
//!
//! - [`cache`]: the code cache, a byte-budgeted store of compiled blobs keyed
//!   by bytecode function id and version, generic over [`cache::Region`].
//!   **Proven in Verus (no axiom, no assumption):** the resident bytes are
//!   the sum of the regions' own lengths and never exceed the budget; keys
//!   are unique; a rejected insert changes nothing; an evicted region leaves
//!   the cache by value, and no resident key is an evicted one. See its
//!   header for the statement.
//! - [`tier`]: when to compile (entry and back-edge thresholds, with backoff
//!   per eviction), as plain functions with tests.
//! - [`limits`]: the hostile-page bounds (per-function size, per-page budget,
//!   compile quota, tracked functions), the [`limits::Fallback`] reasons and
//!   the measurement counters ([`limits::Stats`]; no clock is read).
//! - [`governor`]: the three together, with tests that a flood of compile
//!   requests stays within the budget (arithmetic on counters, tested, not
//!   proven).
//!
//! # What is not (of the first slice)
//!
//! - **That the validator accepts every blob of the first slice's own
//!   emitter** (`emit::X64Backend`) is checked by `tests/validator.rs` (every
//!   template, 3000 generated programs), not proven; the control-flow emitter
//!   is proven above, and covers straight-line programs (a `then` chain of
//!   instructions).
//! - **Not covered by any template of the first slice:** the memory
//!   instructions, structured control flow, `br_table` and `exit` with
//!   operands (those are the second slice, above, for x86-64); `f64` arithmetic, comparison
//!   and conversion
//!   (LIR's `f64` operators are uninterpreted functions, so a refinement to
//!   SSE would need an axiom this crate does not add); rotates (the subset
//!   has no rotate instruction); a frame beyond 31 slots (it needs the
//!   region frame and the bounds-check sequence on every access).
//! - **No tier is claimed.** `tier` stays 0 until CI's full verification of
//!   this crate is green (CLAUDE.md rule 7), and the crate has no independent
//!   transcription and no conformance suite, which
//!   tier 2 requires. The proofs are about the spec of `clazel-x64` and the
//!   semantics of `clazel-lir`, whose faithfulness is their crates' claim.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod a64;
pub mod agree;
pub mod alu;
pub mod api;
pub mod cache;
pub mod cfaccept;
pub mod cfalg;
pub mod cfblobacc;
pub mod cfblock;
pub mod cfbrt;
pub mod cfbs;
pub mod cfcheck;
pub mod cfcheckrun;
pub mod cfcompose;
pub mod cfcontract;
pub mod cfemit;
pub mod cfexit;
pub mod cfheight;
pub mod cfif;
pub mod cfjt;
pub mod cfleaf;
pub mod cflens;
pub mod cfmem;
pub mod cfmemacc;
pub mod cfmemflow;
pub mod cfmemlens;
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
pub mod front;
pub mod governor;
pub mod limits;
pub mod memlemmas;
pub mod mid;
pub mod proofs;
pub mod rel;
pub mod runseq;
pub mod skel;
pub mod spec;
pub mod steps;
pub mod templates;
pub mod tier;
pub mod tlemmas;
