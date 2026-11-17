//! LIR, the JIT's low-level intermediate representation (docs/phases/jit.md
//! item J.5): syntax, semantics and typing, shaped like WebAssembly.
//!
//! - [`syntax`]: types, values and instructions;
//! - [`spec`]: the semantics, `spec fn eval`, with the modelling choices
//!   listed at its top (read those first);
//! - [`typing`]: the typing judgment `tc`;
//! - [`soundness`]: the soundness theorem `tc_sound`, and `run_sound` for a
//!   whole function body;
//! - [`examples`]: small programs with proven properties.
//!
//! There is no back end and no front end. The crate depends only on `vstd`
//! and has no JavaScript-specific type (jit.md, "The instruction-set layer
//! knows nothing of JS").
//!
//! # What is proven
//!
//! - **Determinism and totality of the semantics.** `eval` is a total
//!   `spec fn`; it takes fuel, and running out is the outcome `OutOfFuel`.
//! - **Soundness of the typing** (`soundness::tc_sound`, proven, no axiom
//!   and no assumption): a well-typed instruction in a conforming state is
//!   never `Stuck`. In particular every `load` and `store` is in a region
//!   that exists and inside its bound, because only an `Idx` index types,
//!   and only `bounds_check` makes one.
//! - Concrete programs: typed, rejected when they should be, and evaluated.
//!
//! # What is only stated, or not covered
//!
//! - Nothing is stated-but-unproven in this crate.
//! - **Not covered:** the Wasm specification is not vendored, and its
//!   section numbers in the comments are from memory of release 2.0 (the
//!   instruction and operator names are exact); there is no independent
//!   transcription, no mutation file and no conformance suite, so the crate
//!   stays at tier 0 (`target-tier` 2 is jit.md's goal).
//!   `f64` arithmetic and conversions are uninterpreted functions of the bit
//!   patterns, so no property of IEEE rounding is proven here.
//! - Refinement by the back ends (J.9) and the front end (J.10) is future
//!   work; they will be stated against `eval`.
//!
//! # Coverage of the WebAssembly core instructions (jit.md J.5)
//!
//! A Wasm front end (a later phase) needs the instructions of Wasm core 2.0
//! §2.4. Present in LIR, each with the same meaning as in Wasm unless a note
//! says otherwise:
//!
//! - **Numeric, `i32` and `i64`:** `const`; `add`, `sub`, `mul`, `and`,
//!   `or`, `xor`, `shl`, `shr_s`, `shr_u`, `rotl`, `rotr`; `eqz`; `eq`, `ne`,
//!   `lt_s`, `lt_u`, `gt_s`, `gt_u`, `le_s`, `le_u`, `ge_s`, `ge_u`;
//!   `i32.wrap_i64`, `i64.extend_i32_s`, `i64.extend_i32_u`.
//! - **Numeric, `f64`:** `const`; `add`, `sub`, `mul`, `div`, `sqrt`, `neg`,
//!   `abs`; `eq`, `ne`, `lt`, `gt`, `le`, `ge`; `convert_i32_s`,
//!   `convert_i32_u`, `convert_i64_s`, `convert_i64_u`;
//!   `f64.reinterpret_i64`, `i64.reinterpret_f64`.
//! - **Parametric:** `drop`, `select` (the untyped form; operands of one
//!   type).
//! - **Variable:** `local.get`, `local.set`, `local.tee`.
//! - **Memory:** `i32.load`, `i64.load`, `f64.load`, `i32.store`,
//!   `i64.store`, `f64.store`, from a region, with the bounds check explicit
//!   (a Wasm trap becomes the `bounds_check` exit).
//! - **Control:** `nop`; `block`, `loop`, `if` with multi-value block types
//!   (parameters and results); `br`, `br_if`, `br_table`; `return` (a `br` to
//!   the outermost label); `unreachable` (an `exit`).
//!
//! **Gaps**, with what a Wasm front end would do about each:
//!
//! - **Integer bit counting and division:** `clz`, `ctz`, `popcnt`, `div_s`,
//!   `div_u`, `rem_s`, `rem_u`. The division family traps in Wasm (on zero,
//!   and on `INT_MIN / -1`); add them with an explicit exit on the trapping
//!   operands, as `bounds_check` does.
//! - **Sign-extension operators** (Wasm 2.0 `extend8_s`, `extend16_s`,
//!   `extend32_s`): expressible as `shl` then `shr_s`; add the instruction
//!   when a back end has a cheaper form.
//! - **`f64` rounding and sign operators:** `ceil`, `floor`, `trunc`,
//!   `nearest`, `min`, `max`, `copysign`. `min`, `max` and `copysign` are
//!   definable from the comparison and the bit operations; the rounding ones
//!   are uninterpreted functions of the bits, like `add`, when added.
//! - **Float-to-integer conversion:** `trunc_f64_{s,u}` (trapping) and
//!   `trunc_sat_f64_{s,u}`. The JS engine's `ToInt32` and checked
//!   double-to-int paths will need one of them.
//! - **`f32`**, with `demote`, `promote`, and `i32.reinterpret_f32`: LIR has
//!   no `f32` type (jit.md: "later `f32`").
//! - **Narrow memory access:** `load8_s`, `load8_u`, `load16_*`, `load32_*`,
//!   `store8`, `store16`, `store32`, and the `offset` and `align` immediates
//!   (a front end adds the offset to the index in `i64`, so the effective
//!   address is not computed modulo 2^32 or 2^33 as in Wasm). The access
//!   width becomes a field of `load` and `store`, and the type of `Idx`
//!   already carries a size.
//! - **Memory growth and bulk memory:** `memory.size`, `memory.grow`,
//!   `memory.fill`, `memory.copy`, `memory.init`, `data.drop`. The layout is
//!   a constant of one entry (jit.md: regions are passed afresh at each
//!   entry), so growth must be an `exit` and a re-entry with a new layout;
//!   fill and copy are loops over `load` and `store`, or an exit.
//! - **Globals:** `global.get`, `global.set`. A global is a slot of a region
//!   (a region of globals), reached with `load`/`store` at a constant index;
//!   no new instruction is needed, but the front end's mapping is untested.
//! - **Calls:** `call`, `call_indirect`, `return_call`: jit.md forbids calls
//!   from generated code. A Wasm front end inlines, or exits to the host
//!   with the arguments, and `call_indirect` is an exit that does the table
//!   lookup in Rust. This is the largest gap and fixes the design of a
//!   multi-function Wasm blob; this crate has one function body.
//! - **Reference types and tables:** `ref.null`, `ref.is_null`, `ref.func`,
//!   `table.*`, typed `select`. LIR has no reference types; tables are
//!   regions of `i64` and references would be indexes (jit.md, "heap
//!   references as arena indexes").
//! - **SIMD** (`v128`): no type, no instructions.
//! - **Stack-polymorphic code** after `br`, `br_table`, `return`,
//!   `unreachable`: Wasm accepts it (§3.3.8); LIR's typing rejects any
//!   instruction after one that cannot fall through, so a Wasm front end
//!   drops dead code before it lowers (which a one-pass lowering can do by
//!   tracking validity as Wasm's own validation algorithm does).
//! - **Nondeterminism:** Wasm leaves the NaN payload of float results, and
//!   the choice of `memory.grow` outcome, open. LIR fixes one choice
//!   (uninterpreted but deterministic functions), which refines Wasm.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod soundness;
pub mod spec;
pub mod syntax;
pub mod typing;
