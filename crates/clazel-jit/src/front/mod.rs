//! The JS front end (docs/phases/jit.md item J.10): bytecode → LIR, with a
//! proof per op that the LIR **refines `clazel-js-vm`'s `step`**. It sits
//! above LIR, so what it proves holds on both instruction sets: it stops at
//! LIR and needs nothing from the back ends' control flow.
//!
//! This is the first slice. It was written contract first (CLAUDE.md rule 3):
//! [`spec`] and [`contract`], the statement, came in their own commit, before
//! any lowering.
//!
//! # The statement
//!
//! - [`spec`]: **what the front end is about.** The relation between a
//!   bytecode machine state and a LIR state (the shared frame layout of
//!   phase-7.md "Shapes fixed here for the JIT": the value stack is LIR's
//!   region 0, the frame base is local 0), the exit protocol (the exit code
//!   names the handler, the operand is `pc`), and the per-op outcome a
//!   lowering must have. Read its header first: it lists the modelling
//!   choices, among them the one hypothesis about code outside this crate,
//!   `handler_complete` (not an axiom; this crate has no `axioms.rs`).
//! - [`contract`]: the refinement statement, [`contract::lowers`].
//!
//! # The lowerings and their proofs
//!
//! - [`lower`]: the lowerings, as spec functions (`lower`, `lowered`). There
//!   is no executable emitter yet: `lir::Instr` holds `nat`s and `Seq`s, so
//!   building it needs an executable mirror like [`crate::spec::Op`] first.
//! - Proofs, bottom up: [`lirmem`] (LIR's byte memory), [`run`] (running a
//!   list of simple instructions), [`frame`] (a frame slot's address, load
//!   and store under the relation), [`proofs`] (the handler exit, constants,
//!   copies and jumps), [`arith`] (what LIR computes on NaN-boxed int32s,
//!   against `arith_add`, `arith_sub`, `arith_mul`), [`trace`] (the blocks of
//!   the integer lowerings), [`intops`] (the integer lowerings), [`dispatch`]
//!   (`lemma_lower_refines`, by cases on the op).
//!
//! # What is proven (Verus, no axiom, no assumption but `handler_complete`)
//!
//! `lemma_lower_refines`: for every op [`lower::lowered`] holds of, the
//! lowering satisfies [`contract::lowers`]:
//!
//! - **every handler-class op** (`Exp`, `LooseEq`, `LooseNe`, `TypeOf`,
//!   `InstanceOf`, `HasProperty`, `DeleteProp`, `GetGlobal`, `SetGlobal`,
//!   `NewObject`, `NewArray`, `NewEnv`, `NewClosure`, `New`, `CallSpread`,
//!   `GetIterator`, `IterNext`, `IterClose`, `Yield`, `Await`, `Throw`,
//!   `ThrowError`): an exit to its handler;
//! - **moves, constants and register loads**: `Nop`, `Move`, `LoadConst`,
//!   `LoadInt`, `LoadUndefined`, `LoadNull`, `LoadBool`, `LoadHole`,
//!   `GetThis`, `GetCallee`;
//! - **jumps**: `Jump`, `JumpIfUndefined`, `JumpIfNotUndefined`,
//!   `JumpIfNullish`, `JumpIfNotNullish` (a `br` or `br_if` to the label the
//!   whole-function layout will give the target);
//! - **small-integer `Add`, `Sub`, `Mul`**: two int32 operands and an int32
//!   result (and, for `Mul`, not `-0`) are computed inline; every other case
//!   is an exit to the op's handler, which for two doubles or an overflow
//!   relies on `handler_complete`.
//!
//! # What is not
//!
//! - **Not lowered** (each is a later slice, with its reason):
//!   - `f64` arithmetic: LIR's `f64` operators are uninterpreted functions
//!     (`f64_add`) and the bytecode semantics' rounding is a different
//!     uninterpreted function (`f64_add_finite`); relating them needs an
//!     axiom this crate does not add. So the doubles of `Add`, `Sub` and
//!     `Mul` exit, and `Div`, `Mod`, `Neg`, `Inc`, `Dec`, the bitwise ops,
//!     the shifts and `ToNumeric` have no lowering yet.
//!   - **Comparisons** (`Lt`, `Le`, `Gt`, `Ge`, `StrictEq`, `StrictNe`) and
//!     `Not`, `JumpIfTrue`, `JumpIfFalse`: the integer cases need a lemma
//!     that `f64_of_int` is monotone and injective (the semantics compares
//!     the doubles that int32s stand for); not proven yet.
//!   - **Property and element access through inline caches** (`GetProp`,
//!     `SetProp`, `GetElem`, `SetElem`) and the environment ops: the heap is
//!     an abstract map and the cache table a `Seq` of entries, with no byte
//!     layout (phase-7.md 7.5 has not fixed one), so there is nothing in
//!     LIR's memory to relate them to.
//!   - `Call`, `Return` (they move `fp`), `Loop` (reads the termination flag),
//!     `GetException`, `GetArgc` (they read state with no byte home yet), and
//!     `ThrowIfHole`.
//!   - The newer bytecode ops of the unmerged branches (#224, #227, #230,
//!     #234): they are not in `main`'s `step`.
//! - **No emitter, no whole function, no tiering, no code cache.** One op at
//!   a time, as spec functions.
//! - **The LIR is not shown to type-check** with `clazel-lir`'s `tc`; the
//!   proofs show directly that it is never stuck from a related state.
//! - **No tier is claimed.** `tier` stays 0 (CLAUDE.md rule 7).

pub mod arith;
pub mod blocks;
pub mod contract;
pub mod dispatch;
pub mod frame;
pub mod intcmp;
pub mod intops;
pub mod lirmem;
pub mod lower;
pub mod numord;
pub mod proofs;
pub mod run;
pub mod spec;
pub mod trace;
