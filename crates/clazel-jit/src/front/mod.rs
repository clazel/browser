//! The JS front end (docs/phases/jit.md item J.10): bytecode → LIR, with a
//! proof per op that the LIR **refines `clazel-js-vm`'s `step`**. It sits
//! above LIR, so what it proves holds on both instruction sets: it stops at
//! LIR and needs nothing from the back ends' control flow.
//!
//! This is the first slice. It was written contract first (CLAUDE.md rule 3):
//! [`spec`] and [`contract`], the statement, came in their own commit, before
//! any lowering.
//!
//! - [`spec`]: **what the front end is about.** The relation between a
//!   bytecode machine state and a LIR state (the shared frame layout of
//!   phase-7.md "Shapes fixed here for the JIT"), the exit protocol, and the
//!   per-op outcome a lowering must have. Read its header first: it lists
//!   the modelling choices.
//! - [`contract`]: the refinement statement, [`contract::lowers`].

pub mod contract;
pub mod spec;
