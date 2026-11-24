//! What the front end must be proven to satisfy (CLAUDE.md rule 3,
//! docs/SPEC-STYLE.md): the refinement statement, in terms of
//! [`super::spec`] and the two semantics it relates. It is written before any
//! lowering (the lowerings are the next commit); reviewing it and `spec` is
//! enough to know what is claimed.
//!
//! # The refinement statement
//!
//! [`lowers`]`(c, op, pc, lbl, code)` says that the LIR instruction `code` is
//! a correct lowering of the bytecode op `op` at index `pc` of a function whose
//! code is `c`, with `lbl` the label a jump goes to. (`pc` is in the lowering
//! because an exit tells the handler where it is: modelling choice 7.) For
//! every layout, every bytecode state
//! `s` and LIR state `st` that are related ([`rel`]), where
//!
//! - LIR's operand stack is empty,
//! - `s` is well-formed ([`js::state_wf`]), its function is `c`, its `pc` is
//!   `pc`, and the op there is `op` (so the host's handler call reads the same
//!   op), and
//! - the handlers are complete at `s` ([`handler_complete`], the one
//!   hypothesis about code outside this crate, modelling choice 8),
//!
//! then for every amount of fuel from [`lower_fuel`], LIR's `eval` of `code`
//! has an outcome [`outcome_refines`] allows: fall through, branch or exit,
//! each as that function says, and never `Stuck` or out of fuel.
//!
//! That is a **forward simulation of one bytecode step by one lowering, with
//! the exit as the handler call**, in the shape of `step` itself:
//! `step(s, op)` is `fast_step` when `fast_path` holds and the handler's
//! result otherwise, and the lowering reaches the first by falling through or
//! branching and the second by exiting. A whole function is the sequence of
//! these, composed by the later slice that lays out labels.
//!
//! # What is not stated
//!
//! - **That the handler is right.** The exit's claim is "the handler's
//!   result is `step`'s", true of `step` by definition when `fast_path`
//!   fails and by [`handler_complete`] otherwise. What a handler does is
//!   7.8's and Test262's.
//! - **That the LIR type-checks.** The proof shows directly that evaluation
//!   is never stuck from a related state; LIR's typing judgment is not applied.
//! - **A whole function, a call, a return, tiering and entry at a loop
//!   head.** One op at a time.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `code` is a correct lowering of `op` (see the module doc).
pub open spec fn lowers(c: js::Code, op: js::Op, pc: nat, lbl: nat, code: lir::Instr) -> bool {
    forall|lay: lir::Layout, s: js::State, st: lir::St, fuel: nat|
        #![trigger lir::eval(lay, code, st, fuel), rel(lay, s, st)]
        fuel >= lower_fuel() && rel(lay, s, st) && st.stack == Seq::<lir::Val>::empty()
            && js::state_wf(s) && js::cur_code(s) == c && s.pc == pc && js::fetch(s) == op
            && handler_complete(s, op) ==> outcome_refines(
            lay,
            s,
            op,
            lbl,
            lir::eval(lay, code, st, fuel),
        )
}

} // verus!
