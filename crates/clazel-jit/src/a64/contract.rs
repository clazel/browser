//! What the A64 back end must be proven to satisfy (CLAUDE.md rule 3,
//! docs/SPEC-STYLE.md): the refinement statements, and one `requires` and one
//! `ensures` predicate for each method of [`super::api::Backend`], in terms of
//! [`super::spec`] and the two semantics it relates. These are written before
//! any template; reviewing them and `spec` is enough to know what is claimed.
//! They are [`crate::contract`]'s statements with the A64 machine.
//!
//! # The refinement statement
//!
//! [`refines`]`(i, nl, h, code)` says that the A64 instruction list `code` is a
//! correct translation of the LIR instruction `i`, for a function with `nl`
//! locals, when the operand stack has `h` values. For every layout, every LIR
//! state `a` and machine state `m` related by [`rel`]:
//!
//! - if LIR evaluates `i` in `a` (with any fuel) and **falls through** to the
//!   state `a2` (a `Stuck` or `OutOfFuel` outcome is not claimed about, and
//!   `i` is not required to be well typed: if it is not, LIR is `Stuck`, and
//!   the statement says nothing),
//! - and the end of the code does not wrap the address space,
//! - then running `code` from `m` ([`run_seq`]) does not fault, ends in a
//!   machine state `m2` related to `a2` by [`rel`], with `pc` after the code,
//!   and `m2` differs from `m` only in the exit area ([`preserved`]).
//!
//! That is a **forward simulation of one LIR step by one template**. The exit
//! is [`exit_refines`]; failed steps and branches belong to the control-flow
//! templates, which this slice does not have. A straight-line program is one
//! [`refines`] over [`prog_instr`].
//!
//! # What is not stated
//!
//! - That the output is **accepted by the A64 validator.**
//!   `tests/validator_a64.rs` checks it for every template and generated
//!   programs, by running the executable validator. It is not a theorem here.
//! - That a *failed* LIR step is matched by the machine: no template in this
//!   slice has one.
//! - Anything about [`rel`]'s `pc`, flags or scratch registers.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the machine must be in after `code` ran from `m`, for the LIR state
/// `a2` that `i` reached: no fault, related, `pc` after the code, and nothing
/// outside the exit area changed.
pub open spec fn refines_post(
    lay: lir::Layout,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    code: Seq<isa::Instr>,
    r: Option<isa::State>,
) -> bool {
    match r {
        Some(m2) => rel(lay, a2, m2, nl) && m2.pc as int == m.pc as int + code_len(code)
            && preserved(m, m2),
        None => false,
    }
}

/// `code` refines the LIR instruction `i` at stack height `h` with `nl`
/// locals (see the module doc).
pub open spec fn refines(i: lir::Instr, nl: nat, h: nat, code: Seq<isa::Instr>) -> bool {
    forall|lay: lir::Layout, a: lir::St, m: isa::State, fuel: nat|
        #![trigger lir::eval(lay, i, a, fuel), run_seq(m, code)]
        a.stack.len() == h && rel(lay, a, m, nl) && (m.pc as int) + code_len(code)
            < isa::p2(64) ==> match lir::eval(lay, i, a, fuel) {
            lir::Outcome::Normal(a2) => refines_post(lay, a2, m, nl, code, run_seq(m, code)),
            _ => true,
        }
}

/// The exit sequence for `c` refines LIR's `exit c` with no operands: running
/// the three instructions does not fault; the machine ends at the return
/// address the enter stub left in the link register, with the exit code `c` in
/// the context's exit-code word, the frame and the regions as they were
/// ([`rel`] still holds, and the memory outside the exit area is unchanged),
/// and the link register and `SP` as they were.
pub open spec fn exit_refines(c: u16, nl: nat) -> bool {
    forall|lay: lir::Layout, a: lir::St, m: isa::State, fuel: nat|
        #![trigger lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel), run_seq(m, exit_seq(c))]
        rel(lay, a, m, nl) && (m.pc as int) + code_len(exit_seq(c)) < isa::p2(64)
            ==> match lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel) {
            lir::Outcome::Exit(code, _, a2) => match run_seq(m, exit_seq(c)) {
                Some(m2) => rel(lay, a2, m2, nl) && preserved(m, m2) && isa::mem_read(
                    m2.mem,
                    ctx_of(m) + abi::exit_code_off(),
                    8,
                ) == Some(code as int) && m2.pc == m.r[abi::link_reg() as int],
                None => false,
            },
            _ => true,
        }
}

// ----------------------------------------------------------------------------
// The emitter's contracts (the executable back end, `api::Backend`)
// ----------------------------------------------------------------------------

/// The instructions of `code` are all in the A64 subset ([`isa::valid_instr`]).
pub open spec fn all_valid_instrs(code: Seq<isa::Instr>) -> bool {
    forall|j: int| 0 <= j < code.len() ==> isa::valid_instr(#[trigger] code[j])
}

/// Precondition of `emit_body` and `emit_blob`: none. Every program and every
/// local count is a legal input (one outside the first slice, or too large
/// for the frame, is answered `None`).
pub open spec fn emit_requires(ops: Seq<Op>, nl: usize) -> bool {
    true
}

/// Postcondition of `emit_body`: the program has a translation exactly when
/// [`prog_ok`] says every instruction has a template; the translation is in
/// the subset and refines the program's LIR instruction.
pub open spec fn emit_body_ensures(
    ops: Seq<Op>,
    nl: usize,
    r: Option<Seq<isa::Instr>>,
) -> bool {
    match r {
        Some(code) => prog_ok(ops, nl as nat, 0) && all_valid_instrs(code) && refines(
            prog_instr(ops),
            nl as nat,
            0,
            code,
        ),
        None => !prog_ok(ops, nl as nat, 0),
    }
}

/// Postcondition of `emit_blob`: the bytes are exactly the canonical
/// encodings ([`clazel_codecheck::a64::spec::decodes_to`], which is what the
/// validator reads back) of a body that refines the program, followed by the
/// exit sequence for `exit_code`. `None` exactly when the program has no
/// translation.
pub open spec fn emit_blob_ensures(
    ops: Seq<Op>,
    nl: usize,
    exit_code: u16,
    r: Option<Seq<u8>>,
) -> bool {
    match r {
        Some(bytes) => prog_ok(ops, nl as nat, 0) && exists|body: Seq<isa::Instr>|
            #![trigger all_valid_instrs(body)]
            all_valid_instrs(body) && refines(prog_instr(ops), nl as nat, 0, body)
                && clazel_codecheck::a64::spec::decodes_to(bytes, body + exit_seq(exit_code)),
        None => !prog_ok(ops, nl as nat, 0),
    }
}

} // verus!
