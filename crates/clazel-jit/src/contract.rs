//! What the back end must be proven to satisfy (CLAUDE.md rule 3,
//! docs/SPEC-STYLE.md): the refinement statements, and one `requires` and one
//! `ensures` predicate for each method of [`super::api::Backend`], in terms of
//! [`super::spec`] and the two semantics it relates. These are written before
//! any template (the templates are the next commit); reviewing them and
//! `spec` is enough to know what is claimed.
//!
//! # The refinement statement
//!
//! [`refines`]`(i, nl, h, code)` says that the x86-64 instruction list `code`
//! is a correct translation of the LIR instruction `i`, for a function with
//! `nl` locals, when the operand stack has `h` values. For every layout and
//! every `create_undef` (the machine's unspecified function for undefined
//! flags, so the statement holds for all of them), every LIR state `a` and
//! machine state `m` related by [`rel`]:
//!
//! - if LIR evaluates `i` in `a` (with any fuel) and **falls through** to the
//!   state `a2` (a `Stuck` or `OutOfFuel` outcome is not claimed about, and
//!   `i` is not required to be well typed: if it is not, LIR is `Stuck`, and
//!   the statement says nothing),
//! - and the end of the code is a canonical address,
//! - then running `code` from `m` ([`run_seq`]) does not fault, ends in a
//!   machine state `m2` related to `a2` by [`rel`], with `rip` after the code,
//!   and `m2` differs from `m` only in the exit area ([`preserved`]).
//!
//! That is a **forward simulation of one LIR step by one template**, for the
//! LIR semantics that is deterministic. Soundness of the whole translation
//! (every execution of the machine code is the image of a LIR execution) needs
//! the converse for the exits, branches and `Stuck`: the exit is
//! [`exit_refines`]; the others are for the control-flow templates. A
//! straight-line program is one [`refines`] over [`prog_instr`].
//!
//! # What is not stated
//!
//! - That the output is **accepted by the validator.** jit.md requires it and
//!   `tests/validator.rs` checks it for every template and generated
//!   programs, by running the executable validator. It is not a theorem here.
//! - That a *failed* LIR step (a bounds-check exit, `Stuck`) is matched by the
//!   machine: no template in this slice has one.
//! - Anything about [`rel`]'s `rip`, flags or scratch registers.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the machine must be in after `code` ran from `m`, for the LIR state
/// `a2` that `i` reached: no fault, related, `rip` after the code, and
/// nothing outside the exit area changed.
pub open spec fn refines_post(
    lay: lir::Layout,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    code: Seq<x64::Instr>,
    r: Option<x64::State>,
) -> bool {
    match r {
        Some(m2) => rel(lay, a2, m2, nl) && m2.rip == m.rip + code_len(code) && preserved(m, m2),
        None => false,
    }
}

/// `code` refines the LIR instruction `i` at stack height `h` with `nl`
/// locals (see the module doc).
pub open spec fn refines(i: lir::Instr, nl: nat, h: nat, code: Seq<x64::Instr>) -> bool {
    forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger lir::eval(lay, i, a, fuel), run_seq(cu, m, code)]
        a.stack.len() == h && rel(lay, a, m, nl) && x64::canonical(m.rip + code_len(code))
            ==> match lir::eval(lay, i, a, fuel) {
            lir::Outcome::Normal(a2) => refines_post(lay, a2, m, nl, code, run_seq(cu, m, code)),
            _ => true,
        }
}

/// The exit sequence for `c` refines LIR's `exit c` with no operands, given
/// the stack the enter stub leaves ([`stack_ok`]): running the three
/// instructions does not fault; the machine ends at the return address the
/// stub pushed, with the exit code `c` in the context's exit-code word, the
/// frame and the regions as they were ([`rel`] still holds, and the
/// memory outside the exit area is unchanged), and `rsp` popped by the
/// `ret`.
pub open spec fn exit_refines(c: u32, nl: nat) -> bool {
    forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel), run_seq(cu, m, exit_seq(c))]
        rel(lay, a, m, nl) && stack_ok(m) && x64::canonical(m.rip + code_len(exit_seq(c)))
            ==> match lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel) {
            lir::Outcome::Exit(code, _, a2) => match run_seq(cu, m, exit_seq(c)) {
                Some(m2) => {
                    let rsp = x64::logext(64, m.rgf[abi::sp_reg() as int] as int);
                    rel(lay, a2, m2, nl) && preserved_mem(m, m2) && x64::read_mem(
                        m2.mem,
                        ctx_of(m) + abi::exit_code_off(),
                        8,
                    ) == Some(code as int) && m2.rgf[abi::sp_reg() as int] as int == x64::loghead(
                        64,
                        rsp + 8,
                    ) && match x64::read_mem(m.mem, rsp, 8) {
                        Some(raw) => m2.rip == x64::logext(64, raw),
                        None => false,
                    }
                },
                None => false,
            },
            _ => true,
        }
}

// ----------------------------------------------------------------------------
// The emitter's contracts (the executable back end, `api::Backend`)
// ----------------------------------------------------------------------------

/// The instructions of `code` are all in the x86-64 subset
/// ([`x64::valid_instr`]).
pub open spec fn all_valid_instrs(code: Seq<x64::Instr>) -> bool {
    forall|j: int| 0 <= j < code.len() ==> x64::valid_instr(#[trigger] code[j])
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
    r: Option<Seq<x64::Instr>>,
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

/// Postcondition of `emit_blob`: the bytes are the canonical encodings
/// ([`clazel_codecheck::spec::enc_all`], which is what the validator reads
/// back) of a body that refines the program, followed by the exit sequence
/// for `exit_code`. `None` exactly when the program has no translation.
pub open spec fn emit_blob_ensures(
    ops: Seq<Op>,
    nl: usize,
    exit_code: u32,
    r: Option<Seq<u8>>,
) -> bool {
    match r {
        Some(bytes) => prog_ok(ops, nl as nat, 0) && exists|body: Seq<x64::Instr>|
            #![trigger all_valid_instrs(body)]
            all_valid_instrs(body) && refines(prog_instr(ops), nl as nat, 0, body) && bytes
                == clazel_codecheck::spec::enc_all(body + exit_seq(exit_code)),
        None => !prog_ok(ops, nl as nat, 0),
    }
}

} // verus!
