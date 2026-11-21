//! What the x86-64 back end must be proven to satisfy for **structured control
//! flow, memory instructions and `exit` with operands** (CLAUDE.md rule 3,
//! docs/SPEC-STYLE.md): the refinement statement [`cf_refines`] and the
//! emitter's contract, in terms of [`crate::cfspec`] and the two semantics it
//! relates. Written before any template; reviewing this file and `cfspec` is
//! enough to know what is claimed.
//!
//! # The refinement statement
//!
//! [`cf_refines`]`(i, nl, h, offs, code)` says the x86-64 list `code` is a
//! correct translation of the LIR instruction `i`, for a function with `nl`
//! locals, when the operand stack is `h` values high (the `base` below `i`'s
//! fresh stack, and its own stack), with the labels in scope at the byte
//! offsets `offs` from the first byte of `code` (label 0 first). For every
//! layout, `create_undef`, `base`, LIR state `a` and machine state `m`
//! related by [`rel_base`], with the native stack as the enter stub leaves it
//! ([`stack_ok_r`]), and every address the code can jump to canonical:
//!
//! - **`Normal(a2)`** (falls through): `code` [`reaches`] a state `m2` at the
//!   byte after `code`, related to `a2` on the same `base`, differing from
//!   `m` only in the exit area and the regions ([`preserved_r`]).
//! - **`Branch(l, s)`** (a `br` that no label inside `i` catches): `l` is a
//!   label in scope, and `code` reaches a state at the label's address,
//!   related to `s` on `base` and some `extra` values (choice 13), with the
//!   exit area and regions the only change.
//! - **`Exit(c, vals, s)`**: `code` reaches the state the exit sequence
//!   leaves: the exit code `c` in the context's exit-code word, `rsp` popped
//!   and `rip` at the return address the stub pushed, the frame and regions
//!   related to `s`, and the operands `vals` still in the frame, in the slots
//!   above `s`'s stack.
//! - **`Stuck`, `OutOfFuel`**: nothing is claimed. A bounds-check failure
//!   in a `load` or `store` is `Stuck` in LIR (choice 11).
//!
//! That is a forward simulation of one LIR evaluation by one run of the
//! translation. LIR's evaluation is fuelled, so a divergent program is
//! `OutOfFuel` at every fuel and says nothing, and a terminating one is
//! matched by a terminating run.
//!
//! # What is not stated
//!
//! - That the output is **accepted by the validator** (checked by
//!   `tests/validator.rs`, as for the first slice).
//! - Typed blocks, the `f64` operations, a frame beyond 31 slots (see
//!   [`crate::cfspec`]).
//! - Anything about `rip`, flags or scratch registers beyond what is said.

use crate::cfspec::*;
use crate::cftemplates::cf_prog_ok;
use crate::contract::*;
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every address the code can end at or jump to is canonical.
pub open spec fn cf_canon(rip: int, offs: Seq<int>, code: Seq<x64::Instr>) -> bool {
    x64::canonical(rip + code_len(code)) && forall|l: int|
        0 <= l < offs.len() ==> x64::canonical(rip + #[trigger] offs[l])
}

/// What the machine is at after an exit sequence for `c` from a state with a
/// stack as the enter stub leaves it, as [`exit_refines`] says: the exit-code
/// word holds `c`, `rsp` is popped, `rip` is the return address.
pub open spec fn exit_done(m: x64::State, m2: x64::State, c: nat) -> bool {
    let rsp = x64::logext(64, m.rgf[abi::sp_reg() as int] as int);
    x64::read_mem(m2.mem, ctx_of(m) + abi::exit_code_off(), 8) == Some(c as int)
        && m2.rgf.len() == 16 && m2.rgf[abi::sp_reg() as int] as int == x64::loghead(64, rsp + 8)
        && match x64::read_mem(m.mem, rsp, 8) {
        Some(raw) => m2.rip == x64::logext(64, raw),
        None => false,
    }
}

/// The operands `vals` of an exit are in the frame, in the slots after the
/// first `n0` stack slots (`nl` locals, then the stack): value `i` in slot
/// `nl + n0 + i`.
pub open spec fn ops_in_frame(
    mm: Map<int, u8>,
    ctxb: int,
    nl: nat,
    n0: nat,
    vals: Seq<lir::Val>,
) -> bool {
    forall|i: int|
        0 <= i < vals.len() ==> #[trigger] slot_holds(
            mm,
            ctxb,
            (nl + n0 + i) as nat,
            lir::val_bits(vals[i]),
        )
}

/// The machine represents `s` on top of `base` and **some extra values**
/// (the bases that nested bodies added: see [`crate::cfspec`], choice 13).
pub open spec fn rel_ext(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    s: lir::St,
    m2: x64::State,
    nl: nat,
) -> bool {
    exists|extra: Seq<lir::Val>|
        #![trigger rel_base(lay, base + extra, s, m2, nl)]
        rel_base(lay, base + extra, s, m2, nl)
}

/// [`rel_ext`], and the operands `vals` of an exit are in the frame above the
/// stack (`ctxb` is the context's address).
pub open spec fn exit_rel(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    s: lir::St,
    m2: x64::State,
    nl: nat,
    ctxb: int,
    vals: Seq<lir::Val>,
) -> bool {
    exists|extra: Seq<lir::Val>|
        #![trigger rel_base(lay, base + extra, s, m2, nl)]
        rel_base(lay, base + extra, s, m2, nl) && ops_in_frame(
            m2.mem,
            ctxb,
            nl,
            (base + extra).len() + s.stack.len(),
            vals,
        )
}

/// What must hold after `code` ran from `m`, for LIR's outcome `o` (see the
/// module doc).
pub open spec fn cf_post(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    code: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    o: lir::Outcome,
) -> bool {
    match o {
        lir::Outcome::Normal(a2) => exists|m2: x64::State|
            #![trigger reaches(cu, code, m.rip, m, m2)]
            reaches(cu, code, m.rip, m, m2) && m2.rip == m.rip + code_len(code) && rel_base(
                lay,
                base,
                a2,
                m2,
                nl,
            ) && preserved_r(lay, m, m2),
        lir::Outcome::Branch(l, s) => l < offs.len() && exists|m2: x64::State|
            #![trigger reaches(cu, code, m.rip, m, m2)]
            reaches(cu, code, m.rip, m, m2) && m2.rip == m.rip + offs[l as int] && rel_ext(
                lay,
                base,
                s,
                m2,
                nl,
            ) && preserved_r(lay, m, m2),
        lir::Outcome::Exit(c, vals, s) => exists|m2: x64::State|
            #![trigger reaches(cu, code, m.rip, m, m2)]
            reaches(cu, code, m.rip, m, m2) && exit_done(m, m2, c) && exit_rel(
                lay,
                base,
                s,
                m2,
                nl,
                ctx_of(m),
                vals,
            ) && preserved_mem_r(lay, m, m2),
        _ => true,
    }
}

/// **`code` refines the LIR instruction `i`** at stack height `h` with `nl`
/// locals, the labels in scope at the byte offsets `offs` (see the module
/// doc).
pub open spec fn cf_refines(
    i: lir::Instr,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    code: Seq<x64::Instr>,
) -> bool {
    forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, i, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, code) ==> cf_post(
            lay,
            base,
            nl,
            offs,
            code,
            cu,
            m,
            lir::eval(lay, i, a, fuel),
        )
}

/// The exit sequence for `c` refines LIR's `exit c` **with `k` operands**:
/// [`exit_refines`], and the operands are still in the frame afterwards, in
/// the slots above the stack the exit leaves (the exit sequence writes only
/// the exit-code word, so they are never overwritten; the host reads them
/// from there).
pub open spec fn exit_ops_refines(c: u32, k: nat, nl: nat) -> bool {
    forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger lir::eval(lay, exit_instr(c as nat, k), a, fuel), run_seq(cu, m, exit_seq(c))]
        rel(lay, a, m, nl) && stack_ok(m) && x64::canonical(m.rip + code_len(exit_seq(c)))
            ==> match lir::eval(
            lay,
            exit_instr(c as nat, k),
            a,
            fuel,
        ) {
            lir::Outcome::Exit(code, vals, a2) => match run_seq(cu, m, exit_seq(c)) {
                Some(m2) => rel(lay, a2, m2, nl) && preserved_mem(m, m2) && exit_done(m, m2, code)
                    && forall|i: int|
                    0 <= i < vals.len() ==> #[trigger] slot_holds(
                        m2.mem,
                        ctx_of(m),
                        (nl + a2.stack.len() + i) as nat,
                        lir::val_bits(vals[i]),
                    ),
                None => false,
            },
            _ => true,
        }
}

// ----------------------------------------------------------------------------
// The emitter's contract for control flow (the executable back end)
// ----------------------------------------------------------------------------

/// Postcondition of the control-flow emitter's `emit_blob`: the bytes are the
/// canonical encodings of a body that refines the program `n` with the
/// function's return label at the end of the body (a `br` to it, and falling
/// off the end, reach the exit sequence that follows), followed by the exit
/// sequence for `exit_code`. `None` exactly when [`cf_prog_ok`] refuses.
pub open spec fn emit_cf_blob_ensures(
    n: Node,
    nl: usize,
    exit_code: u32,
    r: Option<Seq<u8>>,
) -> bool {
    match r {
        Some(bytes) => cf_prog_ok(n, nl as nat) && exists|body: Seq<x64::Instr>|
            #![trigger all_valid_instrs(body)]
            all_valid_instrs(body) && cf_refines(
                n@,
                nl as nat,
                0,
                seq![code_len(body) as int],
                body,
            ) && bytes == clazel_codecheck::spec::enc_all(body + exit_seq(exit_code)),
        None => !cf_prog_ok(n, nl as nat),
    }
}

} // verus!
