//! What the A64 back end must be proven to satisfy for **structured control
//! flow, memory instructions and `exit` with operands** (CLAUDE.md rule 3,
//! docs/SPEC-STYLE.md): the refinement statement [`cf_refines`] and the
//! emitter's contract, in terms of [`crate::a64::cfspec`] and the two
//! semantics it relates. It is [`crate::cfcontract`]'s A64 counterpart; read
//! that header, which says the same in x86-64's terms. Reviewing this file and
//! `cfspec` is enough to know what is claimed.
//!
//! # The refinement statement
//!
//! [`cf_refines`]`(i, nl, h, offs, code)` says the A64 list `code` is a
//! correct translation of the LIR instruction `i`, for a function with `nl`
//! locals, when the operand stack is `h` values high (the `base` below `i`'s
//! fresh stack, and its own stack), with the labels in scope at the byte
//! offsets `offs` from the first byte of `code` (label 0 first). For every
//! layout, `base`, LIR state `a` and machine state `m` related by
//! [`rel_base`], with every address the code can end at or branch to a
//! 4-byte-aligned address below `2^64` ([`cf_canon`]):
//!
//! - **`Normal(a2)`** (falls through): `code` [`reaches`] a state `m2` at the
//!   byte after `code`, related to `a2` on the same `base`, differing from
//!   `m` only in the exit area and the regions ([`preserved_r`]).
//! - **`Branch(l, s)`** (a `br` that no label inside `i` catches): `l` is a
//!   label in scope, and `code` reaches a state at the label's address,
//!   related to `s` on `base` and some `extra` values (choice 13 of
//!   [`crate::cfspec`]), with the exit area and regions the only change.
//! - **`Exit(c, vals, s)`**: `code` reaches the state the exit sequence
//!   leaves: the exit code `c` in the context's exit-code word, `pc` at the
//!   return address the enter stub left in `x30`, the frame and regions
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
//! - That the output is **accepted by the A64 validator** (checked by
//!   `tests/validator_a64_cf.rs`, as for the first slice).
//! - Typed blocks, the `f64` operations, a frame beyond 31 slots (see
//!   [`crate::cfspec`]).
//! - Anything about `pc`, flags or scratch registers beyond what is said.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every address the code can end at or branch to is a 4-byte-aligned address
/// below `2^64`: the end of the code, and each label.
pub open spec fn cf_canon(pc: int, offs: Seq<int>, code: Seq<isa::Instr>) -> bool {
    pc + code_len(code) < isa::p2(64) && forall|l: int|
        0 <= l < offs.len() ==> 0 <= pc + #[trigger] offs[l] && pc + offs[l] < isa::p2(64)
            && offs[l] % 4 == 0
}

/// What the machine is at after an exit sequence from a state: the exit-code
/// word holds `c`, and `pc` is the return address in the link register (see
/// [`exit_refines`]).
pub open spec fn exit_done(m: isa::State, m2: isa::State, c: nat) -> bool {
    isa::mem_read(m2.mem, ctx_of(m) + abi::exit_code_off(), 8) == Some(c as int) && m2.pc
        == m.r[abi::link_reg() as int]
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
    m2: isa::State,
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
    m2: isa::State,
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
    code: Seq<isa::Instr>,
    m: isa::State,
    o: lir::Outcome,
) -> bool {
    match o {
        lir::Outcome::Normal(a2) => exists|m2: isa::State|
            #![trigger reaches(code, m.pc as int, m, m2)]
            reaches(code, m.pc as int, m, m2) && m2.pc as int == m.pc as int + code_len(code)
                && rel_base(lay, base, a2, m2, nl) && preserved_r(lay, m, m2),
        lir::Outcome::Branch(l, s) => l < offs.len() && exists|m2: isa::State|
            #![trigger reaches(code, m.pc as int, m, m2)]
            reaches(code, m.pc as int, m, m2) && m2.pc as int == m.pc as int + offs[l as int]
                && rel_ext(lay, base, s, m2, nl) && preserved_r(lay, m, m2),
        lir::Outcome::Exit(c, vals, s) => exists|m2: isa::State|
            #![trigger reaches(code, m.pc as int, m, m2)]
            reaches(code, m.pc as int, m, m2) && exit_done(m, m2, c) && exit_rel(
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
    code: Seq<isa::Instr>,
) -> bool {
    forall|lay: lir::Layout, base: Seq<lir::Val>, a: lir::St, m: isa::State, fuel: nat|
        #![trigger cf_post(lay, base, nl, offs, code, m, lir::eval(lay, i, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            code,
        ) ==> cf_post(lay, base, nl, offs, code, m, lir::eval(lay, i, a, fuel))
}

/// The exit sequence for `c` refines LIR's `exit c` **with `k` operands**:
/// [`exit_refines`], and the operands are still in the frame afterwards, in
/// the slots above the stack the exit leaves (the exit sequence writes only
/// the exit-code word, so they are never overwritten; the host reads them
/// from there).
pub open spec fn exit_ops_refines(c: u16, k: nat, nl: nat) -> bool {
    forall|lay: lir::Layout, a: lir::St, m: isa::State, fuel: nat|
        #![trigger lir::eval(lay, exit_instr(c as nat, k), a, fuel), run_seq(m, exit_seq(c))]
        rel(lay, a, m, nl) && (m.pc as int) + code_len(exit_seq(c)) < isa::p2(64)
            ==> match lir::eval(lay, exit_instr(c as nat, k), a, fuel) {
            lir::Outcome::Exit(code, vals, a2) => match run_seq(m, exit_seq(c)) {
                Some(m2) => rel(lay, a2, m2, nl) && preserved_mem(m, m2) && exit_done(m, m2, code)
                    && m2.r[abi::link_reg() as int] == m.r[abi::link_reg() as int] && m2.sp
                    == m.sp && forall|i: int|
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

/// Postcondition of the control-flow emitter's `emit_cf_blob` (the code it
/// must return is [`crate::a64::cftemplates::ctmpl`]): the bytes are the
/// canonical encodings ([`clazel_codecheck::a64::spec::decodes_to`], which is
/// what the validator reads back) of a body that refines the program `n`
/// with the function's return label at the end of the body (a `br` to it, and
/// falling off the end, reach the exit sequence that follows), followed by the
/// exit sequence for `exit_code`. `None` exactly when [`cf_prog_ok`] refuses.
pub open spec fn emit_cf_blob_ensures(
    n: Node,
    nl: usize,
    exit_code: u16,
    r: Option<Seq<u8>>,
) -> bool {
    match r {
        Some(bytes) => cf_prog_ok(n, nl as nat) && exists|body: Seq<isa::Instr>|
            #![trigger all_valid_instrs(body)]
            all_valid_instrs(body) && cf_refines(
                n@,
                nl as nat,
                0,
                seq![code_len(body) as int],
                body,
            ) && clazel_codecheck::a64::spec::decodes_to(bytes, body + exit_seq(exit_code)),
        None => !cf_prog_ok(n, nl as nat),
    }
}

} // verus!
