//! What the A64 back end's **structured control flow and memory
//! instructions** are about (jit.md item J.9, second slice, A64): the state
//! relation that includes the region table ([`rel_base`]), what a run of
//! code with branches preserves ([`preserved_r`]), and the machine's running of
//! code with jumps ([`steps`], [`reaches`]). It is [`crate::cfspec`]'s A64
//! counterpart and follows its design; the source language ([`Node`], whose
//! blocks are all void) and its static analysis ([`cf_flow`]) are shared with
//! the x86-64 back end, which this crate proves sound for LIR's `eval`
//! ([`crate::cfheight`]). Read [`crate::cfspec`]'s header for the choices
//! the two share (8: void blocks, 9: static heights, 10: labels are byte
//! offsets, 11: a `load` or `store` is its own bounds-check sequence and the
//! access, with its two exits going to a stub after the access, 12: the
//! region table is related, 13: the fresh stack of a block is a `base`, 14:
//! running with jumps, 15: regions are not code). This header says where A64
//! differs.
//!
//! # Where A64 differs from [`crate::cfspec`]
//!
//! 16. **A branch is relative to its own address, in words.** `b` has a
//!     26-bit and `b.cond`, `cbz` and `cbnz` a 19-bit *signed* displacement
//!     in 4-byte words, from the address of the branch itself (`clazel-a64`'s
//!     [`isa::step`]: `BranchTo(PC + 4 * imm)`). So a label's byte offset must
//!     be a multiple of 4 ([`cf_canon`] says it is) and a conditional branch
//!     reaches only 1 MiB each way: the translation refuses a program whose
//!     code is more than [`crate::a64::cftemplates::max_size`] bytes
//!     ([`crate::a64::cftemplates::cf_prog_ok`]), which is what makes every
//!     displacement fit.
//! 17. **Exit codes are 16 bits.** The validator's exit sequence is `movz` of
//!     a 16-bit code ([`exit_seq`]), so an `exit` or a `bounds_check` whose
//!     code is 65536 or more has no translation ([`codes_ok`]); the exit
//!     code of the stub after a `load` or `store` is [`trap_code`], `0xFFFF`
//!     (choice 11: nothing is claimed about it).
//! 18. **No native stack, no `create_undef`.** The exit sequence returns
//!     through `x30` and reads no memory, so there is no [`crate::spec::stack_ok_r`]
//!     analogue, and [`isa::step`] takes no source of undefined values, so no
//!     statement has a `cu`. The link register and `SP` are preserved
//!     ([`preserved_r`]), which the exit sequence needs.
//! 19. **Registers.** The scratch registers are `x0` to `x4`: `x0` and `x2`
//!     are the bounds check's scratch registers (`t`, `bnd`), `x1` holds the
//!     index, `x3` the region's base and `x4` the value a `store` writes
//!     ([`x3`], [`x4`]).
//!
//! # What is not here
//!
//! Typed blocks (choice 8), `f64` arithmetic, rotates, frames beyond 31
//! slots, a `br_table` of more than [`crate::cfspec::max_targets`] targets,
//! and a program of more than `max_size` bytes.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
pub use crate::cfspec::{
    Flow, MTy, MemOp, Node, cf_flow, exit_instr, flow_fits, max_targets, templated, void_bt,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: registers and codes
// ============================================================================

/// `x3`: a region's base, in an access.
pub open spec fn x3() -> u8 {
    3
}

/// `x4`: the value a `store` writes.
pub open spec fn x4() -> u8 {
    4
}

/// The exit code of a bounds check inside a `load` or `store` (choice 11 of
/// [`crate::cfspec`]).
pub open spec fn trap_code() -> u16 {
    0xFFFF
}

/// Every exit code in `n` (of an `exit`, or of a `bounds_check`) is 16 bits
/// (choice 17), so the validator's exit sequence can say it.
pub open spec fn codes_ok(n: Node) -> bool
    decreases n,
{
    match n {
        Node::Op(_) => true,
        Node::Mem(m) => match m {
            MemOp::BoundsCheck { code, .. } => code < 0x1_0000,
            _ => true,
        },
        Node::Then(a, b) => codes_ok(*a) && codes_ok(*b),
        Node::Block(b) => codes_ok(*b),
        Node::Loop(b) => codes_ok(*b),
        Node::If(t, e) => codes_ok(*t) && codes_ok(*e),
        Node::Br(_) => true,
        Node::BrIf(_) => true,
        Node::BrTable(_, _) => true,
        Node::Exit(c, _) => c < 0x1_0000,
    }
}

// ============================================================================
// Section: the state relation with a base, and the region table
// ============================================================================

/// `a` is a byte of some region, `a` an `int`.
pub open spec fn in_regions_i(lay: lir::Layout, a: int) -> bool {
    0 <= a && in_regions(lay, a as nat)
}

/// The context's region table holds LIR's layout: at most 16 regions, and for
/// each, `base` at `x28 + 16 k` and `bound` at `x28 + 16 k + 8`, as 64-bit
/// words (choice 12 of [`crate::cfspec`]). No region overlaps the table, so a
/// store to a region never changes it (the exit area is already clear:
/// [`rel`]).
pub open spec fn table_ok(lay: lir::Layout, m: isa::State) -> bool {
    lay.len() <= abi::num_regions() && (forall|k: int|
        0 <= k < lay.len() ==> {
            &&& isa::mem_read(m.mem, ctx_of(m) + abi::base_off(k), 8) == Some(
                (#[trigger] lay[k]).base as int,
            )
            &&& isa::mem_read(m.mem, ctx_of(m) + abi::bound_off(k), 8) == Some(
                lay[k].bound as int,
            )
        }) && forall|b: int|
        ctx_of(m) <= b < ctx_of(m) + abi::table_end() ==> !#[trigger] in_regions_i(lay, b)
}

/// The machine `m` represents the LIR state `a` on top of the values `base`
/// (choice 13 of [`crate::cfspec`]), and the region table is as LIR's layout.
#[verifier::opaque]
pub open spec fn rel_base(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    nl: nat,
) -> bool {
    rel(lay, a.with_stack(base + a.stack), m, nl) && table_ok(lay, m)
}

/// What a run of code leaves alone in memory, now that a store may write a
/// region: the context register keeps its value, the mapped addresses are the
/// same, and every byte outside the exit area **and outside every region**
/// keeps its value (choice 15 of [`crate::cfspec`]).
pub open spec fn preserved_mem_r(lay: lir::Layout, m: isa::State, m2: isa::State) -> bool {
    m.r.len() == 31 && m2.r.len() == 31 && m2.r[abi::ctx_reg() as int] == m.r[abi::ctx_reg() as int]
        && m2.mem.dom() == m.mem.dom() && (forall|a: int|
        #[trigger] m.mem.dom().contains(a) && !in_exit_area(ctx_of(m), a) && !in_regions_i(lay, a)
            ==> m2.mem[a] == m.mem[a])
}

/// [`preserved_mem_r`], and the link register and the stack pointer keep their
/// values too (choice 18).
pub open spec fn preserved_r(lay: lir::Layout, m: isa::State, m2: isa::State) -> bool {
    preserved_mem_r(lay, m, m2) && m2.r[abi::link_reg() as int] == m.r[abi::link_reg() as int]
        && m2.sp == m.sp
}

// ============================================================================
// Section: running code with jumps
// ============================================================================

/// The instruction of `code` that begins `off` bytes after the first byte:
/// `None` if no instruction begins there (past the end, before the start, or
/// not a multiple of 4).
pub open spec fn fetch(code: Seq<isa::Instr>, off: int) -> Option<isa::Instr> {
    if 0 <= off && off % 4 == 0 && off / 4 < code.len() {
        Some(code[off / 4])
    } else {
        None
    }
}

/// `n` steps of the machine from `s`, the code `code` being placed at address
/// `base` (choice 14 of [`crate::cfspec`]): each fetches the instruction at
/// `pc` and steps it. A fault, or a `pc` with no instruction of `code`, is
/// `None`.
pub open spec fn steps(code: Seq<isa::Instr>, base: int, s: isa::State, n: nat) -> Option<
    isa::State,
>
    decreases n,
{
    if n == 0 {
        Some(s)
    } else {
        match fetch(code, s.pc as int - base) {
            Some(i) => match isa::step(s, i) {
                Some(s1) => steps(code, base, s1, (n - 1) as nat),
                None => None,
            },
            None => None,
        }
    }
}

/// Running `code` (placed at `base`) from `s` reaches `s2` after some number
/// of steps, none of which faults.
pub open spec fn reaches(code: Seq<isa::Instr>, base: int, s: isa::State, s2: isa::State) -> bool {
    exists|n: nat| steps(code, base, s, n) == Some(s2)
}

} // verus!
