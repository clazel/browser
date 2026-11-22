//! The templates for structured control flow and memory instructions (jit.md
//! J.9, second slice, A64), as spec functions: [`ctmpl`] is the A64 code of a
//! [`Node`], given the offsets of the labels in scope; [`csize`] is its length
//! in bytes, which is what a `block`'s label offset is made from. The
//! refinement proofs are in [`crate::a64::cfproofs`]; the statement is
//! [`crate::a64::cfcontract::cf_refines`]. It is [`crate::cftemplates`]'s A64
//! counterpart.
//!
//! The layout (jit.md J.9: "composition over structured control flow", with
//! the labels resolved to code offsets):
//!
//! - `then a b`: the code of `a`, then the code of `b`; `b`'s labels are `a`'s
//!   shifted by the length of `a`'s code.
//! - `block b`: the code of `b`, with a new label 0 at the end of it.
//! - `loop b`: the code of `b`, with a new label 0 at its start.
//! - `if t e`: `ldr x0, [cond]; cbz w0, Lelse; t; b Lend; Lelse: e; Lend:`,
//!   with a new label 0 at `Lend` in each arm.
//! - `br l`: `b` to label `l`. `br_if l`: `ldr x0, [cond]; cbnz w0` to label `l`.
//! - `exit c k`: the exit sequence; the operands stay in their frame slots.
//! - `br_table ls d`: `ldr x0, [index]`, then for each target `i` `movz w1,
//!   #i; cmp w0, w1; b.eq`, then `b` to the default.
//! - a memory instruction: see [`mem_code`].
//!
//! A `b`, `b.cond`, `cbz` or `cbnz` takes a displacement in words from the
//! address of the branch itself, so a branch at byte `pos` to the label at
//! `offs[l]` has displacement `(offs[l] - pos) / 4` (choice 16 of
//! [`crate::a64::cfspec`]).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::templates::*;
#[cfg(verus_only)]
pub use crate::cftemplates::{flow_h, shift, zeros};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ----------------------------------------------------------------------------
// Branch instructions
// ----------------------------------------------------------------------------

/// `b` to the byte `rel` after the branch itself (`rel` a multiple of 4).
pub open spec fn b_i(rel: int) -> isa::Instr {
    isa::Instr::B { imm26: (rel / 4) as i32 }
}

/// `b.cond cc` to the byte `rel` after the branch itself.
pub open spec fn bcond_i(cc: u8, rel: int) -> isa::Instr {
    isa::Instr::BCond { cond: cc, imm19: (rel / 4) as i32 }
}

/// `cbz w0` (`iszero`) or `cbnz w0` to the byte `rel` after the branch itself.
pub open spec fn cb_i(iszero: bool, rel: int) -> isa::Instr {
    isa::Instr::CompareBranch { sf: isa::Width::W32, iszero, t: x0(), imm19: (rel / 4) as i32 }
}

/// The condition test: `ldr x0, [top of stack]; cbz/cbnz w0, rel`, at height
/// `h` with `nl` locals. `rel` is from the branch (the second instruction).
pub open spec fn cond_pre(nl: nat, h: nat, iszero: bool, rel: int) -> Seq<isa::Instr> {
    seq![load_slot(x0(), (nl + h - 1) as nat), cb_i(iszero, rel)]
}

/// The length of [`cond_pre`] (it does not depend on `rel`).
pub open spec fn cond_len(nl: nat, h: nat) -> nat {
    code_len(cond_pre(nl, h, true, 0))
}

// ----------------------------------------------------------------------------
// The code of a node
// ----------------------------------------------------------------------------

/// **The code of a node** at height `h` with `nl` locals, the labels in scope
/// at the byte offsets `offs` from its first byte.
pub open spec fn ctmpl(n: Node, nl: nat, h: nat, offs: Seq<int>) -> Seq<isa::Instr>
    decreases n, 0nat,
{
    match n {
        Node::Op(o) => tmpl(o, nl, h),
        Node::Mem(m) => mem_code(m, nl, h),
        Node::Then(a, b) => ctmpl(*a, nl, h, offs) + ctmpl(
            *b,
            nl,
            flow_h(*a, nl, h, offs.len()),
            shift(offs, csize(*a, nl, h, offs.len()) as int),
        ),
        Node::Block(b) => ctmpl(*b, nl, h, seq![csize(*b, nl, h, offs.len() + 1) as int] + offs),
        Node::Loop(b) => ctmpl(*b, nl, h, seq![0int] + offs),
        Node::If(t, e) => {
            let st = csize(*t, nl, (h - 1) as nat, offs.len() + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, offs.len() + 1) as int;
            cond_pre(nl, h, true, st + 8) + ctmpl(
                *t,
                nl,
                (h - 1) as nat,
                seq![st + 4 + se] + shift(offs, 8),
            ) + seq![b_i(se + 4)] + ctmpl(
                *e,
                nl,
                (h - 1) as nat,
                seq![se] + shift(offs, 12 + st),
            )
        },
        Node::Br(l) => seq![b_i(if l < offs.len() {
            offs[l as int]
        } else {
            0
        })],
        Node::BrIf(l) => cond_pre(nl, h, false, if l < offs.len() {
            offs[l as int] - 4
        } else {
            0
        }),
        Node::BrTable(ls, d) => brt_code(ls@, d, nl, h, offs),
        Node::Exit(c, _) => exit_seq(c as u16),
    }
}

// ----------------------------------------------------------------------------
// Memory instructions
// ----------------------------------------------------------------------------

/// The access width of a value of type `ty`: `i32` 4 bytes, the others 8.
pub open spec fn mty_sf(ty: MTy) -> isa::Width {
    match ty {
        MTy::I32 => isa::Width::W32,
        _ => isa::Width::W64,
    }
}

/// `ldr x3, [x28, #16 k]`: region `k`'s base, from the context's table.
pub open spec fn base_ld(k: nat) -> isa::Instr {
    isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: true,
        t: x3(),
        n: abi::ctx_reg(),
        imm12: (abi::base_off(k as int) / 8) as u16,
    }
}

/// The bounds check of the validator
/// (`clazel_codecheck::a64::spec::check_seq`) on `x1`, with `x0` and `x2` as
/// its scratch registers, region `k`, `n` bytes, and the displacements `r1`,
/// `r2` (in words, from the branch itself) of its two exits.
pub open spec fn mem_chk(k: nat, n: nat, r1: int, r2: int) -> clazel_codecheck::a64::spec::Chk {
    clazel_codecheck::a64::spec::Chk {
        k: k as int,
        n: n as int,
        i: x1(),
        t: x0(),
        bnd: x2(),
        r1: r1 as i32,
        r2: r2 as i32,
    }
}

/// The region of a memory instruction.
pub open spec fn mem_region(m: MemOp) -> nat {
    match m {
        MemOp::BoundsCheck { region, .. } => region as nat,
        MemOp::Load { region, .. } => region as nat,
        MemOp::Store { region, .. } => region as nat,
    }
}

/// The number of bytes the check of a memory instruction admits.
pub open spec fn mem_n(m: MemOp) -> nat {
    match m {
        MemOp::BoundsCheck { size, .. } => size as nat,
        MemOp::Load { ty, .. } => ty.size(),
        MemOp::Store { ty, .. } => ty.size(),
    }
}

/// The exit code of the stub after a memory instruction.
pub open spec fn mem_exit_code(m: MemOp) -> u16 {
    match m {
        MemOp::BoundsCheck { code, .. } => code as u16,
        _ => trap_code(),
    }
}

/// What a memory instruction does before its check: the operands into
/// registers (the index in `x1`, the value of a store in `x4`), and, for an
/// access, the region's base into `x3`.
pub open spec fn mem_pre(m: MemOp, nl: nat, h: nat) -> Seq<isa::Instr> {
    match m {
        MemOp::BoundsCheck { .. } => seq![load_slot(x1(), (nl + h - 1) as nat)],
        MemOp::Load { region, .. } => seq![
            load_slot(x1(), (nl + h - 1) as nat),
            base_ld(region as nat),
        ],
        MemOp::Store { region, .. } => seq![
            load_slot(x4(), (nl + h - 1) as nat),
            load_slot(x1(), (nl + h - 2) as nat),
            base_ld(region as nat),
        ],
    }
}

/// What a memory instruction does after its check passed: the access, and for
/// a load the store of the result to the slot of the index.
pub open spec fn mem_tail(m: MemOp, nl: nat, h: nat) -> Seq<isa::Instr> {
    match m {
        MemOp::BoundsCheck { .. } => seq![],
        MemOp::Load { ty, .. } => seq![
            isa::Instr::LoadStoreReg {
                sf: mty_sf(ty),
                load: true,
                t: x0(),
                n: x3(),
                m: x1(),
                s: false,
            },
            store_slot((nl + h - 1) as nat, x0()),
        ],
        MemOp::Store { ty, .. } => seq![
            isa::Instr::LoadStoreReg {
                sf: mty_sf(ty),
                load: false,
                t: x4(),
                n: x3(),
                m: x1(),
                s: false,
            },
        ],
    }
}

/// The displacement (in words, from the branch itself) of the check's first
/// exit, the `b.hs` at the third instruction of the check: over the rest of
/// the check (5 instructions), the tail and the `b` over the stub.
pub open spec fn mem_r1(m: MemOp, nl: nat, h: nat) -> int {
    (5 + mem_tail(m, nl, h).len() + 1) as int
}

/// The displacement of the check's second exit, the `b.hi` at the fifth
/// instruction.
pub open spec fn mem_r2(m: MemOp, nl: nat, h: nat) -> int {
    (3 + mem_tail(m, nl, h).len() + 1) as int
}

/// The bounds-check sequence of a memory instruction.
pub open spec fn mem_check(m: MemOp, nl: nat, h: nat) -> Seq<isa::Instr> {
    clazel_codecheck::a64::spec::check_seq(
        mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h)),
    )
}

/// **The code of a memory instruction** (choice 11 of [`crate::cfspec`]): the
/// operands and the region's base in registers; the validator's bounds check,
/// whose two exits go to the stub; the access; a `b` over the stub; the stub
/// (an exit sequence), so that check and access are one basic block.
pub open spec fn mem_code(m: MemOp, nl: nat, h: nat) -> Seq<isa::Instr> {
    mem_pre(m, nl, h) + mem_check(m, nl, h) + mem_tail(m, nl, h) + seq![
        b_i(code_len(exit_seq(mem_exit_code(m))) as int + 4),
    ] + exit_seq(mem_exit_code(m))
}

// ----------------------------------------------------------------------------
// br_table
// ----------------------------------------------------------------------------

/// The chain's entry for target `i`: `movz w1, #i; cmp w0, w1; b.eq rel`, with
/// `rel` from the `b.eq`.
pub open spec fn brt_entry(i: nat, rel: int) -> Seq<isa::Instr> {
    seq![
        isa::Instr::MoveWide {
            sf: isa::Width::W32,
            opcode: isa::MoveWideOp::Z,
            d: x1(),
            imm16: i as u16,
            hw: 0,
        },
        cmp_rr(isa::Width::W32, x0(), x1()),
        bcond_i(0, rel),
    ]
}

/// The length of a chain entry (it does not depend on `i` or `rel`).
pub open spec fn brt_e() -> int {
    code_len(brt_entry(0, 0)) as int
}

/// The length of what comes before the chain: `ldr x0, [index]`.
pub open spec fn brt_p0(nl: nat, h: nat) -> int {
    code_len(seq![load_slot(x0(), (nl + h - 1) as nat)]) as int
}

/// The displacement to label `l` from a jump at byte `pos`.
pub open spec fn brt_rel(offs: Seq<int>, l: usize, pos: int) -> int {
    if l < offs.len() {
        offs[l as int] - pos
    } else {
        0
    }
}

/// The chain from entry `i` on: entry `j` begins `p0 + j e` bytes in, and its
/// `b.eq` is its third instruction.
pub open spec fn brt_entries(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat) -> Seq<isa::Instr>
    decreases ls.len() - i,
{
    if i >= ls.len() {
        seq![]
    } else {
        brt_entry(i, brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8)) + brt_entries(
            ls,
            offs,
            p0,
            i + 1,
        )
    }
}

/// **The code of `br_table ls d`** (choice 10 of [`crate::cfspec`]): `ldr x0,
/// [index]`, a compare and `b.eq` per target, then a `b` to the default.
pub open spec fn brt_code(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>) -> Seq<
    isa::Instr,
> {
    let p0 = brt_p0(nl, h);
    seq![load_slot(x0(), (nl + h - 1) as nat)] + brt_entries(ls, offs, p0, 0) + seq![
        b_i(brt_rel(offs, d, p0 + ls.len() * brt_e())),
    ]
}

/// The length in bytes of a node's code (it does not depend on the values of
/// the label offsets, only on how many there are:
/// [`crate::a64::cflens::lemma_ctmpl_len`]).
pub open spec fn csize(n: Node, nl: nat, h: nat, depth: nat) -> nat
    decreases n, 1nat,
{
    code_len(ctmpl(n, nl, h, zeros(depth)))
}

/// The largest code this slice translates, in bytes: `2^19`, well below the
/// reach of a `b.cond` or `cbz` (1 MiB each way, 19-bit signed words), so
/// every displacement fits ([`crate::a64::cfproofs::labels_fit`]).
pub open spec fn max_size() -> nat {
    0x8_0000
}

/// The program `n` of a function with `nl` locals has a translation: its
/// frame holds the locals, its analysis, entered with an empty stack and the
/// return label in scope, is defined, every node in it has a template
/// ([`templated`]), every exit code is 16 bits ([`codes_ok`]), and the code is
/// at most [`max_size`] bytes.
pub open spec fn cf_prog_ok(n: Node, nl: nat) -> bool {
    nl <= max_slots() && cf_flow(n, nl, 0, 1) is Some && templated(n) && codes_ok(n) && csize(
        n,
        nl,
        0,
        1,
    ) <= max_size()
}

} // verus!
