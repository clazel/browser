//! The templates for structured control flow (jit.md J.9, second slice), as
//! spec functions: [`ctmpl`] is the x86-64 code of a [`Node`], given the
//! offsets of the labels in scope; [`csize`] is its length in bytes, which is
//! what a `block`'s label offset is made from. The refinement proofs are in
//! [`crate::cfproofs`]; the statement is [`crate::cfcontract::cf_refines`].
//!
//! The layout (jit.md J.9: "composition over structured control flow", with
//! the labels resolved to code offsets):
//!
//! - `then a b`: the code of `a`, then the code of `b`; `b`'s labels are `a`'s
//!   shifted by the length of `a`'s code.
//! - `block b`: the code of `b`, with a new label 0 at the end of it.
//! - `loop b`: the code of `b`, with a new label 0 at its start.
//! - `if t e`: `mov rax, [cond]; test eax, eax; je Lelse; t; jmp Lend; Lelse:
//!   e; Lend:`, with a new label 0 at `Lend` in each arm.
//! - `br l`: `jmp` to label `l`. `br_if l`: `mov rax, [cond]; test eax, eax;
//!   jne` to label `l`.
//! - `exit c k`: the exit sequence; the operands stay in their frame slots.
//!
//! A `jmp` or `jcc` has a 32-bit displacement from the end of the
//! instruction, so every label offset is `target - end of this jump`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfproofs::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `jmp` to the byte `rel` after the end of the instruction.
pub open spec fn jmp_i(rel: int) -> x64::Instr {
    x64::Instr::Jmp { rel: rel as i32 }
}

/// `jcc cc` to the byte `rel` after the end of the instruction.
pub open spec fn jcc_i(cc: u8, rel: int) -> x64::Instr {
    x64::Instr::Jcc { cc: cc, rel: rel as i32 }
}

/// The offsets [`csize`] is defined with: `depth` labels, all at 0 (the length
/// of the code does not depend on them: [`crate::cflens::lemma_ctmpl_len`]).
pub open spec fn zeros(depth: nat) -> Seq<int> {
    Seq::new(depth, |i: int| 0int)
}

/// The labels of `offs`, as seen from `d` bytes further on.
pub open spec fn shift(offs: Seq<int>, d: int) -> Seq<int> {
    offs.map_values(|o: int| o - d)
}

/// The condition test: `mov rax, [top of stack]; test eax, eax; jcc cc rel`,
/// at height `h` with `nl` locals.
pub open spec fn cond_pre(nl: nat, h: nat, cc: u8, rel: int) -> Seq<x64::Instr> {
    seq![
        load_slot(rax(), (nl + h - 1) as nat),
        x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() },
        jcc_i(cc, rel),
    ]
}

/// The length of [`cond_pre`] (it does not depend on `rel` or `cc`).
pub open spec fn cond_len(nl: nat, h: nat) -> nat {
    code_len(cond_pre(nl, h, 0, 0))
}

/// The height after a node, when it falls through (else the same height).
pub open spec fn flow_h(n: Node, nl: nat, h: nat, depth: nat) -> nat {
    match cf_flow(n, nl, h, depth) {
        Some(Flow::Falls(h1)) => h1,
        _ => h,
    }
}

/// **The code of a node** at height `h` with `nl` locals, the labels in scope
/// at the byte offsets `offs` from its first byte. Empty for the nodes this
/// slice has no template for ([`cf_flow`] refuses them).
pub open spec fn ctmpl(n: Node, nl: nat, h: nat, offs: Seq<int>) -> Seq<x64::Instr>
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
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, offs.len() + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, offs.len() + 1) as int;
            cond_pre(nl, h, 4, st + 5) + ctmpl(
                *t,
                nl,
                (h - 1) as nat,
                seq![st + 5 + se] + shift(offs, p),
            ) + seq![jmp_i(se)] + ctmpl(
                *e,
                nl,
                (h - 1) as nat,
                seq![se] + shift(offs, p + st + 5),
            )
        },
        Node::Br(l) => seq![jmp_i(if l < offs.len() {
            offs[l as int] - 5
        } else {
            0
        })],
        Node::BrIf(l) => cond_pre(nl, h, 5, if l < offs.len() {
            offs[l as int] - cond_len(nl, h) as int
        } else {
            0
        }),
        Node::BrTable(ls, d) => brt_code(ls@, d, nl, h, offs),
        Node::Exit(c, _) => exit_seq(c),
    }
}

// ----------------------------------------------------------------------------
// Memory instructions
// ----------------------------------------------------------------------------

/// The operand size of an access of type `ty`: `i32` 4 bytes, the others 8.
pub open spec fn mty_sz(ty: MTy) -> x64::Size {
    match ty {
        MTy::I32 => x64::Size::W32,
        _ => x64::Size::W64,
    }
}

/// `[rsi + rcx]`: a region base plus the checked index (scale 1).
pub open spec fn ix_mem() -> x64::Mem {
    x64::Mem { base: rsi(), index: Some(x64::Index { reg: rcx(), scale: 0 }), disp: 0 }
}

/// `[r15 + 16 k]`: region `k`'s base, in the context's table.
pub open spec fn base_mem(k: nat) -> x64::Mem {
    x64::Mem { base: abi::ctx_reg(), index: None, disp: abi::base_off(k as int) as i32 }
}

/// The bounds check of the validator (`clazel_codecheck::spec::check_seq`)
/// on `rcx`, with `rdx` and `rax` as its scratch registers, region `k`, `n`
/// bytes, and the displacements `r1`, `r2` of its two exits.
pub open spec fn mem_chk(k: nat, n: nat, r1: int, r2: int) -> clazel_codecheck::spec::Chk {
    clazel_codecheck::spec::Chk {
        k: k as int,
        n: n as int,
        i: rcx(),
        t: rdx(),
        z: rax(),
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
pub open spec fn mem_exit_code(m: MemOp) -> u32 {
    match m {
        MemOp::BoundsCheck { code, .. } => code,
        _ => trap_code(),
    }
}

/// What a memory instruction does before its check: the operands into
/// registers (the index in `rcx`, the value of a store in `rdi`), and, for an
/// access, the region's base into `rsi`.
pub open spec fn mem_pre(m: MemOp, nl: nat, h: nat) -> Seq<x64::Instr> {
    match m {
        MemOp::BoundsCheck { .. } => seq![load_slot(rcx(), (nl + h - 1) as nat)],
        MemOp::Load { region, .. } => seq![
            load_slot(rcx(), (nl + h - 1) as nat),
            x64::Instr::MovLoad { sz: x64::Size::W64, dst: rsi(), mem: base_mem(region as nat) },
        ],
        MemOp::Store { region, .. } => seq![
            load_slot(rdi(), (nl + h - 1) as nat),
            load_slot(rcx(), (nl + h - 2) as nat),
            x64::Instr::MovLoad { sz: x64::Size::W64, dst: rsi(), mem: base_mem(region as nat) },
        ],
    }
}

/// What a memory instruction does after its check passed: the access, and for
/// a load the store of the result to the slot of the index.
pub open spec fn mem_tail(m: MemOp, nl: nat, h: nat) -> Seq<x64::Instr> {
    match m {
        MemOp::BoundsCheck { .. } => seq![],
        MemOp::Load { ty, .. } => seq![
            x64::Instr::MovLoad { sz: mty_sz(ty), dst: rax(), mem: ix_mem() },
            store_slot((nl + h - 1) as nat, rax()),
        ],
        MemOp::Store { ty, .. } => seq![
            x64::Instr::MovStore { sz: mty_sz(ty), mem: ix_mem(), src: rdi() },
        ],
    }
}

/// The length of the bounds-check sequence's instructions from the `j`th on
/// (what an exit jumps over: `j` is 3 for the first, 5 for the second).
pub open spec fn chk_len_from(j: nat) -> nat {
    code_len(clazel_codecheck::spec::check_seq(mem_chk(0, 1, 0, 0)).skip(j as int))
}

/// The displacement of the check's first exit: over the rest of the check,
/// the tail and the `jmp` over the stub.
pub open spec fn mem_r1(m: MemOp, nl: nat, h: nat) -> int {
    (chk_len_from(3) + code_len(mem_tail(m, nl, h)) + 5) as int
}

/// The displacement of the check's second exit.
pub open spec fn mem_r2(m: MemOp, nl: nat, h: nat) -> int {
    (chk_len_from(5) + code_len(mem_tail(m, nl, h)) + 5) as int
}

/// The bounds-check sequence of a memory instruction.
pub open spec fn mem_check(m: MemOp, nl: nat, h: nat) -> Seq<x64::Instr> {
    clazel_codecheck::spec::check_seq(
        mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h)),
    )
}

/// **The code of a memory instruction** (choice 11): the operands and the
/// region's base in registers; the validator's bounds check, whose two exits
/// go to the stub; the access; a `jmp` over the stub; the stub (an exit
/// sequence), so that check and access are one basic block.
pub open spec fn mem_code(m: MemOp, nl: nat, h: nat) -> Seq<x64::Instr> {
    mem_pre(m, nl, h) + mem_check(m, nl, h) + mem_tail(m, nl, h) + seq![
        jmp_i(code_len(exit_seq(mem_exit_code(m))) as int),
    ] + exit_seq(mem_exit_code(m))
}

// ----------------------------------------------------------------------------
// br_table
// ----------------------------------------------------------------------------

/// The chain's entry for target `i`: `mov edx, i; cmp eax, edx; je rel`.
pub open spec fn brt_entry(i: nat, rel: int) -> Seq<x64::Instr> {
    seq![
        x64::Instr::MovImm32 { dst: rdx(), imm_u32: i as u32 },
        x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: x64::Size::W32, dst: rax(), src: rdx() },
        jcc_i(4, rel),
    ]
}

/// The length of a chain entry (it does not depend on `i` or `rel`).
pub open spec fn brt_e() -> int {
    code_len(brt_entry(0, 0)) as int
}

/// The length of what comes before the chain: `mov rax, [index]`.
pub open spec fn brt_p0(nl: nat, h: nat) -> int {
    code_len(seq![load_slot(rax(), (nl + h - 1) as nat)]) as int
}

/// The displacement to label `l` from a jump that ends `end` bytes in.
pub open spec fn brt_rel(offs: Seq<int>, l: usize, end: int) -> int {
    if l < offs.len() {
        offs[l as int] - end
    } else {
        0
    }
}

/// The chain from entry `i` on: entry `j` ends `p0 + (j + 1) e` bytes in.
pub open spec fn brt_entries(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat) -> Seq<x64::Instr>
    decreases ls.len() - i,
{
    if i >= ls.len() {
        seq![]
    } else {
        brt_entry(i, brt_rel(offs, ls[i as int], p0 + (i + 1) * brt_e())) + brt_entries(
            ls,
            offs,
            p0,
            i + 1,
        )
    }
}

/// **The code of `br_table ls d`** (choice 10): `mov rax, [index]`, a compare
/// and `je` per target, then a `jmp` to the default.
pub open spec fn brt_code(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>) -> Seq<
    x64::Instr,
> {
    let p0 = brt_p0(nl, h);
    seq![load_slot(rax(), (nl + h - 1) as nat)] + brt_entries(ls, offs, p0, 0) + seq![
        jmp_i(brt_rel(offs, d, p0 + ls.len() * brt_e() + 5)),
    ]
}

/// The length in bytes of a node's code (it does not depend on the values of
/// the label offsets, only on how many there are: [`lemma_ctmpl_len`]).
pub open spec fn csize(n: Node, nl: nat, h: nat, depth: nat) -> nat
    decreases n, 1nat,
{
    code_len(ctmpl(n, nl, h, zeros(depth)))
}

/// The largest code this slice translates, in bytes: well below `2^31`, so
/// every displacement fits a `rel32` ([`crate::cfproofs::labels_fit`]).
pub open spec fn max_size() -> nat {
    0x2000_0000
}

/// The program `n` of a function with `nl` locals has a translation: its
/// frame holds the locals, its analysis, entered with an empty stack and the return label in scope, is
/// defined, every node in it has a template ([`templated`]), and the code is at most
/// [`max_size`] bytes.
pub open spec fn cf_prog_ok(n: Node, nl: nat) -> bool {
    nl <= max_slots() && cf_flow(n, nl, 0, 1) is Some && templated(n) && csize(n, nl, 0, 1)
        <= max_size()
}

} // verus!
