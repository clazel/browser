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
        Node::Mem(_) => seq![],
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
        Node::BrTable(_, _) => seq![],
        Node::Exit(c, _) => exit_seq(c),
    }
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
