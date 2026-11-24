//! The templates as lists of the validator's units, and where a jump may land
//! (jit.md item J.9, "every emitted blob is accepted", x86-64).
//!
//! [`utmpl`] is [`ctmpl`] cut into the units the validator's scan sees: every
//! instruction is a unit of its own, except the bounds-check sequence of a
//! memory instruction (8 instructions) and every exit sequence (3).
//! [`lemma_utmpl_flat`]: the instructions of the units are `ctmpl`.
//!
//! [`bs`] says where a jump inside a node may land, as a byte position from
//! the node's start, other than at one of the labels it was given: the
//! node's own start and end, the starts and ends of its parts, and the stub
//! after a memory instruction (where the check's exits go). [`prot`] is where
//! no jump lands: in a memory instruction, the start of the bounds-check
//! sequence and the start of the access, because the scan forgets what it
//! knows at a jump target and the access needs what the load of the region's
//! base and the check told it. They are disjoint ([`lemma_bs_prot`]), and
//! every position of [`bs`] is a unit start or the end ([`lemma_bs_ubi`]).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::cfunits::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The units of a memory instruction: the operands and the base one
/// instruction at a time, the bounds-check sequence, the access, the `jmp`
/// over the stub, and the stub (an exit sequence).
pub open spec fn mem_units(m: MemOp, nl: nat, h: nat) -> Us {
    ones(mem_pre(m, nl, h)) + seq![mem_check(m, nl, h)] + ones(mem_tail(m, nl, h)) + seq![
        seq![jmp_i(code_len(exit_seq(mem_exit_code(m))) as int)],
        exit_seq(mem_exit_code(m)),
    ]
}

/// **[`ctmpl`] as units.**
pub open spec fn utmpl(n: Node, nl: nat, h: nat, offs: Seq<int>) -> Us
    decreases n,
{
    match n {
        Node::Op(o) => ones(tmpl(o, nl, h)),
        Node::Mem(m) => mem_units(m, nl, h),
        Node::Then(a, b) => utmpl(*a, nl, h, offs) + utmpl(
            *b,
            nl,
            flow_h(*a, nl, h, offs.len()),
            shift(offs, csize(*a, nl, h, offs.len()) as int),
        ),
        Node::Block(b) => utmpl(*b, nl, h, seq![csize(*b, nl, h, offs.len() + 1) as int] + offs),
        Node::Loop(b) => utmpl(*b, nl, h, seq![0int] + offs),
        Node::If(t, e) => {
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, offs.len() + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, offs.len() + 1) as int;
            ones(cond_pre(nl, h, 4, st + 5)) + utmpl(
                *t,
                nl,
                (h - 1) as nat,
                seq![st + 5 + se] + shift(offs, p),
            ) + seq![seq![jmp_i(se)]] + utmpl(
                *e,
                nl,
                (h - 1) as nat,
                seq![se] + shift(offs, p + st + 5),
            )
        },
        Node::Br(_) => ones(ctmpl(n, nl, h, offs)),
        Node::BrIf(_) => ones(ctmpl(n, nl, h, offs)),
        Node::BrTable(_, _) => ones(ctmpl(n, nl, h, offs)),
        Node::Exit(c, _) => seq![exit_seq(c)],
    }
}

/// The byte offset of the stub of a memory instruction: after the operands,
/// the check, the access and the `jmp`.
pub open spec fn stub_off(m: MemOp, nl: nat, h: nat) -> int {
    (code_len(mem_pre(m, nl, h)) + code_len(mem_check(m, nl, h)) + code_len(mem_tail(m, nl, h))
        + 5) as int
}

/// **Where a jump of the node may land**, other than at a label it was
/// given, as a byte position from the node's first byte.
pub open spec fn bs(n: Node, nl: nat, h: nat, d: nat, x: int) -> bool
    decreases n,
{
    match n {
        Node::Mem(m) => x == 0 || x == stub_off(m, nl, h) || x == csize(n, nl, h, d) as int,
        Node::Then(a, b) => bs(*a, nl, h, d, x) || bs(
            *b,
            nl,
            flow_h(*a, nl, h, d),
            d,
            x - csize(*a, nl, h, d) as int,
        ),
        Node::Block(b) => bs(*b, nl, h, d + 1, x),
        Node::Loop(b) => bs(*b, nl, h, d + 1, x),
        Node::If(t, e) => {
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            x == 0 || bs(*t, nl, (h - 1) as nat, d + 1, x - p) || bs(
                *e,
                nl,
                (h - 1) as nat,
                d + 1,
                x - (p + st + 5),
            )
        },
        _ => x == 0 || x == csize(n, nl, h, d) as int,
    }
}

/// **Where no jump lands**: inside a memory instruction, the start of the
/// check and the start of the access.
pub open spec fn prot(n: Node, nl: nat, h: nat, d: nat, x: int) -> bool
    decreases n,
{
    match n {
        Node::Mem(m) => x == code_len(mem_pre(m, nl, h)) as int || x == (code_len(
            mem_pre(m, nl, h),
        ) + code_len(mem_check(m, nl, h))) as int,
        Node::Then(a, b) => prot(*a, nl, h, d, x) || prot(
            *b,
            nl,
            flow_h(*a, nl, h, d),
            d,
            x - csize(*a, nl, h, d) as int,
        ),
        Node::Block(b) => prot(*b, nl, h, d + 1, x),
        Node::Loop(b) => prot(*b, nl, h, d + 1, x),
        Node::If(t, e) => {
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            prot(*t, nl, (h - 1) as nat, d + 1, x - p) || prot(
                *e,
                nl,
                (h - 1) as nat,
                d + 1,
                x - (p + st + 5),
            )
        },
        _ => false,
    }
}

// ----------------------------------------------------------------------------
// The units are the template
// ----------------------------------------------------------------------------

/// The instructions of a one-unit list.
pub proof fn lemma_uflat_one(u: Seq<x64::Instr>)
    ensures
        uflat(seq![u]) =~= u,
{
    let s = seq![u];
    assert(s.skip(1) =~= Seq::<Seq<x64::Instr>>::empty());
    assert(uflat(s) =~= u + uflat(s.skip(1)));
    assert(u + Seq::<x64::Instr>::empty() =~= u);
}

/// The instructions of a two-unit list.
pub proof fn lemma_uflat_two(u: Seq<x64::Instr>, v: Seq<x64::Instr>)
    ensures
        uflat(seq![u, v]) =~= u + v,
{
    let s = seq![u, v];
    assert(s.skip(1) =~= seq![v]);
    lemma_uflat_one(v);
    assert(uflat(s) =~= u + uflat(s.skip(1)));
}

/// The units of a memory instruction are its code.
pub proof fn lemma_mem_units_flat(m: MemOp, nl: nat, h: nat)
    ensures
        uflat(mem_units(m, nl, h)) =~= mem_code(m, nl, h),
{
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![jmp_i(code_len(exit_seq(mem_exit_code(m))) as int)];
    let stub = exit_seq(mem_exit_code(m));
    lemma_uflat_ones(pre);
    lemma_uflat_ones(tail);
    lemma_uflat_one(chk);
    lemma_uflat_two(jm, stub);
    lemma_uflat_cat(ones(pre), seq![chk]);
    lemma_uflat_cat(ones(pre) + seq![chk], ones(tail));
    lemma_uflat_cat(ones(pre) + seq![chk] + ones(tail), seq![jm, stub]);
    assert(uflat(mem_units(m, nl, h)) =~= pre + chk + tail + (jm + stub));
    assert(mem_code(m, nl, h) =~= pre + chk + tail + jm + stub);
}

/// **The units of [`utmpl`] are the instructions of [`ctmpl`].**
pub proof fn lemma_utmpl_flat(n: Node, nl: nat, h: nat, offs: Seq<int>)
    ensures
        uflat(utmpl(n, nl, h, offs)) =~= ctmpl(n, nl, h, offs),
    decreases n,
{
    let d = offs.len();
    match n {
        Node::Op(o) => {
            lemma_uflat_ones(tmpl(o, nl, h));
        },
        Node::Mem(m) => {
            lemma_mem_units_flat(m, nl, h);
        },
        Node::Then(a, b) => {
            let ob = shift(offs, csize(*a, nl, h, d) as int);
            lemma_utmpl_flat(*a, nl, h, offs);
            lemma_utmpl_flat(*b, nl, flow_h(*a, nl, h, d), ob);
            lemma_uflat_cat(
                utmpl(*a, nl, h, offs),
                utmpl(*b, nl, flow_h(*a, nl, h, d), ob),
            );
        },
        Node::Block(b) => {
            lemma_utmpl_flat(*b, nl, h, seq![csize(*b, nl, h, d + 1) as int] + offs);
        },
        Node::Loop(b) => {
            lemma_utmpl_flat(*b, nl, h, seq![0int] + offs);
        },
        Node::If(t, e) => {
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 5 + se] + shift(offs, p);
            let oe = seq![se] + shift(offs, p + st + 5);
            let cp = cond_pre(nl, h, 4, st + 5);
            lemma_utmpl_flat(*t, nl, (h - 1) as nat, ot);
            lemma_utmpl_flat(*e, nl, (h - 1) as nat, oe);
            lemma_uflat_ones(cp);
            lemma_uflat_one(seq![jmp_i(se)]);
            lemma_uflat_cat(ones(cp), utmpl(*t, nl, (h - 1) as nat, ot));
            lemma_uflat_cat(ones(cp) + utmpl(*t, nl, (h - 1) as nat, ot), seq![seq![jmp_i(se)]]);
            lemma_uflat_cat(
                ones(cp) + utmpl(*t, nl, (h - 1) as nat, ot) + seq![seq![jmp_i(se)]],
                utmpl(*e, nl, (h - 1) as nat, oe),
            );
            assert(uflat(utmpl(n, nl, h, offs)) =~= cp + ctmpl(*t, nl, (h - 1) as nat, ot) + seq![
                jmp_i(se),
            ] + ctmpl(*e, nl, (h - 1) as nat, oe));
        },
        Node::Br(_) => {
            lemma_uflat_ones(ctmpl(n, nl, h, offs));
        },
        Node::BrIf(_) => {
            lemma_uflat_ones(ctmpl(n, nl, h, offs));
        },
        Node::BrTable(_, _) => {
            lemma_uflat_ones(ctmpl(n, nl, h, offs));
        },
        Node::Exit(c, _) => {
            lemma_uflat_one(exit_seq(c));
        },
    }
}

/// The byte length of the units is `csize`.
pub proof fn lemma_utmpl_blen(n: Node, nl: nat, h: nat, offs: Seq<int>)
    ensures
        blen(utmpl(n, nl, h, offs)) == csize(n, nl, h, offs.len()),
{
    lemma_utmpl_flat(n, nl, h, offs);
    lemma_blen_flat(utmpl(n, nl, h, offs));
    crate::cflens::lemma_ctmpl_len(n, nl, h, offs);
}

} // verus!
