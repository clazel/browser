//! The positions a jump may and may not land on ([`bs`] and [`prot`] of
//! [`crate::cfaccept`]): they are inside the node, disjoint, and the first
//! are unit starts (jit.md item J.9, "every emitted blob is accepted",
//! x86-64).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfaccept::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::cfunits::*;
#[cfg(verus_only)]
use crate::runseq::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A memory instruction's layout: operands (8 to 24 bytes), the check (47),
/// the access, the `jmp` (5) and the stub (14).
pub proof fn lemma_mem_csize(m: MemOp, nl: nat, h: nat, d: nat)
    requires
        mem_region(m) < 16,
    ensures
        csize(Node::Mem(m), nl, h, d) == stub_off(m, nl, h) + 14,
        code_len(mem_pre(m, nl, h)) >= 8,
        code_len(mem_check(m, nl, h)) == 47,
        code_len(mem_tail(m, nl, h)) >= 0,
        stub_off(m, nl, h) == code_len(mem_pre(m, nl, h)) + 47 + code_len(mem_tail(m, nl, h)) + 5,
{
    lemma_mem_parts_len(m, nl, h);
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![jmp_i(code_len(exit_seq(mem_exit_code(m))) as int)];
    let stub = exit_seq(mem_exit_code(m));
    crate::cflens::lemma_jmp_len(code_len(stub) as int);
    lemma_code_len_one(jmp_i(code_len(stub) as int));
    lemma_code_len_append(pre, chk);
    lemma_code_len_append(pre + chk, tail);
    lemma_code_len_append(pre + chk + tail, jm);
    lemma_code_len_append(pre + chk + tail + jm, stub);
    assert(csize(Node::Mem(m), nl, h, d) == code_len(mem_code(m, nl, h)));
}

/// A `nop` has no code.
pub proof fn lemma_nop_size(nl: nat, h: nat, d: nat)
    ensures
        csize(Node::Op(Op::Nop), nl, h, d) == 0,
{
    assert(tmpl(Op::Nop, nl, h) =~= Seq::<x64::Instr>::empty());
}

/// What [`lemma_bs_facts`] says about a node.
pub open spec fn bs_facts(n: Node, nl: nat, h: nat, d: nat) -> bool {
    bs(n, nl, h, d, 0) && bs(n, nl, h, d, csize(n, nl, h, d) as int) && (forall|x: int|
        #[trigger] bs(n, nl, h, d, x) ==> 0 <= x <= csize(n, nl, h, d) as int) && (forall|x: int|
        #[trigger] prot(n, nl, h, d, x) ==> 0 < x < csize(n, nl, h, d) as int) && (forall|x: int|
        !(#[trigger] bs(n, nl, h, d, x) && prot(n, nl, h, d, x)))
}

/// `then`, from the facts of its parts: the second part starts `sa` bytes in.
proof fn lemma_bs_then(
    a: Node,
    b: Node,
    nl: nat,
    h: nat,
    d: nat,
    h1: nat,
    sb: nat,
)
    requires
        h1 == flow_h(a, nl, h, d),
        csize(Node::Then(Box::new(a), Box::new(b)), nl, h, d) == csize(a, nl, h, d) + sb,
        bs_facts(a, nl, h, d),
        bs(b, nl, h1, d, 0),
        bs(b, nl, h1, d, sb as int),
        forall|x: int| #[trigger] bs(b, nl, h1, d, x) ==> 0 <= x <= sb as int,
        forall|x: int| #[trigger] prot(b, nl, h1, d, x) ==> 0 < x < sb as int,
        forall|x: int| !(#[trigger] bs(b, nl, h1, d, x) && prot(b, nl, h1, d, x)),
    ensures
        bs_facts(Node::Then(Box::new(a), Box::new(b)), nl, h, d),
{
    let t = Node::Then(Box::new(a), Box::new(b));
    let sa = csize(a, nl, h, d) as int;
    assert(bs(t, nl, h, d, 0));
    assert(bs(b, nl, h1, d, sb as int));
    assert(bs(t, nl, h, d, sa + sb as int));
    assert forall|x: int| #[trigger] bs(t, nl, h, d, x) implies 0 <= x <= sa + sb by {
        if bs(a, nl, h, d, x) {
        } else {
            assert(bs(b, nl, h1, d, x - sa));
        }
    }
    assert forall|x: int| #[trigger] prot(t, nl, h, d, x) implies 0 < x < sa + sb by {
        if prot(a, nl, h, d, x) {
        } else {
            assert(prot(b, nl, h1, d, x - sa));
        }
    }
    assert forall|x: int| !(#[trigger] bs(t, nl, h, d, x) && prot(t, nl, h, d, x)) by {
        if bs(t, nl, h, d, x) && prot(t, nl, h, d, x) {
            if bs(a, nl, h, d, x) {
                if prot(a, nl, h, d, x) {
                } else {
                    assert(prot(b, nl, h1, d, x - sa));
                }
            } else {
                assert(bs(b, nl, h1, d, x - sa));
                if prot(a, nl, h, d, x) {
                } else {
                    assert(prot(b, nl, h1, d, x - sa));
                }
            }
        }
    }
}

/// `if`, from the facts of its arms.
proof fn lemma_bs_if(t: Node, e: Node, nl: nat, h: nat, d: nat)
    requires
        1 <= h,
        bs_facts(t, nl, (h - 1) as nat, d + 1),
        bs_facts(e, nl, (h - 1) as nat, d + 1),
    ensures
        bs_facts(Node::If(Box::new(t), Box::new(e)), nl, h, d),
{
    lemma_csize_if(t, e, nl, h, d);
    let n = Node::If(Box::new(t), Box::new(e));
    let h0 = (h - 1) as nat;
    let p = cond_len(nl, h) as int;
    let st = csize(t, nl, h0, d + 1) as int;
    let se = csize(e, nl, h0, d + 1) as int;
    assert(bs(n, nl, h, d, 0));
    assert(bs(e, nl, h0, d + 1, se));
    assert(bs(n, nl, h, d, p + st + 5 + se));
    assert forall|x: int| #[trigger] bs(n, nl, h, d, x) implies 0 <= x <= p + st + 5 + se by {
        if x == 0 {
        } else if bs(t, nl, h0, d + 1, x - p) {
        } else {
            assert(bs(e, nl, h0, d + 1, x - (p + st + 5)));
        }
    }
    assert forall|x: int| #[trigger] prot(n, nl, h, d, x) implies 0 < x < p + st + 5 + se by {
        if prot(t, nl, h0, d + 1, x - p) {
        } else {
            assert(prot(e, nl, h0, d + 1, x - (p + st + 5)));
        }
    }
    assert forall|x: int| !(#[trigger] bs(n, nl, h, d, x) && prot(n, nl, h, d, x)) by {
        if bs(n, nl, h, d, x) && prot(n, nl, h, d, x) {
            if x == 0 {
                if prot(t, nl, h0, d + 1, x - p) {
                } else {
                    assert(prot(e, nl, h0, d + 1, x - (p + st + 5)));
                }
            } else if bs(t, nl, h0, d + 1, x - p) {
                if prot(t, nl, h0, d + 1, x - p) {
                } else {
                    assert(prot(e, nl, h0, d + 1, x - (p + st + 5)));
                }
            } else {
                assert(bs(e, nl, h0, d + 1, x - (p + st + 5)));
                if prot(t, nl, h0, d + 1, x - p) {
                } else {
                    assert(prot(e, nl, h0, d + 1, x - (p + st + 5)));
                }
            }
        }
    }
}

/// **Where a jump may land is inside the node, where none may is strictly
/// inside it, and the two are disjoint.** The node's start and end are
/// among the first.
pub proof fn lemma_bs_facts(n: Node, nl: nat, h: nat, d: nat)
    requires
        cf_flow(n, nl, h, d) is Some,
    ensures
        bs_facts(n, nl, h, d),
    decreases n,
{
    match n {
        Node::Mem(m) => {
            lemma_mem_csize(m, nl, h, d);
            assert forall|x: int| !(#[trigger] bs(n, nl, h, d, x) && prot(n, nl, h, d, x)) by {}
        },
        Node::Then(a, b) => {
            lemma_bs_facts(*a, nl, h, d);
            lemma_csize_then(*a, *b, nl, h, d);
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    lemma_bs_facts(*b, nl, h1, d);
                    assert(flow_h(*a, nl, h, d) == h1);
                    lemma_bs_then(*a, *b, nl, h, d, h1, csize(*b, nl, h1, d));
                },
                Some(Flow::Dead) => {
                    assert(*b == Node::Op(Op::Nop));
                    lemma_nop_size(nl, h, d);
                    assert(flow_h(*a, nl, h, d) == h);
                    assert forall|y: int| #[trigger] bs(*b, nl, h, d, y) == (y == 0) by {}
                    assert forall|y: int| !prot(*b, nl, h, d, y) by {}
                    lemma_bs_then(*a, *b, nl, h, d, h, 0);
                },
                None => {},
            }
        },
        Node::Block(b) => {
            lemma_csize_block(*b, nl, h, d);
            lemma_bs_facts(*b, nl, h, d + 1);
            let sz = csize(*b, nl, h, d + 1) as int;
            assert(bs(n, nl, h, d, 0));
            assert(bs(n, nl, h, d, sz));
            assert forall|x: int| #[trigger] bs(n, nl, h, d, x) implies 0 <= x <= sz by {
                assert(bs(*b, nl, h, d + 1, x));
            }
            assert forall|x: int| #[trigger] prot(n, nl, h, d, x) implies 0 < x < sz by {
                assert(prot(*b, nl, h, d + 1, x));
            }
            assert forall|x: int| !(#[trigger] bs(n, nl, h, d, x) && prot(n, nl, h, d, x)) by {
                assert(bs(n, nl, h, d, x) == bs(*b, nl, h, d + 1, x));
                assert(prot(n, nl, h, d, x) == prot(*b, nl, h, d + 1, x));
            }
        },
        Node::Loop(b) => {
            lemma_csize_loop(*b, nl, h, d);
            lemma_bs_facts(*b, nl, h, d + 1);
            let sz = csize(*b, nl, h, d + 1) as int;
            assert(bs(n, nl, h, d, 0));
            assert(bs(n, nl, h, d, sz));
            assert forall|x: int| #[trigger] bs(n, nl, h, d, x) implies 0 <= x <= sz by {
                assert(bs(*b, nl, h, d + 1, x));
            }
            assert forall|x: int| #[trigger] prot(n, nl, h, d, x) implies 0 < x < sz by {
                assert(prot(*b, nl, h, d + 1, x));
            }
            assert forall|x: int| !(#[trigger] bs(n, nl, h, d, x) && prot(n, nl, h, d, x)) by {
                assert(bs(n, nl, h, d, x) == bs(*b, nl, h, d + 1, x));
                assert(prot(n, nl, h, d, x) == prot(*b, nl, h, d + 1, x));
            }
        },
        Node::If(t, e) => {
            lemma_bs_facts(*t, nl, (h - 1) as nat, d + 1);
            lemma_bs_facts(*e, nl, (h - 1) as nat, d + 1);
            lemma_bs_if(*t, *e, nl, h, d);
        },
        Node::Op(_) => {
            lemma_bs_leaf(n, nl, h, d);
        },
        Node::Br(_) => {
            lemma_bs_leaf(n, nl, h, d);
        },
        Node::BrIf(_) => {
            lemma_bs_leaf(n, nl, h, d);
        },
        Node::BrTable(_, _) => {
            lemma_bs_leaf(n, nl, h, d);
        },
        Node::Exit(_, _) => {
            lemma_bs_leaf(n, nl, h, d);
        },
    }
}

/// The nodes with no inner structure.
proof fn lemma_bs_leaf(n: Node, nl: nat, h: nat, d: nat)
    requires
        n is Br || n is BrIf || n is BrTable || n is Op || n is Exit,
    ensures
        bs_facts(n, nl, h, d),
{
    assert(bs(n, nl, h, d, 0));
    assert(bs(n, nl, h, d, csize(n, nl, h, d) as int));
    assert forall|x: int| #[trigger] bs(n, nl, h, d, x) implies 0 <= x <= csize(n, nl, h, d) as int
    by {}
    assert forall|x: int| !prot(n, nl, h, d, x) by {}
    assert forall|x: int| !(#[trigger] bs(n, nl, h, d, x) && prot(n, nl, h, d, x)) by {}
}

/// What [`lemma_bs_ubi`] says about a node.
pub open spec fn ubi_facts(n: Node, nl: nat, h: nat, offs: Seq<int>) -> bool {
    forall|pos: int, x: int|
        bs(n, nl, h, offs.len(), x) ==> #[trigger] ubi(utmpl(n, nl, h, offs), pos, pos + x)
}

/// A memory instruction.
proof fn lemma_ubif_mem(m: MemOp, nl: nat, h: nat, offs: Seq<int>)
    requires
        mem_region(m) < 16,
    ensures
        ubi_facts(Node::Mem(m), nl, h, offs),
{
    let n = Node::Mem(m);
    let d = offs.len();
    lemma_mem_csize(m, nl, h, d);
    lemma_utmpl_blen(n, nl, h, offs);
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![jmp_i(code_len(exit_seq(mem_exit_code(m))) as int)];
    let stub = exit_seq(mem_exit_code(m));
    let u1 = ones(pre) + seq![chk] + ones(tail);
    let u2 = seq![jm, stub];
    lemma_blen_ones(pre);
    lemma_blen_ones(tail);
    lemma_blen_cat(ones(pre), seq![chk]);
    lemma_blen_cat(ones(pre) + seq![chk], ones(tail));
    lemma_blen_one(chk);
    assert(blen(u1) == code_len(pre) + code_len(chk) + code_len(tail));
    lemma_code_len_one(jmp_i(code_len(stub) as int));
    crate::cflens::lemma_jmp_len(code_len(stub) as int);
    lemma_blen_two(jm, stub);
    assert(code_len(jm) == 5);
    assert(mem_units(m, nl, h) =~= u1 + u2);
    assert forall|pos: int, x: int| bs(n, nl, h, d, x) implies #[trigger] ubi(
        utmpl(n, nl, h, offs),
        pos,
        pos + x,
    ) by {
        if x == 0 {
            lemma_uflat_ones(pre);
            assert(ones(pre).len() > 0);
            assert(ub(ones(pre), pos, pos));
            assert(mem_units(m, nl, h) =~= ones(pre) + (seq![chk] + ones(tail) + u2));
            lemma_ub_cat(ones(pre), seq![chk] + ones(tail) + u2, pos, pos + x);
        } else if x == stub_off(m, nl, h) {
            assert(u2.len() == 2);
            assert(u2.skip(1)[0] == stub);
            assert(u2[0] == jm);
            assert(code_len(u2[0]) == 5);
            assert(ub(u2.skip(1), pos + blen(u1) + 5, pos + x));
            assert(ub(u2, pos + blen(u1), pos + x));
            lemma_ub_cat(u1, u2, pos, pos + x);
        } else {
            assert(x == csize(n, nl, h, d) as int);
            lemma_blen_cat(u1, u2);
        }
    }
}

/// `if`.
proof fn lemma_ubif_if(t: Node, e: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        ubi_facts(t, nl, (h - 1) as nat, seq![
            csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 5 + csize(
                e,
                nl,
                (h - 1) as nat,
                offs.len() + 1,
            ) as int,
        ] + shift(offs, cond_len(nl, h) as int)),
        ubi_facts(e, nl, (h - 1) as nat, seq![csize(e, nl, (h - 1) as nat, offs.len() + 1) as int]
            + shift(
            offs,
            cond_len(nl, h) as int + csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 5,
        )),
    ensures
        ubi_facts(Node::If(Box::new(t), Box::new(e)), nl, h, offs),
{
    let n = Node::If(Box::new(t), Box::new(e));
    let d = offs.len();
    let p = cond_len(nl, h) as int;
    let st = csize(t, nl, (h - 1) as nat, d + 1) as int;
    let se = csize(e, nl, (h - 1) as nat, d + 1) as int;
    let ot = seq![st + 5 + se] + shift(offs, p);
    let oe = seq![se] + shift(offs, p + st + 5);
    assert(ot.len() == d + 1 && oe.len() == d + 1);
    let cp = cond_pre(nl, h, 4, st + 5);
    let ut = utmpl(t, nl, (h - 1) as nat, ot);
    let ue = utmpl(e, nl, (h - 1) as nat, oe);
    let jmu = seq![seq![jmp_i(se)]];
    lemma_cond_pre_len(nl, h, 4, st + 5);
    lemma_blen_ones(cp);
    lemma_utmpl_blen(t, nl, (h - 1) as nat, ot);
    lemma_utmpl_blen(e, nl, (h - 1) as nat, oe);
    crate::cflens::lemma_jmp_len(se);
    lemma_code_len_one(jmp_i(se));
    lemma_blen_one(seq![jmp_i(se)]);
    let a1 = ones(cp);
    let a2 = a1 + ut;
    let a3 = a2 + jmu;
    lemma_blen_cat(a1, ut);
    lemma_blen_cat(a2, jmu);
    lemma_blen_cat(a3, ue);
    assert(utmpl(n, nl, h, offs) =~= a3 + ue);
    assert forall|pos: int, x: int| bs(n, nl, h, d, x) implies #[trigger] ubi(
        utmpl(n, nl, h, offs),
        pos,
        pos + x,
    ) by {
        if x == 0 {
            lemma_uflat_ones(cp);
            assert(ub(a1, pos, pos));
            assert(utmpl(n, nl, h, offs) =~= a1 + (ut + jmu + ue));
            lemma_ubi_cat(a1, ut + jmu + ue, pos, pos + x);
        } else if bs(t, nl, (h - 1) as nat, d + 1, x - p) {
            assert(ubi(ut, pos + p, pos + p + (x - p)));
            lemma_ubi_cat(a1, ut, pos, pos + x);
            lemma_ubi_cat(a2, jmu, pos, pos + x);
            lemma_ubi_cat(a3, ue, pos, pos + x);
        } else {
            assert(bs(e, nl, (h - 1) as nat, d + 1, x - (p + st + 5)));
            assert(ubi(ue, pos + (p + st + 5), pos + (p + st + 5) + (x - (p + st + 5))));
            lemma_ubi_cat(a3, ue, pos, pos + x);
        }
    }
}

/// `then`.
proof fn lemma_ubif_then(a: Node, b: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(Node::Then(Box::new(a), Box::new(b)), nl, h, offs.len()) is Some,
        ubi_facts(a, nl, h, offs),
        cf_flow(a, nl, h, offs.len()) is Some,
        match cf_flow(a, nl, h, offs.len()) {
            Some(Flow::Falls(h1)) => ubi_facts(
                b,
                nl,
                h1,
                shift(offs, csize(a, nl, h, offs.len()) as int),
            ),
            _ => true,
        },
    ensures
        ubi_facts(Node::Then(Box::new(a), Box::new(b)), nl, h, offs),
{
    let n = Node::Then(Box::new(a), Box::new(b));
    let d = offs.len();
    let sa = csize(a, nl, h, d);
    let ob = shift(offs, sa as int);
    let h1 = flow_h(a, nl, h, d);
    lemma_utmpl_blen(a, nl, h, offs);
    assert forall|pos: int, x: int| bs(n, nl, h, d, x) implies #[trigger] ubi(
        utmpl(n, nl, h, offs),
        pos,
        pos + x,
    ) by {
        if bs(a, nl, h, d, x) {
            assert(ubi(utmpl(a, nl, h, offs), pos, pos + x));
            lemma_ubi_cat(utmpl(a, nl, h, offs), utmpl(b, nl, h1, ob), pos, pos + x);
        } else {
            assert(bs(b, nl, h1, d, x - sa as int));
            match cf_flow(a, nl, h, d) {
                Some(Flow::Falls(_)) => {
                    assert(ob.len() == d);
                    assert(ubi(
                        utmpl(b, nl, h1, ob),
                        pos + sa as int,
                        pos + sa as int + (x - sa as int),
                    ));
                    lemma_ubi_cat(utmpl(a, nl, h, offs), utmpl(b, nl, h1, ob), pos, pos + x);
                },
                Some(Flow::Dead) => {
                    assert(b == Node::Op(Op::Nop));
                    lemma_nop_size(nl, h, d);
                    assert(utmpl(b, nl, h1, ob) =~= Seq::<Seq<x64::Instr>>::empty());
                    assert(x == sa as int);
                    lemma_blen_cat(utmpl(a, nl, h, offs), utmpl(b, nl, h1, ob));
                },
                None => {},
            }
        }
    }
}

/// A node whose units are one instruction each, or an exit sequence.
proof fn lemma_ubif_leaf(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
        n is Br || n is BrIf || n is BrTable || n is Op || n is Exit,
    ensures
        ubi_facts(n, nl, h, offs),
{
    let d = offs.len();
    lemma_utmpl_blen(n, nl, h, offs);
    let us = utmpl(n, nl, h, offs);
    assert forall|pos: int, x: int| bs(n, nl, h, d, x) implies #[trigger] ubi(us, pos, pos + x) by {
        if x == 0 {
            match n {
                Node::Exit(c, _) => {
                    assert(us.len() == 1);
                    assert(ub(us, pos, pos));
                },
                _ => {
                    let c = match n {
                        Node::Op(o) => tmpl(o, nl, h),
                        _ => ctmpl(n, nl, h, offs),
                    };
                    assert(us == ones(c));
                    if c.len() > 0 {
                        assert(us.len() > 0);
                        assert(ub(us, pos, pos));
                    } else {
                        assert(us.len() == 0);
                        lemma_blen_ones(c);
                    }
                },
            }
        } else {
            assert(x == csize(n, nl, h, d) as int);
        }
    }
}

/// `block`.
proof fn lemma_ubif_block(b: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        ubi_facts(b, nl, h, seq![csize(b, nl, h, offs.len() + 1) as int] + offs),
    ensures
        ubi_facts(Node::Block(Box::new(b)), nl, h, offs),
{
    let n = Node::Block(Box::new(b));
    let ob = seq![csize(b, nl, h, offs.len() + 1) as int] + offs;
    assert(ob.len() == offs.len() + 1);
    assert forall|pos: int, x: int| bs(n, nl, h, offs.len(), x) implies #[trigger] ubi(
        utmpl(n, nl, h, offs),
        pos,
        pos + x,
    ) by {
        assert(bs(b, nl, h, offs.len() + 1, x));
        assert(ubi(utmpl(b, nl, h, ob), pos, pos + x));
    }
}

/// `loop`.
proof fn lemma_ubif_loop(b: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        ubi_facts(b, nl, h, seq![0int] + offs),
    ensures
        ubi_facts(Node::Loop(Box::new(b)), nl, h, offs),
{
    let n = Node::Loop(Box::new(b));
    let ob = seq![0int] + offs;
    assert(ob.len() == offs.len() + 1);
    assert forall|pos: int, x: int| bs(n, nl, h, offs.len(), x) implies #[trigger] ubi(
        utmpl(n, nl, h, offs),
        pos,
        pos + x,
    ) by {
        assert(bs(b, nl, h, offs.len() + 1, x));
        assert(ubi(utmpl(b, nl, h, ob), pos, pos + x));
    }
}

/// **Every position a jump may land on is a unit start or the end of the
/// units.**
pub proof fn lemma_bs_ubi(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
    ensures
        ubi_facts(n, nl, h, offs),
    decreases n,
{
    let d = offs.len();
    match n {
        Node::Mem(m) => {
            lemma_ubif_mem(m, nl, h, offs);
        },
        Node::Then(a, b) => {
            let sa = csize(*a, nl, h, d);
            let ob = shift(offs, sa as int);
            lemma_bs_ubi(*a, nl, h, offs);
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    assert(ob.len() == d);
                    lemma_bs_ubi(*b, nl, h1, ob);
                },
                _ => {},
            }
            lemma_ubif_then(*a, *b, nl, h, offs);
        },
        Node::Block(b) => {
            let ob = seq![csize(*b, nl, h, d + 1) as int] + offs;
            assert(ob.len() == d + 1);
            lemma_bs_ubi(*b, nl, h, ob);
            lemma_ubif_block(*b, nl, h, offs);
        },
        Node::Loop(b) => {
            let ob = seq![0int] + offs;
            assert(ob.len() == d + 1);
            lemma_bs_ubi(*b, nl, h, ob);
            lemma_ubif_loop(*b, nl, h, offs);
        },
        Node::If(t, e) => {
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 5 + se] + shift(offs, p);
            let oe = seq![se] + shift(offs, p + st + 5);
            assert(ot.len() == d + 1 && oe.len() == d + 1);
            lemma_bs_ubi(*t, nl, (h - 1) as nat, ot);
            lemma_bs_ubi(*e, nl, (h - 1) as nat, oe);
            lemma_ubif_if(*t, *e, nl, h, offs);
        },
        _ => {
            lemma_ubif_leaf(n, nl, h, offs);
        },
    }
}

} // verus!
