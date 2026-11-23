//! Where the branches of the A64 templates land (jit.md item J.9, "every
//! emitted blob is accepted"): every branch target of a node's code is one of
//! the labels it was given or one of [`bs`]. The counterpart of
//! [`crate::cfjt`]; a branch is relative to its own address.
//!
//! `jt c x` says that some branch of `c` lands on byte `x` of `c`, computed
//! as the validator does ([`clazel_codecheck::a64::spec::jump_targets`]: the
//! address of the branch plus its displacement).

#[cfg(verus_only)]
use super::cfaccept::*;
#[cfg(verus_only)]
use super::cfbs::*;
#[cfg(verus_only)]
use super::cfcompose::lemma_shift_index;
#[cfg(verus_only)]
use super::cffit::{labels_fit, lemma_fit_cons, lemma_fit_mono, lemma_fit_shift};
#[cfg(verus_only)]
use super::cflens::*;
#[cfg(verus_only)]
use super::cfsimple::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::cfunits::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Some branch of `c` lands on byte `x` of `c`.
pub open spec fn jt(c: Seq<isa::Instr>, x: int) -> bool {
    exists|j: int|
        0 <= j < c.len() && #[trigger] clazel_codecheck::a64::spec::jump_rel(c[j]) is Some && x
            == clazel_codecheck::a64::spec::start_of(c, j)
            + clazel_codecheck::a64::spec::jump_rel(c[j])->Some_0
}

/// `x` is one of the labels.
pub open spec fn inoffs(offs: Seq<int>, x: int) -> bool {
    exists|l: int| 0 <= l < offs.len() && #[trigger] offs[l] == x
}

// ----------------------------------------------------------------------------
// Positions in a list of instructions
// ----------------------------------------------------------------------------

/// A branch of a concatenation is a branch of a part.
pub proof fn lemma_jt_cat(a: Seq<isa::Instr>, b: Seq<isa::Instr>, x: int)
    requires
        jt(a + b, x),
    ensures
        jt(a, x) || jt(b, x - code_len(a)),
{
    let j = choose|j: int|
        0 <= j < (a + b).len() && #[trigger] clazel_codecheck::a64::spec::jump_rel((a + b)[j]) is Some
            && x == clazel_codecheck::a64::spec::start_of(a + b, j)
            + clazel_codecheck::a64::spec::jump_rel((a + b)[j])->Some_0;
    if j < a.len() {
        assert((a + b)[j] == a[j]);
        assert(jt(a, x));
    } else {
        let k = j - a.len();
        assert((a + b)[j] == b[k]);
        assert(clazel_codecheck::a64::spec::jump_rel(b[k]) is Some);
        assert(jt(b, x - code_len(a)));
    }
}

/// Code with no branch has no branch target.
pub proof fn lemma_jt_none(c: Seq<isa::Instr>, x: int)
    requires
        forall|k: int| 0 <= k < c.len() ==> nojump(#[trigger] c[k]),
    ensures
        !jt(c, x),
{
}

/// The only branch is the last instruction.
pub proof fn lemma_jt_last(c: Seq<isa::Instr>, x: int)
    requires
        c.len() > 0,
        forall|k: int| 0 <= k < c.len() - 1 ==> nojump(#[trigger] c[k]),
        clazel_codecheck::a64::spec::jump_rel(c[c.len() - 1]) is Some,
        jt(c, x),
    ensures
        x == code_len(c) - 4 + clazel_codecheck::a64::spec::jump_rel(c[c.len() - 1])->Some_0,
{
    let j = choose|j: int|
        0 <= j < c.len() && #[trigger] clazel_codecheck::a64::spec::jump_rel(c[j]) is Some && x
            == clazel_codecheck::a64::spec::start_of(c, j)
            + clazel_codecheck::a64::spec::jump_rel(c[j])->Some_0;
    assert(j == c.len() - 1);
}

/// The displacement of a `b`, `b.cond` or `cbz`/`cbnz` made with a byte
/// displacement that is a multiple of 4 is that displacement.
pub proof fn lemma_branch_rel(rel: int, cc: u8, iszero: bool)
    requires
        rel % 4 == 0,
        -0x4000_0000 <= rel <= 0x4000_0000,
    ensures
        clazel_codecheck::a64::spec::jump_rel(b_i(rel)) == Some(rel),
        clazel_codecheck::a64::spec::jump_rel(bcond_i(cc, rel)) == Some(rel),
        clazel_codecheck::a64::spec::jump_rel(cb_i(iszero, rel)) == Some(rel),
{
    assert(rel / 4 * 4 == rel);
    assert(((rel / 4) as i32) as int == rel / 4);
}

// ----------------------------------------------------------------------------
// The leaves
// ----------------------------------------------------------------------------

/// The statement of [`lemma_jt_bs`] for a node.
pub open spec fn jt_facts(n: Node, nl: nat, h: nat, offs: Seq<int>) -> bool {
    forall|x: int|
        jt(ctmpl(n, nl, h, offs), x) ==> #[trigger] inoffs(offs, x) || bs(
            n,
            nl,
            h,
            offs.len(),
            x,
        )
}

/// `br l`: the branch lands on the label.
proof fn lemma_jtf_br(l: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        l < offs.len(),
        labels_fit(offs, 4),
    ensures
        jt_facts(Node::Br(l), nl, h, offs),
{
    let rel = offs[l as int];
    assert(offs[l as int] % 4 == 0);
    lemma_branch_rel(rel, 0, false);
    assert forall|x: int| jt(ctmpl(Node::Br(l), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::Br(l), nl, h, offs.len(), x) by {
        let c = ctmpl(Node::Br(l), nl, h, offs);
        assert(c == seq![b_i(rel)]);
        lemma_jt_last(c, x);
        assert(offs[l as int] == x);
    }
}

/// `br_if l`.
proof fn lemma_jtf_brif(l: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        l < offs.len(),
        labels_fit(offs, 8),
    ensures
        jt_facts(Node::BrIf(l), nl, h, offs),
{
    let rel = offs[l as int] - 4;
    assert(offs[l as int] % 4 == 0);
    lemma_branch_rel(rel, 0, false);
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    assert forall|x: int| jt(ctmpl(Node::BrIf(l), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::BrIf(l), nl, h, offs.len(), x) by {
        let c = ctmpl(Node::BrIf(l), nl, h, offs);
        assert(c == cond_pre(nl, h, false, rel));
        assert(c.len() == 2);
        assert(forall|k: int| 0 <= k < 1 ==> nojump(#[trigger] c[k])) by {
            assert forall|k: int| 0 <= k < 1 implies nojump(c[k]) by {
                assert(k == 0);
            }
        }
        lemma_jt_last(c, x);
        assert(offs[l as int] == x);
    }
}

/// `exit`: no branch.
proof fn lemma_jtf_exit(c: u32, k: usize, nl: nat, h: nat, offs: Seq<int>)
    ensures
        jt_facts(Node::Exit(c, k), nl, h, offs),
{
    assert forall|x: int| jt(ctmpl(Node::Exit(c, k), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::Exit(c, k), nl, h, offs.len(), x) by {
        let e = exit_seq(c as u16);
        assert(forall|j: int| 0 <= j < e.len() ==> nojump(#[trigger] e[j])) by {
            assert forall|j: int| 0 <= j < e.len() implies nojump(e[j]) by {
                assert(j == 0 || j == 1 || j == 2);
            }
        }
        lemma_jt_none(e, x);
    }
}

/// A straight-line instruction: no branch.
proof fn lemma_jtf_op(o: Op, nl: nat, h: nat, offs: Seq<int>)
    requires
        op_ok(o, nl, h),
    ensures
        jt_facts(Node::Op(o), nl, h, offs),
{
    lemma_tmpl_straight(o, nl, h);
    assert forall|x: int| jt(ctmpl(Node::Op(o), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::Op(o), nl, h, offs.len(), x) by {
        let c = tmpl(o, nl, h);
        assert(forall|k: int| 0 <= k < c.len() ==> nojump(#[trigger] c[k])) by {
            assert forall|k: int| 0 <= k < c.len() implies nojump(c[k]) by {
                assert(straight(c[k]));
            }
        }
        lemma_jt_none(c, x);
    }
}

// ----------------------------------------------------------------------------
// br_table
// ----------------------------------------------------------------------------

/// The chain from entry `i` on: a branch lands on a target label.
proof fn lemma_jt_entries(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat, x: int)
    requires
        i <= ls.len(),
        p0 == 4,
        forall|k: int| 0 <= k < ls.len() ==> #[trigger] ls[k] < offs.len(),
        forall|l: int|
            0 <= l < offs.len() ==> #[trigger] offs[l] % 4 == 0 && -0x10_0000 + 8 + 12 * ls.len()
                <= offs[l] && offs[l] <= 0xF_FFF0,
        jt(brt_entries(ls, offs, p0, i), x),
    ensures
        exists|k: int| i <= k < ls.len() && x + p0 + i * 12 == #[trigger] offs[ls[k] as int],
    decreases ls.len() - i,
{
    assert(brt_e() == 12);
    if i >= ls.len() {
        assert(brt_entries(ls, offs, p0, i) =~= Seq::<isa::Instr>::empty());
        assert(false);
    } else {
        let rel = brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8);
        let e = brt_entry(i, rel);
        let rest = brt_entries(ls, offs, p0, i + 1);
        assert(brt_entries(ls, offs, p0, i) == e + rest);
        lemma_jt_cat(e, rest, x);
        if jt(e, x) {
            assert(ls[i as int] < offs.len());
            let t = ls[i as int] as int;
            assert(rel == offs[t] - (p0 + i * 12 + 8));
            assert((i + 1) * 12 <= ls.len() * 12) by (nonlinear_arith)
                requires
                    i < ls.len(),
            ;
            assert(rel % 4 == 0) by {
                assert(offs[t] % 4 == 0);
                assert((p0 + i * 12 + 8) % 4 == 0) by (nonlinear_arith)
                    requires
                        p0 == 4,
                ;
            }
            lemma_branch_rel(rel, 0, false);
            assert(e.len() == 3);
            assert(forall|k: int| 0 <= k < 2 ==> nojump(#[trigger] e[k])) by {
                assert forall|k: int| 0 <= k < 2 implies nojump(e[k]) by {
                    assert(k == 0 || k == 1);
                }
            }
            assert(clazel_codecheck::a64::spec::jump_rel(e[2]) == Some(rel));
            lemma_jt_last(e, x);
            assert(x + p0 + i * 12 == offs[t]);
            assert(offs[ls[i as int] as int] == x + p0 + i * 12);
            assert(i <= i && i < ls.len());
        } else {
            assert(jt(rest, x - 12));
            lemma_jt_entries(ls, offs, p0, i + 1, x - 12);
            let k = choose|k: int|
                i + 1 <= k < ls.len() && (x - 12) + p0 + (i + 1) * 12 == #[trigger] offs[ls[k] as int];
            assert(x + p0 + i * 12 == offs[ls[k] as int]);
        }
    }
}

/// `br_table`.
proof fn lemma_jtf_brt(ls: Vec<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        d < offs.len(),
        forall|k: int| 0 <= k < ls@.len() ==> #[trigger] ls@[k] < offs.len(),
        labels_fit(offs, 8 + 12 * ls@.len()),
    ensures
        jt_facts(Node::BrTable(ls, d), nl, h, offs),
{
    let p0 = brt_p0(nl, h);
    assert(p0 == 4);
    let n = ls@.len();
    let a = seq![load_slot(x0(), (nl + h - 1) as nat)];
    let ch = brt_entries(ls@, offs, p0, 0);
    let jm = seq![b_i(brt_rel(offs, d, p0 + n * brt_e()))];
    let whole = brt_code(ls@, d, nl, h, offs);
    assert(brt_e() == 12);
    assert(whole =~= a + (ch + jm));
    assert(code_len(ch) == 12 * n) by {
        lemma_entries_code_len(ls@, offs, p0, 0);
    }
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
    assert forall|x: int| jt(ctmpl(Node::BrTable(ls, d), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::BrTable(ls, d), nl, h, offs.len(), x) by {
        assert(ctmpl(Node::BrTable(ls, d), nl, h, offs) == whole);
        lemma_jt_cat(a, ch + jm, x);
        assert(!jt(a, x)) by {
            assert(nojump(a[0]));
            lemma_jt_none(a, x);
        }
        lemma_jt_cat(ch, jm, x - code_len(a));
        assert(code_len(a) == 4);
        if jt(ch, x - code_len(a)) {
            assert forall|l: int|
                0 <= l < offs.len() implies #[trigger] offs[l] % 4 == 0 && -0x10_0000 + 8 + 12 * n
                <= offs[l] && offs[l] <= 0xF_FFF0 by {}
            lemma_jt_entries(ls@, offs, p0, 0, x - code_len(a));
            let k = choose|k: int|
                0 <= k < n && (x - code_len(a)) + p0 + 0 * 12 == #[trigger] offs[ls@[k] as int];
            assert(offs[ls@[k] as int] == x);
            assert(inoffs(offs, x));
        } else {
            let z = x - code_len(a) - code_len(ch);
            assert(jt(jm, z));
            let rel = brt_rel(offs, d, p0 + n * brt_e());
            assert(rel == offs[d as int] - (4 + 12 * n));
            assert(rel % 4 == 0) by {
                assert(offs[d as int] % 4 == 0);
            }
            lemma_branch_rel(rel, 0, false);
            assert(clazel_codecheck::a64::spec::jump_rel(jm[0]) == Some(rel));
            lemma_jt_last(jm, z);
            assert(x == offs[d as int]);
            assert(inoffs(offs, x));
        }
    }
}

/// The chain's entries are 12 bytes each.
proof fn lemma_entries_code_len(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat)
    ensures
        code_len(brt_entries(ls, offs, p0, i)) == if i >= ls.len() {
            0nat
        } else {
            (12 * (ls.len() - i)) as nat
        },
    decreases ls.len() - i,
{
    if i < ls.len() {
        let e = brt_entry(i, brt_rel(offs, ls[i as int], p0 + i * brt_e() + 8));
        lemma_entries_code_len(ls, offs, p0, i + 1);
        assert(brt_entries(ls, offs, p0, i) == e + brt_entries(ls, offs, p0, i + 1));
    } else {
        assert(brt_entries(ls, offs, p0, i) =~= Seq::<isa::Instr>::empty());
    }
}

// ----------------------------------------------------------------------------
// Memory instructions
// ----------------------------------------------------------------------------

/// The check's two exits: the validator's own sequence, whose `b.cond`s are the
/// third and fifth instructions.
proof fn lemma_jt_chk(c: clazel_codecheck::a64::spec::Chk, x: int)
    requires
        jt(clazel_codecheck::a64::spec::check_seq(c), x),
    ensures
        x == 8 + 4 * (c.r1 as int) || x == 16 + 4 * (c.r2 as int),
{
    let cs = clazel_codecheck::a64::spec::check_seq(c);
    assert(cs[0] == clazel_codecheck::a64::spec::check_instr(0, c));
    assert(cs[1] == clazel_codecheck::a64::spec::check_instr(1, c));
    assert(cs[2] == clazel_codecheck::a64::spec::check_instr(2, c));
    assert(cs[3] == clazel_codecheck::a64::spec::check_instr(3, c));
    assert(cs[4] == clazel_codecheck::a64::spec::check_instr(4, c));
    assert(cs[5] == clazel_codecheck::a64::spec::check_instr(5, c));
    assert(cs[6] == clazel_codecheck::a64::spec::check_instr(6, c));
    let j = choose|j: int|
        0 <= j < cs.len() && #[trigger] clazel_codecheck::a64::spec::jump_rel(cs[j]) is Some && x
            == clazel_codecheck::a64::spec::start_of(cs, j)
            + clazel_codecheck::a64::spec::jump_rel(cs[j])->Some_0;
    assert(j == 2 || j == 4);
}

/// A memory instruction: its branches land on the stub, or at its end.
proof fn lemma_jtf_mem(m: MemOp, nl: nat, h: nat, offs: Seq<int>)
    ensures
        jt_facts(Node::Mem(m), nl, h, offs),
{
    lemma_mem_csize(m, nl, h, offs.len());
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![b_i(code_len(exit_seq(mem_exit_code(m))) as int + 4)];
    let stub = exit_seq(mem_exit_code(m));
    let c0 = mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h));
    assert(code_len(stub) == 12);
    lemma_branch_rel(16, 0, false);
    assert forall|x: int| jt(ctmpl(Node::Mem(m), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::Mem(m), nl, h, offs.len(), x) by {
        let a1 = pre + chk;
        let a2 = a1 + tail;
        let a3 = a2 + jm;
        assert(ctmpl(Node::Mem(m), nl, h, offs) == mem_code(m, nl, h));
        assert(mem_code(m, nl, h) == a3 + stub);
        lemma_jt_cat(a3, stub, x);
        assert(!jt(stub, x - code_len(a3))) by {
            assert(forall|j: int| 0 <= j < stub.len() ==> nojump(#[trigger] stub[j])) by {
                assert forall|j: int| 0 <= j < stub.len() implies nojump(stub[j]) by {
                    assert(j == 0 || j == 1 || j == 2);
                }
            }
            lemma_jt_none(stub, x - code_len(a3));
        }
        lemma_jt_cat(a2, jm, x);
        if jt(jm, x - code_len(a2)) {
            lemma_jt_last(jm, x - code_len(a2));
            assert(clazel_codecheck::a64::spec::jump_rel(jm[0]) == Some(16int));
            assert(x == csize(Node::Mem(m), nl, h, offs.len()));
            assert(bs(Node::Mem(m), nl, h, offs.len(), x));
        } else {
            lemma_jt_cat(a1, tail, x);
            assert(jt(a1, x)) by {
                if jt(tail, x - code_len(a1)) {
                    assert(forall|j: int| 0 <= j < tail.len() ==> nojump(#[trigger] tail[j])) by {
                        assert forall|j: int| 0 <= j < tail.len() implies nojump(tail[j]) by {
                            match m {
                                MemOp::BoundsCheck { .. } => {},
                                MemOp::Load { .. } => {
                                    assert(j == 0 || j == 1);
                                },
                                MemOp::Store { .. } => {
                                    assert(j == 0);
                                },
                            }
                        }
                    }
                    lemma_jt_none(tail, x - code_len(a1));
                }
            }
            lemma_jt_cat(pre, chk, x);
            assert(jt(chk, x - code_len(pre))) by {
                if jt(pre, x) {
                    assert(forall|j: int| 0 <= j < pre.len() ==> nojump(#[trigger] pre[j])) by {
                        assert forall|j: int| 0 <= j < pre.len() implies nojump(pre[j]) by {
                            match m {
                                MemOp::BoundsCheck { .. } => {
                                    assert(j == 0);
                                },
                                MemOp::Load { .. } => {
                                    assert(j == 0 || j == 1);
                                },
                                MemOp::Store { .. } => {
                                    assert(j == 0 || j == 1 || j == 2);
                                },
                            }
                        }
                    }
                    lemma_jt_none(pre, x);
                }
            }
            assert(chk == clazel_codecheck::a64::spec::check_seq(c0));
            lemma_jt_chk(c0, x - code_len(pre));
            assert(c0.r1 == mem_r1(m, nl, h) as i32);
            assert(c0.r2 == mem_r2(m, nl, h) as i32);
            assert(x == stub_off(m, nl, h));
            assert(bs(Node::Mem(m), nl, h, offs.len(), x));
        }
    }
}

// ----------------------------------------------------------------------------
// Composition
// ----------------------------------------------------------------------------

/// `then`.
proof fn lemma_jtf_then(a: Node, b: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(Node::Then(Box::new(a), Box::new(b)), nl, h, offs.len()) is Some,
        cf_flow(a, nl, h, offs.len()) is Some,
        jt_facts(a, nl, h, offs),
        match cf_flow(a, nl, h, offs.len()) {
            Some(Flow::Falls(h1)) => jt_facts(
                b,
                nl,
                flow_h(a, nl, h, offs.len()),
                shift(offs, csize(a, nl, h, offs.len()) as int),
            ),
            _ => true,
        },
    ensures
        jt_facts(Node::Then(Box::new(a), Box::new(b)), nl, h, offs),
{
    let n = Node::Then(Box::new(a), Box::new(b));
    let d = offs.len();
    let sa = csize(a, nl, h, d) as int;
    let h1 = flow_h(a, nl, h, d);
    let ob = shift(offs, sa);
    lemma_ctmpl_len(a, nl, h, offs);
    assert forall|x: int| jt(ctmpl(n, nl, h, offs), x) implies #[trigger] inoffs(offs, x) || bs(
        n,
        nl,
        h,
        d,
        x,
    ) by {
        lemma_jt_cat(ctmpl(a, nl, h, offs), ctmpl(b, nl, h1, ob), x);
        if jt(ctmpl(a, nl, h, offs), x) {
            if inoffs(offs, x) {
            } else {
                assert(bs(a, nl, h, d, x));
            }
        } else {
            let y = x - sa;
            assert(jt(ctmpl(b, nl, h1, ob), y));
            match cf_flow(a, nl, h, d) {
                Some(Flow::Falls(_)) => {
                    assert(ob.len() == d);
                    if inoffs(ob, y) {
                        let l = choose|l: int| 0 <= l < ob.len() && #[trigger] ob[l] == y;
                        lemma_shift_index(offs, sa, l);
                        assert(offs[l] == x);
                        assert(inoffs(offs, x));
                    } else {
                        assert(bs(b, nl, h1, d, y));
                    }
                },
                Some(Flow::Dead) => {
                    assert(b == Node::Op(Op::Nop));
                    assert(ctmpl(b, nl, h1, ob) =~= Seq::<isa::Instr>::empty());
                    assert(false);
                },
                None => {},
            }
        }
    }
}

/// `block`.
proof fn lemma_jtf_block(b: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(Node::Block(Box::new(b)), nl, h, offs.len()) is Some,
        jt_facts(b, nl, h, seq![csize(b, nl, h, offs.len() + 1) as int] + offs),
    ensures
        jt_facts(Node::Block(Box::new(b)), nl, h, offs),
{
    let n = Node::Block(Box::new(b));
    let d = offs.len();
    let sb = csize(b, nl, h, d + 1) as int;
    let ob = seq![sb] + offs;
    assert(ob.len() == d + 1);
    lemma_bs_facts(b, nl, h, d + 1);
    assert forall|x: int| jt(ctmpl(n, nl, h, offs), x) implies #[trigger] inoffs(offs, x) || bs(
        n,
        nl,
        h,
        d,
        x,
    ) by {
        assert(jt(ctmpl(b, nl, h, ob), x));
        if inoffs(ob, x) {
            let l = choose|l: int| 0 <= l < ob.len() && #[trigger] ob[l] == x;
            if l == 0 {
                assert(x == sb);
                assert(bs(b, nl, h, d + 1, sb));
            } else {
                assert(ob[l] == offs[l - 1]);
                assert(inoffs(offs, x));
            }
        } else {
            assert(bs(b, nl, h, d + 1, x));
        }
    }
}

/// `loop`.
proof fn lemma_jtf_loop(b: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(Node::Loop(Box::new(b)), nl, h, offs.len()) is Some,
        jt_facts(b, nl, h, seq![0int] + offs),
    ensures
        jt_facts(Node::Loop(Box::new(b)), nl, h, offs),
{
    let n = Node::Loop(Box::new(b));
    let d = offs.len();
    let ob = seq![0int] + offs;
    assert(ob.len() == d + 1);
    lemma_bs_facts(b, nl, h, d + 1);
    assert forall|x: int| jt(ctmpl(n, nl, h, offs), x) implies #[trigger] inoffs(offs, x) || bs(
        n,
        nl,
        h,
        d,
        x,
    ) by {
        assert(jt(ctmpl(b, nl, h, ob), x));
        if inoffs(ob, x) {
            let l = choose|l: int| 0 <= l < ob.len() && #[trigger] ob[l] == x;
            if l == 0 {
                assert(x == 0);
                assert(bs(b, nl, h, d + 1, 0));
            } else {
                assert(ob[l] == offs[l - 1]);
                assert(inoffs(offs, x));
            }
        } else {
            assert(bs(b, nl, h, d + 1, x));
        }
    }
}

/// `if`.
#[verifier::rlimit(1500)]
proof fn lemma_jtf_if(t: Node, e: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(Node::If(Box::new(t), Box::new(e)), nl, h, offs.len()) is Some,
        csize(Node::If(Box::new(t), Box::new(e)), nl, h, offs.len()) <= max_size(),
        jt_facts(t, nl, (h - 1) as nat, seq![
            csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 4 + csize(
                e,
                nl,
                (h - 1) as nat,
                offs.len() + 1,
            ) as int,
        ] + shift(offs, 8)),
        jt_facts(e, nl, (h - 1) as nat, seq![csize(e, nl, (h - 1) as nat, offs.len() + 1) as int]
            + shift(offs, 12 + csize(t, nl, (h - 1) as nat, offs.len() + 1) as int)),
    ensures
        jt_facts(Node::If(Box::new(t), Box::new(e)), nl, h, offs),
{
    let n = Node::If(Box::new(t), Box::new(e));
    let d = offs.len();
    let h0 = (h - 1) as nat;
    let st = csize(t, nl, h0, d + 1) as int;
    let se = csize(e, nl, h0, d + 1) as int;
    let ot = seq![st + 4 + se] + shift(offs, 8);
    let oe = seq![se] + shift(offs, 12 + st);
    assert(ot.len() == d + 1 && oe.len() == d + 1);
    lemma_csize_if(t, e, nl, h, d);
    lemma_bs_facts(t, nl, h0, d + 1);
    lemma_bs_facts(e, nl, h0, d + 1);
    let cp = cond_pre(nl, h, true, st + 8);
    let ct = ctmpl(t, nl, h0, ot);
    let ce = ctmpl(e, nl, h0, oe);
    let jm = seq![b_i(se + 4)];
    lemma_ctmpl_len(t, nl, h0, ot);
    lemma_ctmpl_len(e, nl, h0, oe);
    assert(st % 4 == 0 && se % 4 == 0) by {
        super::cfproofs::lemma_csize_mod4(t, nl, h0, d + 1);
        super::cfproofs::lemma_csize_mod4(e, nl, h0, d + 1);
    }
    lemma_branch_rel(st + 8, 0, true);
    lemma_branch_rel(se + 4, 0, true);
    assert(code_len(cp) == 8);
    assert forall|x: int| jt(ctmpl(n, nl, h, offs), x) implies #[trigger] inoffs(offs, x) || bs(
        n,
        nl,
        h,
        d,
        x,
    ) by {
        assert(ctmpl(n, nl, h, offs) == cp + ct + jm + ce);
        lemma_jt_cat(cp + ct + jm, ce, x);
        assert(code_len(cp + ct) == 8 + st);
        assert(code_len(cp + ct + jm) == 12 + st);
        if jt(cp + ct + jm, x) {
            lemma_jt_cat(cp + ct, jm, x);
            if jt(cp + ct, x) {
                lemma_jt_cat(cp, ct, x);
                if jt(cp, x) {
                    assert(cp.len() == 2);
                    assert(forall|k: int| 0 <= k < 1 ==> nojump(#[trigger] cp[k])) by {
                        assert forall|k: int| 0 <= k < 1 implies nojump(cp[k]) by {
                            assert(k == 0);
                        }
                    }
                    lemma_jt_last(cp, x);
                    assert(x == 4 + st + 8);
                    assert(bs(e, nl, h0, d + 1, 0));
                    assert(x - (12 + st) == 0);
                } else {
                    let y = x - 8;
                    assert(jt(ct, y));
                    if inoffs(ot, y) {
                        let l = choose|l: int| 0 <= l < ot.len() && #[trigger] ot[l] == y;
                        if l == 0 {
                            assert(x == 12 + st + se);
                            assert(bs(e, nl, h0, d + 1, se));
                        } else {
                            assert(ot[l] == shift(offs, 8)[l - 1]);
                            lemma_shift_index(offs, 8, l - 1);
                            assert(offs[l - 1] == x);
                            assert(inoffs(offs, x));
                        }
                    } else {
                        assert(bs(t, nl, h0, d + 1, y));
                    }
                }
            } else {
                lemma_jt_last(jm, x - code_len(cp + ct));
                assert(clazel_codecheck::a64::spec::jump_rel(jm[0]) == Some(se + 4));
                assert(x == 8 + st + se + 4);
                assert(bs(e, nl, h0, d + 1, se));
            }
        } else {
            let y = x - (12 + st);
            assert(jt(ce, y));
            if inoffs(oe, y) {
                let l = choose|l: int| 0 <= l < oe.len() && #[trigger] oe[l] == y;
                if l == 0 {
                    assert(bs(e, nl, h0, d + 1, se));
                } else {
                    assert(oe[l] == shift(offs, 12 + st)[l - 1]);
                    lemma_shift_index(offs, 12 + st, l - 1);
                    assert(offs[l - 1] == x);
                    assert(inoffs(offs, x));
                }
            } else {
                assert(bs(e, nl, h0, d + 1, y));
            }
        }
    }
}

/// **Every branch of a node's code lands on a label it was given, or on a
/// position of [`bs`].**
#[verifier::rlimit(1500)]
pub proof fn lemma_jt_bs(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
        csize(n, nl, h, offs.len()) <= max_size(),
        labels_fit(offs, csize(n, nl, h, offs.len())),
    ensures
        jt_facts(n, nl, h, offs),
    decreases n,
{
    let d = offs.len();
    let size = csize(n, nl, h, d);
    match n {
        Node::Op(o) => {
            lemma_jtf_op(o, nl, h, offs);
        },
        Node::Mem(m) => {
            lemma_jtf_mem(m, nl, h, offs);
        },
        Node::Then(a, b) => {
            lemma_csize_then(*a, *b, nl, h, d);
            let sa = csize(*a, nl, h, d);
            lemma_fit_mono(offs, size, sa);
            lemma_jt_bs(*a, nl, h, offs);
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    assert(flow_h(*a, nl, h, d) == h1);
                    let sb = csize(*b, nl, h1, d);
                    let ob = shift(offs, sa as int);
                    super::cfproofs::lemma_csize_mod4(*a, nl, h, d);
                    lemma_fit_shift(offs, sa, size, sb);
                    assert(ob.len() == d);
                    lemma_jt_bs(*b, nl, h1, ob);
                },
                _ => {},
            }
            lemma_jtf_then(*a, *b, nl, h, offs);
        },
        Node::Block(b) => {
            lemma_csize_block(*b, nl, h, d);
            let sb = csize(*b, nl, h, d + 1);
            let ob = seq![sb as int] + offs;
            super::cfproofs::lemma_csize_mod4(*b, nl, h, d + 1);
            lemma_fit_mono(offs, size, sb);
            lemma_fit_cons(sb as int, offs, sb);
            assert(ob.len() == d + 1);
            lemma_jt_bs(*b, nl, h, ob);
            lemma_jtf_block(*b, nl, h, offs);
        },
        Node::Loop(b) => {
            lemma_csize_loop(*b, nl, h, d);
            let sb = csize(*b, nl, h, d + 1);
            let ob = seq![0int] + offs;
            lemma_fit_mono(offs, size, sb);
            lemma_fit_cons(0, offs, sb);
            assert(ob.len() == d + 1);
            lemma_jt_bs(*b, nl, h, ob);
            lemma_jtf_loop(*b, nl, h, offs);
        },
        Node::If(t, e) => {
            lemma_csize_if(*t, *e, nl, h, d);
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 4 + se] + shift(offs, 8);
            let oe = seq![se] + shift(offs, 12 + st);
            super::cfproofs::lemma_csize_mod4(*t, nl, (h - 1) as nat, d + 1);
            super::cfproofs::lemma_csize_mod4(*e, nl, (h - 1) as nat, d + 1);
            lemma_fit_shift(offs, 8, size, st as nat);
            lemma_fit_cons(st + 4 + se, shift(offs, 8), st as nat);
            lemma_fit_shift(offs, (12 + st) as nat, size, se as nat);
            lemma_fit_cons(se, shift(offs, 12 + st), se as nat);
            assert(ot.len() == d + 1 && oe.len() == d + 1);
            lemma_jt_bs(*t, nl, (h - 1) as nat, ot);
            lemma_jt_bs(*e, nl, (h - 1) as nat, oe);
            lemma_jtf_if(*t, *e, nl, h, offs);
        },
        Node::Br(l) => {
            lemma_csize_br(l, nl, h, d);
            lemma_jtf_br(l, nl, h, offs);
        },
        Node::BrIf(l) => {
            lemma_csize_brif(l, nl, h, d);
            lemma_jtf_brif(l, nl, h, offs);
        },
        Node::BrTable(ls, dd) => {
            lemma_brt_len(ls@, dd, nl, h, offs);
            lemma_ctmpl_len(n, nl, h, offs);
            assert(size == 8 + 12 * ls@.len());
            lemma_jtf_brt(ls, dd, nl, h, offs);
        },
        Node::Exit(c, k) => {
            lemma_jtf_exit(c, k, nl, h, offs);
        },
    }
}

} // verus!
