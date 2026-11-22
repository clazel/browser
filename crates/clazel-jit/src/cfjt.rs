//! Where the jumps of the templates land (jit.md item J.9, "every emitted
//! blob is accepted", x86-64): every jump target of a node's code is one of
//! the labels it was given or one of [`bs`] (the node's own start, end, the
//! starts and ends of its parts, and the stub after a memory instruction).
//!
//! `jt c x` says that some jump of `c` lands on byte `x` of `c`, computed as
//! the validator does ([`clazel_codecheck::spec::jump_targets`]: the end of
//! the jump plus its displacement).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfaccept::*;
#[cfg(verus_only)]
use crate::cfbs::*;
#[cfg(verus_only)]
use crate::cfcompose::lemma_shift_index;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfproofs::{labels_fit, lemma_fit_cons, lemma_fit_mono, lemma_fit_shift};
#[cfg(verus_only)]
use crate::cfsimple::*;
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

/// Some jump of `c` lands on byte `x` of `c`.
pub open spec fn jt(c: Seq<x64::Instr>, x: int) -> bool {
    exists|j: int|
        0 <= j < c.len() && #[trigger] clazel_codecheck::spec::jump_rel(c[j]) is Some && x
            == clazel_codecheck::spec::start_of(c, j + 1) + clazel_codecheck::spec::jump_rel(
            c[j],
        )->Some_0
}

/// `x` is one of the labels.
pub open spec fn inoffs(offs: Seq<int>, x: int) -> bool {
    exists|l: int| 0 <= l < offs.len() && #[trigger] offs[l] == x
}

// ----------------------------------------------------------------------------
// Positions in a list of instructions
// ----------------------------------------------------------------------------

/// The byte position of instruction `j` is the length of the first `j`.
pub proof fn lemma_start_of_take(c: Seq<x64::Instr>, j: int)
    requires
        0 <= j <= c.len(),
    ensures
        clazel_codecheck::spec::start_of(c, j) == code_len(c.take(j)),
    decreases j,
{
    if j == 0 {
        assert(c.take(0) =~= Seq::<x64::Instr>::empty());
    } else {
        lemma_start_of_take(c, j - 1);
        assert(c.take(j) =~= c.take(j - 1) + seq![c[j - 1]]);
        lemma_code_len_append(c.take(j - 1), seq![c[j - 1]]);
        lemma_code_len_one(c[j - 1]);
    }
}

/// The position of the end of the list is its length.
pub proof fn lemma_start_of_end(c: Seq<x64::Instr>)
    ensures
        clazel_codecheck::spec::start_of(c, c.len() as int) == code_len(c),
{
    lemma_start_of_take(c, c.len() as int);
    assert(c.take(c.len() as int) =~= c);
}

/// Positions inside the first part of a concatenation.
pub proof fn lemma_start_of_cat_l(a: Seq<x64::Instr>, b: Seq<x64::Instr>, j: int)
    requires
        0 <= j <= a.len(),
    ensures
        clazel_codecheck::spec::start_of(a + b, j) == clazel_codecheck::spec::start_of(a, j),
{
    lemma_start_of_take(a + b, j);
    lemma_start_of_take(a, j);
    assert((a + b).take(j) =~= a.take(j));
}

/// Positions inside the second part of a concatenation.
pub proof fn lemma_start_of_cat_r(a: Seq<x64::Instr>, b: Seq<x64::Instr>, j: int)
    requires
        0 <= j <= b.len(),
    ensures
        clazel_codecheck::spec::start_of(a + b, a.len() + j) == code_len(a)
            + clazel_codecheck::spec::start_of(b, j),
{
    lemma_start_of_take(a + b, a.len() + j);
    lemma_start_of_take(b, j);
    assert((a + b).take(a.len() + j) =~= a + b.take(j));
    lemma_code_len_append(a, b.take(j));
}

/// A jump of a concatenation is a jump of a part.
pub proof fn lemma_jt_cat(a: Seq<x64::Instr>, b: Seq<x64::Instr>, x: int)
    requires
        jt(a + b, x),
    ensures
        jt(a, x) || jt(b, x - code_len(a)),
{
    let j = choose|j: int|
        0 <= j < (a + b).len() && #[trigger] clazel_codecheck::spec::jump_rel((a + b)[j]) is Some
            && x == clazel_codecheck::spec::start_of(a + b, j + 1)
            + clazel_codecheck::spec::jump_rel((a + b)[j])->Some_0;
    if j < a.len() {
        assert((a + b)[j] == a[j]);
        lemma_start_of_cat_l(a, b, j + 1);
        assert(jt(a, x));
    } else {
        let k = j - a.len();
        assert((a + b)[j] == b[k]);
        lemma_start_of_cat_r(a, b, k + 1);
        assert(clazel_codecheck::spec::jump_rel(b[k]) is Some);
        assert(x - code_len(a) == clazel_codecheck::spec::start_of(b, k + 1)
            + clazel_codecheck::spec::jump_rel(b[k])->Some_0);
        assert(jt(b, x - code_len(a)));
    }
}

/// Code with no jump has no jump target.
pub proof fn lemma_jt_none(c: Seq<x64::Instr>, x: int)
    requires
        forall|k: int| 0 <= k < c.len() ==> nojump(#[trigger] c[k]),
    ensures
        !jt(c, x),
{
}

/// The only jump is the last instruction.
pub proof fn lemma_jt_last(c: Seq<x64::Instr>, x: int)
    requires
        c.len() > 0,
        forall|k: int| 0 <= k < c.len() - 1 ==> nojump(#[trigger] c[k]),
        clazel_codecheck::spec::jump_rel(c[c.len() - 1]) is Some,
        jt(c, x),
    ensures
        x == code_len(c) + clazel_codecheck::spec::jump_rel(c[c.len() - 1])->Some_0,
{
    let j = choose|j: int|
        0 <= j < c.len() && #[trigger] clazel_codecheck::spec::jump_rel(c[j]) is Some && x
            == clazel_codecheck::spec::start_of(c, j + 1) + clazel_codecheck::spec::jump_rel(
            c[j],
        )->Some_0;
    assert(j == c.len() - 1);
    lemma_start_of_end(c);
}

/// A displacement that fits 32 bits survives the cast.
pub proof fn lemma_fit_i32(r: int)
    requires
        -0x8000_0000 <= r <= 0x7FFF_FFFF,
    ensures
        (r as i32) as int == r,
{
}

/// A `jmp` to `rel`.
pub proof fn lemma_jt_jmp(rel: int, x: int)
    requires
        -0x8000_0000 <= rel <= 0x7FFF_FFFF,
        jt(seq![jmp_i(rel)], x),
    ensures
        x == 5 + rel,
{
    let c = seq![jmp_i(rel)];
    lemma_jmp_len(rel);
    lemma_code_len_one(jmp_i(rel));
    lemma_fit_i32(rel);
    assert(clazel_codecheck::spec::jump_rel(c[0]) is Some);
    lemma_jt_last(c, x);
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

/// `br l`: the jump lands on the label.
proof fn lemma_jtf_br(l: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        l < offs.len(),
        labels_fit(offs, 5),
    ensures
        jt_facts(Node::Br(l), nl, h, offs),
{
    let rel = offs[l as int] - 5;
    assert(-0x8000_0000 <= offs[l as int] <= 0x7FFF_FFFF);
    assert forall|x: int| jt(ctmpl(Node::Br(l), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::Br(l), nl, h, offs.len(), x) by {
        assert(ctmpl(Node::Br(l), nl, h, offs) == seq![jmp_i(rel)]);
        lemma_jt_jmp(rel, x);
        assert(offs[l as int] == x);
    }
}

/// The condition test: its `jcc` is the last instruction.
proof fn lemma_jt_cond(nl: nat, h: nat, cc: u8, rel: int, x: int)
    requires
        1 <= h,
        nl + h <= max_slots(),
        -0x8000_0000 <= rel <= 0x7FFF_FFFF,
        jt(cond_pre(nl, h, cc, rel), x),
    ensures
        x == cond_len(nl, h) + rel,
{
    let c = cond_pre(nl, h, cc, rel);
    lemma_cond_pre_len(nl, h, cc, rel);
    lemma_fit_i32(rel);
    assert(c.len() == 3);
    assert(forall|k: int| 0 <= k < 2 ==> nojump(#[trigger] c[k])) by {
        assert forall|k: int| 0 <= k < 2 implies nojump(c[k]) by {
            assert(k == 0 || k == 1);
        }
    }
    assert(clazel_codecheck::spec::jump_rel(c[2]) is Some);
    lemma_jt_last(c, x);
}

/// `br_if l`.
proof fn lemma_jtf_brif(l: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        l < offs.len(),
        labels_fit(offs, cond_len(nl, h)),
    ensures
        jt_facts(Node::BrIf(l), nl, h, offs),
{
    let rel = offs[l as int] - cond_len(nl, h) as int;
    assert forall|x: int| jt(ctmpl(Node::BrIf(l), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::BrIf(l), nl, h, offs.len(), x) by {
        assert(ctmpl(Node::BrIf(l), nl, h, offs) == cond_pre(nl, h, 5, rel));
        lemma_jt_cond(nl, h, 5, rel, x);
        assert(offs[l as int] == x);
    }
}

/// `exit`: no jump.
proof fn lemma_jtf_exit(c: u32, k: usize, nl: nat, h: nat, offs: Seq<int>)
    ensures
        jt_facts(Node::Exit(c, k), nl, h, offs),
{
    assert forall|x: int| jt(ctmpl(Node::Exit(c, k), nl, h, offs), x) implies #[trigger] inoffs(
        offs,
        x,
    ) || bs(Node::Exit(c, k), nl, h, offs.len(), x) by {
        let e = exit_seq(c);
        assert(forall|j: int| 0 <= j < e.len() ==> nojump(#[trigger] e[j])) by {
            assert forall|j: int| 0 <= j < e.len() implies nojump(e[j]) by {
                assert(j == 0 || j == 1 || j == 2);
            }
        }
        lemma_jt_none(e, x);
    }
}

/// A straight-line instruction: no jump.
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

/// The chain from entry `i` on: a jump lands on a target label.
proof fn lemma_jt_entries(ls: Seq<usize>, offs: Seq<int>, p0: int, i: nat, x: int)
    requires
        i <= ls.len(),
        forall|k: int| 0 <= k < ls.len() ==> #[trigger] ls[k] < offs.len(),
        forall|l: int|
            0 <= l < offs.len() ==> -0x8000_0000 + p0 + ls.len() * 13 + 5 <= #[trigger] offs[l]
                && offs[l] <= 0x7FFF_FFFF,
        0 <= p0,
        jt(brt_entries(ls, offs, p0, i), x),
    ensures
        exists|k: int|
            i <= k < ls.len() && x + p0 + i * 13 == #[trigger] offs[ls[k] as int],
    decreases ls.len() - i,
{
    if i >= ls.len() {
        assert(brt_entries(ls, offs, p0, i) =~= Seq::<x64::Instr>::empty());
        assert(false);
    } else {
        lemma_brt_entry_len(i, 0);
        let rel = brt_rel(offs, ls[i as int], p0 + (i + 1) * brt_e());
        let e = brt_entry(i, rel);
        let rest = brt_entries(ls, offs, p0, i + 1);
        assert(brt_entries(ls, offs, p0, i) == e + rest);
        lemma_jt_cat(e, rest, x);
        lemma_brt_entry_len(i, rel);
        if jt(e, x) {
            assert(ls[i as int] < offs.len());
            let t = ls[i as int] as int;
            assert(rel == offs[t] - (p0 + (i + 1) * 13));
            assert((i + 1) * 13 <= ls.len() * 13) by (nonlinear_arith)
                requires
                    i < ls.len(),
            ;
            assert(-0x8000_0000 <= rel <= 0x7FFF_FFFF);
            lemma_fit_i32(rel);
            assert(forall|k: int| 0 <= k < e.len() - 1 ==> nojump(#[trigger] e[k])) by {
                assert forall|k: int| 0 <= k < e.len() - 1 implies nojump(e[k]) by {
                    assert(k == 0 || k == 1);
                }
            }
            assert(e.len() == 3);
            assert(clazel_codecheck::spec::jump_rel(e[2]) is Some);
            lemma_jt_last(e, x);
            assert(x + p0 + i * 13 == offs[t]);
            assert(offs[ls[i as int] as int] == x + p0 + i * 13);
            assert(i <= i && i < ls.len());
        } else {
            assert(jt(rest, x - 13));
            lemma_jt_entries(ls, offs, p0, i + 1, x - 13);
            let k = choose|k: int|
                i + 1 <= k < ls.len() && (x - 13) + p0 + (i + 1) * 13 == #[trigger] offs[ls[k] as int];
            assert(x + p0 + i * 13 == offs[ls[k] as int]);
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
        labels_fit(offs, 13 + 13 * ls@.len()),
    ensures
        jt_facts(Node::BrTable(ls, d), nl, h, offs),
{
    crate::cfbrt::lemma_brt_p0(nl, h);
    let p0 = brt_p0(nl, h);
    let n = ls@.len();
    let a = seq![load_slot(rax(), (nl + h - 1) as nat)];
    let ch = brt_entries(ls@, offs, p0, 0);
    let jm = seq![jmp_i(brt_rel(offs, d, p0 + n * brt_e() + 5))];
    let whole = brt_code(ls@, d, nl, h, offs);
    lemma_brt_entry_len(0, 0);
    assert(whole =~= a + (ch + jm));
    crate::cfbrt::lemma_entries_len(ls@, offs, p0, 0);
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
        lemma_len1(load_slot(rax(), (nl + h - 1) as nat));
        lemma_mem_instr_lens((nl + h - 1) as nat, 0);
        if jt(ch, x - code_len(a)) {
            assert forall|l: int|
                0 <= l < offs.len() implies -0x8000_0000 + p0 + n * 13 + 5 <= #[trigger] offs[l]
                && offs[l] <= 0x7FFF_FFFF by {}
            lemma_jt_entries(ls@, offs, p0, 0, x - code_len(a));
            let k = choose|k: int|
                0 <= k < n && (x - code_len(a)) + p0 + 0 * 13 == #[trigger] offs[ls@[k] as int];
            assert(offs[ls@[k] as int] == x);
            assert(inoffs(offs, x));
        } else {
            let z = x - code_len(a) - code_len(ch);
            assert(jt(jm, z));
            let rel = brt_rel(offs, d, p0 + n * brt_e() + 5);
            assert(rel == offs[d as int] - (13 + 13 * n));
            lemma_fit_i32(rel);
            assert(clazel_codecheck::spec::jump_rel(jm[0]) is Some);
            lemma_jmp_len(rel);
            lemma_code_len_one(jmp_i(rel));
            lemma_jt_last(jm, z);
            assert(x == offs[d as int]);
            assert(inoffs(offs, x));
        }
    }
}

// ----------------------------------------------------------------------------
// Memory instructions
// ----------------------------------------------------------------------------

/// The check's two exits: the validator's own sequence, whose `jcc`s are the
/// third and fifth instructions.
proof fn lemma_jt_chk(c: clazel_codecheck::spec::Chk, x: int)
    requires
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
        jt(clazel_codecheck::spec::check_seq(c), x),
    ensures
        x == 16 + c.r1 as int || x == 30 + c.r2 as int,
{
    let cs = clazel_codecheck::spec::check_seq(c);
    lemma_check_instr_lens(c);
    assert(cs[0] == clazel_codecheck::spec::check_instr(0, c));
    assert(cs[1] == clazel_codecheck::spec::check_instr(1, c));
    assert(cs[2] == clazel_codecheck::spec::check_instr(2, c));
    assert(cs[3] == clazel_codecheck::spec::check_instr(3, c));
    assert(cs[4] == clazel_codecheck::spec::check_instr(4, c));
    assert(cs[5] == clazel_codecheck::spec::check_instr(5, c));
    assert(cs[6] == clazel_codecheck::spec::check_instr(6, c));
    assert(cs[7] == clazel_codecheck::spec::check_instr(7, c));
    let j = choose|j: int|
        0 <= j < cs.len() && #[trigger] clazel_codecheck::spec::jump_rel(cs[j]) is Some && x
            == clazel_codecheck::spec::start_of(cs, j + 1) + clazel_codecheck::spec::jump_rel(
            cs[j],
        )->Some_0;
    assert(j == 2 || j == 4);
    reveal_with_fuel(clazel_codecheck::spec::start_of, 6);
    assert(clazel_codecheck::spec::start_of(cs, 3) == 16);
    assert(clazel_codecheck::spec::start_of(cs, 5) == 30);
}

/// A memory instruction: its jumps land on the stub, or at its end.
proof fn lemma_jtf_mem(m: MemOp, nl: nat, h: nat, offs: Seq<int>)
    requires
        mem_region(m) < 16,
    ensures
        jt_facts(Node::Mem(m), nl, h, offs),
{
    lemma_mem_csize(m, nl, h, offs.len());
    lemma_mem_parts_len(m, nl, h);
    let pre = mem_pre(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let chk = mem_check(m, nl, h);
    let jm = seq![jmp_i(code_len(exit_seq(mem_exit_code(m))) as int)];
    let stub = exit_seq(mem_exit_code(m));
    lemma_exit_seq_len(mem_exit_code(m));
    let c0 = mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h));
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
        lemma_code_len_append(a1, tail);
        lemma_code_len_append(pre, chk);
        if jt(jm, x - code_len(a2)) {
            lemma_jmp_len(code_len(stub) as int);
            lemma_jt_jmp(code_len(stub) as int, x - code_len(a2));
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
                    assert(ctmpl(b, nl, h1, ob) =~= Seq::<x64::Instr>::empty());
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
            csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 5 + csize(
                e,
                nl,
                (h - 1) as nat,
                offs.len() + 1,
            ) as int,
        ] + shift(offs, cond_len(nl, h) as int)),
        jt_facts(e, nl, (h - 1) as nat, seq![csize(e, nl, (h - 1) as nat, offs.len() + 1) as int]
            + shift(
            offs,
            cond_len(nl, h) as int + csize(t, nl, (h - 1) as nat, offs.len() + 1) as int + 5,
        )),
    ensures
        jt_facts(Node::If(Box::new(t), Box::new(e)), nl, h, offs),
{
    let n = Node::If(Box::new(t), Box::new(e));
    let d = offs.len();
    let h0 = (h - 1) as nat;
    let p = cond_len(nl, h) as int;
    let st = csize(t, nl, h0, d + 1) as int;
    let se = csize(e, nl, h0, d + 1) as int;
    let ot = seq![st + 5 + se] + shift(offs, p);
    let oe = seq![se] + shift(offs, p + st + 5);
    assert(ot.len() == d + 1 && oe.len() == d + 1);
    lemma_csize_if(t, e, nl, h, d);
    lemma_bs_facts(t, nl, h0, d + 1);
    lemma_bs_facts(e, nl, h0, d + 1);
    let cp = cond_pre(nl, h, 4, st + 5);
    let ct = ctmpl(t, nl, h0, ot);
    let ce = ctmpl(e, nl, h0, oe);
    let jm = seq![jmp_i(se)];
    lemma_ctmpl_len(t, nl, h0, ot);
    lemma_ctmpl_len(e, nl, h0, oe);
    lemma_cond_pre_len(nl, h, 4, st + 5);
    lemma_jmp_len(se);
    lemma_code_len_one(jmp_i(se));
    assert(st + 5 + se <= max_size());
    assert forall|x: int| jt(ctmpl(n, nl, h, offs), x) implies #[trigger] inoffs(offs, x) || bs(
        n,
        nl,
        h,
        d,
        x,
    ) by {
        assert(ctmpl(n, nl, h, offs) == cp + ct + jm + ce);
        lemma_jt_cat(cp + ct + jm, ce, x);
        lemma_code_len_append(cp, ct);
        lemma_code_len_append(cp + ct, jm);
        if jt(cp + ct + jm, x) {
            lemma_jt_cat(cp + ct, jm, x);
            if jt(cp + ct, x) {
                lemma_jt_cat(cp, ct, x);
                if jt(cp, x) {
                    lemma_jt_cond(nl, h, 4, st + 5, x);
                    assert(bs(e, nl, h0, d + 1, 0));
                    assert(x - (p + st + 5) == 0);
                } else {
                    let y = x - p;
                    assert(jt(ct, y));
                    if inoffs(ot, y) {
                        let l = choose|l: int| 0 <= l < ot.len() && #[trigger] ot[l] == y;
                        if l == 0 {
                            assert(x == p + st + 5 + se);
                            assert(bs(e, nl, h0, d + 1, se));
                        } else {
                            assert(ot[l] == shift(offs, p)[l - 1]);
                            lemma_shift_index(offs, p, l - 1);
                            assert(offs[l - 1] == x);
                            assert(inoffs(offs, x));
                        }
                    } else {
                        assert(bs(t, nl, h0, d + 1, y));
                    }
                }
            } else {
                lemma_jt_jmp(se, x - code_len(cp + ct));
                assert(x == p + st + 5 + se);
                assert(bs(e, nl, h0, d + 1, se));
            }
        } else {
            let y = x - (p + st + 5);
            assert(jt(ce, y));
            if inoffs(oe, y) {
                let l = choose|l: int| 0 <= l < oe.len() && #[trigger] oe[l] == y;
                if l == 0 {
                    assert(bs(e, nl, h0, d + 1, se));
                } else {
                    assert(oe[l] == shift(offs, p + st + 5)[l - 1]);
                    lemma_shift_index(offs, p + st + 5, l - 1);
                    assert(offs[l - 1] == x);
                    assert(inoffs(offs, x));
                }
            } else {
                assert(bs(e, nl, h0, d + 1, y));
            }
        }
    }
}

/// **Every jump of a node's code lands on a label it was given, or on a
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
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 5 + se] + shift(offs, p);
            let oe = seq![se] + shift(offs, p + st + 5);
            lemma_fit_shift(offs, p as nat, size, st as nat);
            lemma_fit_cons(st + 5 + se, shift(offs, p), st as nat);
            lemma_fit_shift(offs, (p + st + 5) as nat, size, se as nat);
            lemma_fit_cons(se, shift(offs, p + st + 5), se as nat);
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
            crate::cfbrt::lemma_brt_fetch_jmp(ls@, dd, nl, h, seq![]);
            crate::cflens::lemma_ctmpl_len(n, nl, h, offs);
            crate::cfbrt::lemma_brt_fetch_jmp(ls@, dd, nl, h, offs);
            assert(size == 13 + 13 * ls@.len());
            lemma_jtf_brt(ls, dd, nl, h, offs);
        },
        Node::Exit(c, k) => {
            lemma_jtf_exit(c, k, nl, h, offs);
        },
    }
}

} // verus!
