//! **Composition over structured control flow**: how the [`cf_refines`]
//! statement of a node follows from those of its parts. One lemma per way of
//! combining: `then` ([`lemma_then`]), `block` ([`lemma_block`]), `loop`
//! ([`lemma_loop`]), `if` ([`crate::cfif::lemma_if`]). The leaves
//! (`br`, `br_if`, `exit`, straight-line instructions) are in
//! [`crate::cfleaf`]; [`crate::cfproofs`] puts them together by induction on
//! the node.
//!
//! Two lifting lemmas do the bookkeeping the cases share: a statement about a
//! part, from the state after the code before it ([`lemma_lift_pre`]), and one
//! about the code followed by more ([`lemma_lift_post`]).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfheight::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `shift(offs, d)` at `l` is `offs[l] - d`.
pub proof fn lemma_shift_index(offs: Seq<int>, d: int, l: int)
    requires
        0 <= l < offs.len(),
    ensures
        shift(offs, d).len() == offs.len(),
        shift(offs, d)[l] == offs[l] - d,
{
}

/// **Lifting a part's statement to the code that starts with something
/// else.** `c`'s outcome `o`, seen from `m1` (the state after the code
/// `pre`, which ran from `m`), is the outcome of `pre + c` from `m`, with the
/// labels moved by the length of `pre`.
pub proof fn lemma_lift_pre(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    offs_c: Seq<int>,
    pre: Seq<x64::Instr>,
    c: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    m1: x64::State,
    o: lir::Outcome,
)
    requires
        offs_c.len() == offs.len(),
        forall|l: int| 0 <= l < offs.len() ==> #[trigger] offs_c[l] + code_len(pre) == offs[l],
        m1.rip == m.rip + code_len(pre),
        reaches(cu, pre + c, m.rip, m, m1),
        preserved_r(lay, m, m1),
        stack_ok_r(lay, m),
        cf_post(lay, base, nl, offs_c, c, cu, m1, o),
    ensures
        cf_post(lay, base, nl, offs, pre + c, cu, m, o),
{
    super::steps::lemma_abi_consts();
    lemma_stack_pres(lay, m, m1);
    assert(ctx_of(m1) == ctx_of(m));
    let d = code_len(pre);
    match o {
        lir::Outcome::Normal(a2) => {
            let m2 = choose|m2: x64::State|
                reaches(cu, c, m1.rip, m1, m2) && m2.rip == m1.rip + code_len(c) && rel_base(
                    lay,
                    base,
                    a2,
                    m2,
                    nl,
                ) && preserved_r(lay, m1, m2);
            assert(pre + c + Seq::<x64::Instr>::empty() =~= pre + c);
            lemma_reaches_embed(cu, pre, c, Seq::empty(), m1.rip, m1, m2);
            assert(m1.rip - d == m.rip);
            lemma_reaches_trans(cu, pre + c, m.rip, m, m1, m2);
            super::runseq::lemma_code_len_append(pre, c);
            lemma_pr_trans(lay, m, m1, m2);
            assert(reaches(cu, pre + c, m.rip, m, m2) && m2.rip == m.rip + code_len(pre + c)
                && rel_base(lay, base, a2, m2, nl) && preserved_r(lay, m, m2));
        },
        lir::Outcome::Branch(l, s) => {
            let m2 = choose|m2: x64::State|
                reaches(cu, c, m1.rip, m1, m2) && m2.rip == m1.rip + offs_c[l as int] && rel_ext(
                    lay,
                    base,
                    s,
                    m2,
                    nl,
                ) && preserved_r(lay, m1, m2);
            assert(pre + c + Seq::<x64::Instr>::empty() =~= pre + c);
            lemma_reaches_embed(cu, pre, c, Seq::empty(), m1.rip, m1, m2);
            assert(m1.rip - d == m.rip);
            lemma_reaches_trans(cu, pre + c, m.rip, m, m1, m2);
            lemma_pr_trans(lay, m, m1, m2);
            assert(l < offs.len());
            assert(offs_c[l as int] + d == offs[l as int]);
        },
        lir::Outcome::Exit(code, vals, s) => {
            let m2 = choose|m2: x64::State|
                reaches(cu, c, m1.rip, m1, m2) && exit_done(m1, m2, code) && exit_rel(
                    lay,
                    base,
                    s,
                    m2,
                    nl,
                    ctx_of(m1),
                    vals,
                ) && preserved_mem_r(lay, m1, m2);
            assert(pre + c + Seq::<x64::Instr>::empty() =~= pre + c);
            lemma_reaches_embed(cu, pre, c, Seq::empty(), m1.rip, m1, m2);
            assert(m1.rip - d == m.rip);
            lemma_reaches_trans(cu, pre + c, m.rip, m, m1, m2);
            lemma_pr_pmr_trans(lay, m, m1, m2);
            assert(exit_done(m, m2, code));
        },
        _ => {},
    }
}

/// **Lifting a statement to the code followed by more**, for an outcome other
/// than falling through (which would end earlier).
pub proof fn lemma_lift_post(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    c: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    o: lir::Outcome,
)
    requires
        !(o is Normal),
        cf_post(lay, base, nl, offs, c, cu, m, o),
    ensures
        cf_post(lay, base, nl, offs, c + post, cu, m, o),
{
    match o {
        lir::Outcome::Branch(l, s) => {
            let m2 = choose|m2: x64::State|
                reaches(cu, c, m.rip, m, m2) && m2.rip == m.rip + offs[l as int] && rel_ext(
                    lay,
                    base,
                    s,
                    m2,
                    nl,
                ) && preserved_r(lay, m, m2);
            assert(Seq::<x64::Instr>::empty() + c + post =~= c + post);
            lemma_reaches_embed(cu, Seq::empty(), c, post, m.rip, m, m2);
            assert(code_len(Seq::<x64::Instr>::empty()) == 0);
        },
        lir::Outcome::Exit(code, vals, s) => {
            let m2 = choose|m2: x64::State|
                reaches(cu, c, m.rip, m, m2) && exit_done(m, m2, code) && exit_rel(
                    lay,
                    base,
                    s,
                    m2,
                    nl,
                    ctx_of(m),
                    vals,
                ) && preserved_mem_r(lay, m, m2);
            assert(Seq::<x64::Instr>::empty() + c + post =~= c + post);
            lemma_reaches_embed(cu, Seq::empty(), c, post, m.rip, m, m2);
            assert(code_len(Seq::<x64::Instr>::empty()) == 0);
        },
        _ => {},
    }
}

/// `cf_canon` for the first part of a sequence.
pub proof fn lemma_canon_prefix(rip: int, offs: Seq<int>, a: Seq<x64::Instr>, b: Seq<x64::Instr>)
    requires
        x64::canonical(rip),
        cf_canon(rip, offs, a + b),
    ensures
        cf_canon(rip, offs, a),
{
    super::runseq::lemma_code_len_append(a, b);
    super::runseq::lemma_canonical_between(rip, rip + code_len(a), rip + code_len(a + b));
}

/// **`then`.** If the first instruction falls through at height `h1` and its
/// code and the second's (whose labels are the first's moved by its length)
/// refine them, their concatenation refines the pair.
#[verifier::rlimit(400)]
pub proof fn lemma_then(
    x: Node,
    y: Node,
    nl: nat,
    h: nat,
    h1: nat,
    offs: Seq<int>,
    cx: Seq<x64::Instr>,
    cy: Seq<x64::Instr>,
)
    requires
        cf_flow(x, nl, h, offs.len()) == Some(Flow::Falls(h1)),
        cf_refines(x@, nl, h, offs, cx),
        cf_refines(y@, nl, h1, shift(offs, code_len(cx) as int), cy),
    ensures
        cf_refines(Node::Then(Box::new(x), Box::new(y))@, nl, h, offs, cx + cy),
{
    let t = Node::Then(Box::new(x), Box::new(y));
    let big = cx + cy;
    super::runseq::lemma_code_len_append(cx, cy);
    let ll = code_len(cx) as int;
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, big, cu, m, lir::eval(lay, t@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, big) implies cf_post(
        lay,
        base,
        nl,
        offs,
        big,
        cu,
        m,
        lir::eval(lay, t@, a, fuel),
    ) by {
        if fuel > 0 {
            let f = (fuel - 1) as nat;
            lemma_rel_base_unfold(lay, base, a, m, nl);
            assert(x64::canonical(m.rip));
            lemma_canon_prefix(m.rip, offs, cx, cy);
            lemma_use_cf(x@, nl, h, offs, cx, lay, cu, base, a, m, f);
            let o1 = lir::eval(lay, x@, a, f);
            match o1 {
                lir::Outcome::Normal(a1) => {
                    let m1 = choose|m1: x64::State|
                        reaches(cu, cx, m.rip, m, m1) && m1.rip == m.rip + code_len(cx)
                            && rel_base(lay, base, a1, m1, nl) && preserved_r(lay, m, m1);
                    lemma_cf_height(x, nl, h, offs.len(), h1, base.len(), lay, a, a1, f);
                    lemma_stack_pres(lay, m, m1);
                    assert(x64::canonical(m1.rip));
                    assert forall|l: int| 0 <= l < shift(offs, ll).len() implies x64::canonical(
                        m1.rip + #[trigger] shift(offs, ll)[l],
                    ) by {
                        lemma_shift_index(offs, ll, l);
                        assert(cf_canon(m.rip, offs, big));
                        assert(x64::canonical(m.rip + offs[l]));
                    }
                    assert(cf_canon(m1.rip, shift(offs, ll), cy));
                    lemma_use_cf(y@, nl, h1, shift(offs, ll), cy, lay, cu, base, a1, m1, f);
                    assert(Seq::<x64::Instr>::empty() + cx + cy =~= cx + cy);
                    lemma_reaches_embed(cu, Seq::empty(), cx, cy, m.rip, m, m1);
                    assert(code_len(Seq::<x64::Instr>::empty()) == 0);
                    assert forall|l: int| 0 <= l < offs.len() implies #[trigger] shift(offs, ll)[l]
                        + code_len(cx) == offs[l] by {
                        lemma_shift_index(offs, ll, l);
                    }
                    lemma_lift_pre(
                        lay,
                        base,
                        nl,
                        offs,
                        shift(offs, ll),
                        cx,
                        cy,
                        cu,
                        m,
                        m1,
                        lir::eval(lay, y@, a1, f),
                    );
                },
                _ => {
                    lemma_lift_post(lay, base, nl, offs, cx, cy, cu, m, o1);
                },
            }
        }
    }
}

/// **`then` whose first part is dead** (a `br`, `br_table` or `exit`): only
/// `nop` follows, and it has no code, so the pair's code is the first's.
pub proof fn lemma_then_dead(
    x: Node,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    cx: Seq<x64::Instr>,
)
    requires
        cf_flow(x, nl, h, offs.len()) == Some(Flow::Dead),
        cf_refines(x@, nl, h, offs, cx),
    ensures
        cf_refines(
            Node::Then(Box::new(x), Box::new(Node::Op(Op::Nop)))@,
            nl,
            h,
            offs,
            cx,
        ),
{
    let t = Node::Then(Box::new(x), Box::new(Node::Op(Op::Nop)));
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, cx, cu, m, lir::eval(lay, t@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, cx) implies cf_post(
        lay,
        base,
        nl,
        offs,
        cx,
        cu,
        m,
        lir::eval(lay, t@, a, fuel),
    ) by {
        if fuel > 0 {
            let f = (fuel - 1) as nat;
            lemma_use_cf(x@, nl, h, offs, cx, lay, cu, base, a, m, f);
            lemma_dead_not_normal(x, nl, h, offs.len(), lay, a, f);
        }
    }
}

} // verus!
