//! `block` and `loop`: a body's [`cf_post`], on top of the stack the block was
//! entered with, becomes the block's. Four transports (falling out of the
//! body, a branch to the block's own label, a branch past it, an exit), then
//! the two lemmas that use them.

use crate::cfalg::*;
use crate::cfcompose::*;
use crate::cfcontract::*;
use crate::cfheight::*;
use crate::cfspec::*;
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The body of a block, entered with the outer stack `ast` as its `base`, is
/// related to the same machine state as the block: `rel_base` with the
/// stacks concatenated.
pub proof fn lemma_rel_base_cat(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    s: lir::St,
    m: x64::State,
    nl: nat,
)
    requires
        rel_base(lay, base + ast, s, m, nl),
    ensures
        rel_base(lay, base, s.with_stack(ast + s.stack), m, nl),
{
    reveal(rel_base);
    assert((base + ast) + s.stack =~= base + (ast + s.stack));
    assert(s.with_stack(ast + s.stack).with_stack(base + (ast + s.stack)) == s.with_stack(
        base + (ast + s.stack),
    ));
}

/// The block's start state, as the body's: the outer stack `a.stack` becomes
/// the body's `base`, and the body's own stack is empty.
pub proof fn lemma_rel_base_enter(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    nl: nat,
)
    requires
        rel_base(lay, base, a, m, nl),
    ensures
        rel_base(lay, base + a.stack, fresh(a), m, nl),
{
    reveal(rel_base);
    assert(base + a.stack + Seq::<lir::Val>::empty() =~= base + a.stack);
    assert(fresh(a).with_stack(base + a.stack + fresh(a).stack) == a.with_stack(base + a.stack));
}

/// Concatenation of stacks is associative inside [`rel_base`].
pub proof fn lemma_rel_base_assoc(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    x: Seq<lir::Val>,
    y: Seq<lir::Val>,
    s: lir::St,
    m: x64::State,
    nl: nat,
)
    ensures
        rel_base(lay, base + x + y, s, m, nl) == rel_base(lay, base + (x + y), s, m, nl),
{
    reveal(rel_base);
    assert(base + x + y =~= base + (x + y));
}

/// **Falling out of the body.** The body's `Normal(s)` is the block's
/// `Normal(s)` on top of the outer stack.
pub proof fn lemma_blk_normal(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    c: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    s: lir::St,
    offs_b: Seq<int>,
)
    requires
        cf_post(lay, base + ast, nl, offs_b, c, cu, m, lir::Outcome::Normal(s)),
    ensures
        cf_post(lay, base, nl, offs, c, cu, m, lir::Outcome::Normal(s.with_stack(ast + s.stack))),
{
    let m2 = choose|m2: x64::State|
        reaches(cu, c, m.rip, m, m2) && m2.rip == m.rip + code_len(c) && rel_base(
            lay,
            base + ast,
            s,
            m2,
            nl,
        ) && preserved_r(lay, m, m2);
    lemma_rel_base_cat(lay, base, ast, s, m2, nl);
}

/// Seen from outside the block, the body's extra values include the block's
/// outer stack.
pub proof fn lemma_rel_ext_cat(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    s: lir::St,
    m2: x64::State,
    nl: nat,
)
    requires
        rel_ext(lay, base + ast, s, m2, nl),
    ensures
        rel_ext(lay, base, s, m2, nl),
{
    let extra = choose|extra: Seq<lir::Val>| rel_base(lay, base + ast + extra, s, m2, nl);
    lemma_rel_base_assoc(lay, base, ast, extra, s, m2, nl);
    let extra2 = ast + extra;
    assert(rel_base(lay, base + extra2, s, m2, nl));
}

/// As [`lemma_rel_ext_cat`], for an exit's operands.
pub proof fn lemma_exit_rel_cat(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    s: lir::St,
    m2: x64::State,
    nl: nat,
    ctxb: int,
    vals: Seq<lir::Val>,
)
    requires
        exit_rel(lay, base + ast, s, m2, nl, ctxb, vals),
    ensures
        exit_rel(lay, base, s, m2, nl, ctxb, vals),
{
    let extra = choose|extra: Seq<lir::Val>|
        rel_base(lay, base + ast + extra, s, m2, nl) && ops_in_frame(
            m2.mem,
            ctxb,
            nl,
            (base + ast + extra).len() + s.stack.len(),
            vals,
        );
    lemma_rel_base_assoc(lay, base, ast, extra, s, m2, nl);
    let extra2 = ast + extra;
    assert(rel_base(lay, base + extra2, s, m2, nl));
    assert((base + extra2).len() == (base + ast + extra).len());
}

/// The relation part of a branch to the block's own label: with the body's
/// base extended by the outer stack and some extra values, the outer stack
/// alone is related.
pub proof fn lemma_br0_rel(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    s: lir::St,
    m2: x64::State,
    nl: nat,
)
    requires
        rel_ext(lay, base + ast, s, m2, nl),
    ensures
        rel_base(lay, base, s.with_stack(ast), m2, nl),
{
    reveal(rel_base);
    let extra = choose|extra: Seq<lir::Val>| rel_base(lay, base + ast + extra, s, m2, nl);
    let full = base + ast + extra + s.stack;
    assert(rel(lay, s.with_stack(full), m2, nl));
    assert(full.take((base + ast).len() as int) =~= base + ast);
    lemma_rel_prefix(lay, s, full, base + ast, m2, nl);
    assert(s.with_stack(ast).with_stack(base + ast) == s.with_stack(base + ast));
}

/// **A branch to the block's own label** (label 0 of the body) is the block
/// ending: the state is related to the outer stack alone, at the end of the
/// block's code (`offs_b[0]` is its length).
pub proof fn lemma_blk_br0(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    c: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    s: lir::St,
    offs_b: Seq<int>,
)
    requires
        offs_b.len() > 0,
        offs_b[0] == code_len(c),
        cf_post(lay, base + ast, nl, offs_b, c, cu, m, lir::Outcome::Branch(0, s)),
    ensures
        cf_post(lay, base, nl, offs, c, cu, m, lir::Outcome::Normal(s.with_stack(ast))),
{
    let m2 = choose|m2: x64::State|
        reaches(cu, c, m.rip, m, m2) && m2.rip == m.rip + offs_b[0] && rel_ext(
            lay,
            base + ast,
            s,
            m2,
            nl,
        ) && preserved_r(lay, m, m2);
    lemma_br0_rel(lay, base, ast, s, m2, nl);
}

/// **A branch past the block** (label `n + 1` of the body is the block's
/// label `n`): still a branch, on top of more values.
pub proof fn lemma_blk_brn(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    c: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    n: nat,
    s: lir::St,
    offs_b: Seq<int>,
)
    requires
        n > 0,
        n < offs_b.len(),
        ((n - 1) as nat) < offs.len(),
        offs_b[n as int] == offs[((n - 1) as nat) as int],
        cf_post(lay, base + ast, nl, offs_b, c, cu, m, lir::Outcome::Branch(n, s)),
    ensures
        cf_post(lay, base, nl, offs, c, cu, m, lir::Outcome::Branch((n - 1) as nat, s)),
{
    let m2 = choose|m2: x64::State|
        reaches(cu, c, m.rip, m, m2) && m2.rip == m.rip + offs_b[n as int] && rel_ext(
            lay,
            base + ast,
            s,
            m2,
            nl,
        ) && preserved_r(lay, m, m2);
    lemma_rel_ext_cat(lay, base, ast, s, m2, nl);
}

/// **An exit inside the body** is the block's exit, on top of more values.
pub proof fn lemma_blk_exit(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    ast: Seq<lir::Val>,
    nl: nat,
    offs: Seq<int>,
    c: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    code: nat,
    vals: Seq<lir::Val>,
    s: lir::St,
    offs_b: Seq<int>,
)
    requires
        cf_post(lay, base + ast, nl, offs_b, c, cu, m, lir::Outcome::Exit(code, vals, s)),
    ensures
        cf_post(lay, base, nl, offs, c, cu, m, lir::Outcome::Exit(code, vals, s)),
{
    let m2 = choose|m2: x64::State|
        reaches(cu, c, m.rip, m, m2) && exit_done(m, m2, code) && exit_rel(
            lay,
            base + ast,
            s,
            m2,
            nl,
            ctx_of(m),
            vals,
        ) && preserved_mem_r(lay, m, m2);
    lemma_exit_rel_cat(lay, base, ast, s, m2, nl, ctx_of(m), vals);
}

/// **`block`.** If the body's code refines the body with the block's label
/// added at the end of the code, the code refines the `block`.
#[verifier::rlimit(400)]
pub proof fn lemma_block(b: Node, nl: nat, h: nat, offs: Seq<int>, cb: Seq<x64::Instr>)
    requires
        cf_refines(b@, nl, h, seq![code_len(cb) as int] + offs, cb),
    ensures
        cf_refines(Node::Block(Box::new(b))@, nl, h, offs, cb),
{
    let t = Node::Block(Box::new(b));
    let offs_b = seq![code_len(cb) as int] + offs;
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, cb, cu, m, lir::eval(lay, t@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, cb) implies cf_post(
        lay,
        base,
        nl,
        offs,
        cb,
        cu,
        m,
        lir::eval(lay, t@, a, fuel),
    ) by {
        if fuel > 0 {
            let f = (fuel - 1) as nat;
            lemma_eval_block(lay, b, a, fuel);
            lemma_rel_base_enter(lay, base, a, m, nl);
            assert(cf_canon(m.rip, offs_b, cb)) by {
                assert forall|l: int| 0 <= l < offs_b.len() implies x64::canonical(
                    m.rip + #[trigger] offs_b[l],
                ) by {
                    if l > 0 {
                        assert(offs_b[l] == offs[l - 1]);
                    } else {
                        assert(offs_b[0] == code_len(cb) as int);
                    }
                }
            }
            assert((base + a.stack).len() + fresh(a).stack.len() == h);
            lemma_use_cf(b@, nl, h, offs_b, cb, lay, cu, base + a.stack, fresh(a), m, f);
            let o = lir::eval(lay, b@, fresh(a), f);
            match o {
                lir::Outcome::Normal(s) => {
                    lemma_blk_normal(lay, base, a.stack, nl, offs, cb, cu, m, s, offs_b);
                },
                lir::Outcome::Branch(n, s) => {
                    if n == 0 {
                        assert(lir::top(s.stack, 0) =~= Seq::<lir::Val>::empty());
                        assert(a.stack + lir::top(s.stack, 0) =~= a.stack);
                        lemma_blk_br0(lay, base, a.stack, nl, offs, cb, cu, m, s, offs_b);
                    } else {
                        assert(n < offs_b.len());
                        assert(((n - 1) as nat) < offs.len());
                        assert(offs_b[n as int] == offs[((n - 1) as nat) as int]);
                        lemma_blk_brn(lay, base, a.stack, nl, offs, cb, cu, m, n, s, offs_b);
                    }
                },
                lir::Outcome::Exit(c, vals, s) => {
                    lemma_blk_exit(lay, base, a.stack, nl, offs, cb, cu, m, c, vals, s, offs_b);
                },
                _ => {},
            }
        }
    }
}

/// **`loop`, at one fuel.** By induction on the fuel: a branch to the loop's
/// label restarts it, from the state after the body, which is related to the
/// loop's own entry state with the outer stack alone.
#[verifier::rlimit(400)]
pub proof fn lemma_loop_fuel(
    b: Node,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    cb: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    fuel: nat,
)
    requires
        cf_refines(b@, nl, h, seq![0int] + offs, cb),
        base.len() + a.stack.len() == h,
        rel_base(lay, base, a, m, nl),
        stack_ok_r(lay, m),
        cf_canon(m.rip, offs, cb),
    ensures
        cf_post(lay, base, nl, offs, cb, cu, m, lir::eval(lay, Node::Loop(Box::new(b))@, a, fuel)),
    decreases fuel,
{
    let t = Node::Loop(Box::new(b));
    let offs_b = seq![0int] + offs;
    if fuel > 0 {
        let f = (fuel - 1) as nat;
        lemma_eval_loop(lay, b, a, fuel);
        lemma_rel_base_enter(lay, base, a, m, nl);
        lemma_rel_base_unfold(lay, base, a, m, nl);
        assert(cf_canon(m.rip, offs_b, cb)) by {
            assert forall|l: int| 0 <= l < offs_b.len() implies x64::canonical(
                m.rip + #[trigger] offs_b[l],
            ) by {
                if l > 0 {
                    assert(offs_b[l] == offs[l - 1]);
                } else {
                    assert(offs_b[0] == 0);
                }
            }
        }
        assert((base + a.stack).len() + fresh(a).stack.len() == h);
        lemma_use_cf(b@, nl, h, offs_b, cb, lay, cu, base + a.stack, fresh(a), m, f);
        let restart = Some(lir::Instr::Loop(void_bt(), Box::new(b@)));
        let o = lir::eval(lay, b@, fresh(a), f);
        match o {
            lir::Outcome::Normal(s) => {
                lemma_blk_normal(lay, base, a.stack, nl, offs, cb, cu, m, s, offs_b);
            },
            lir::Outcome::Branch(n, s) => {
                if n > 0 {
                    assert(n < offs_b.len());
                    assert(((n - 1) as nat) < offs.len());
                    assert(offs_b[n as int] == offs[((n - 1) as nat) as int]);
                    lemma_blk_brn(lay, base, a.stack, nl, offs, cb, cu, m, n, s, offs_b);
                } else {
                    assert(lir::top(s.stack, 0) =~= Seq::<lir::Val>::empty());
                    assert(a.stack + lir::top(s.stack, 0) =~= a.stack);
                    if f > 0 {
                        // the machine is back at the start of the loop
                        let m1 = choose|m1: x64::State|
                            reaches(cu, cb, m.rip, m, m1) && m1.rip == m.rip + offs_b[0]
                                && rel_ext(lay, base + a.stack, s, m1, nl)
                                && preserved_r(lay, m, m1);
                        let extra = choose|extra: Seq<lir::Val>|
                            rel_base(lay, base + a.stack + extra, s, m1, nl);
                        reveal(rel_base);
                        let full = base + a.stack + extra + s.stack;
                        assert(rel(lay, s.with_stack(full), m1, nl));
                        assert(full.take((base + a.stack).len() as int) =~= base + a.stack);
                        lemma_rel_prefix(lay, s, full, base + a.stack, m1, nl);
                        let a1 = s.with_stack(a.stack);
                        assert(a1.with_stack(base + a1.stack) == s.with_stack(base + a.stack));
                        lemma_table_pres(lay, m, m1);
                        assert(rel_base(lay, base, a1, m1, nl));
                        lemma_stack_pres(lay, m, m1);
                        assert(m1.rip == m.rip);
                        assert(x64::canonical(m1.rip));
                        lemma_loop_fuel(b, nl, h, offs, cb, lay, cu, base, a1, m1, (f - 1) as nat);
                        assert(Seq::<x64::Instr>::empty() + cb =~= cb);
                        assert(code_len(Seq::<x64::Instr>::empty()) == 0);
                        assert forall|l: int| 0 <= l < offs.len() implies #[trigger] offs[l]
                            + code_len(Seq::<x64::Instr>::empty()) == offs[l] by {}
                        lemma_lift_pre(
                            lay,
                            base,
                            nl,
                            offs,
                            offs,
                            Seq::empty(),
                            cb,
                            cu,
                            m,
                            m1,
                            lir::eval(lay, t@, a1, (f - 1) as nat),
                        );
                    }
                }
            },
            lir::Outcome::Exit(c, vals, s) => {
                lemma_blk_exit(lay, base, a.stack, nl, offs, cb, cu, m, c, vals, s, offs_b);
            },
            _ => {},
        }
    }
}

/// **`loop`.** If the body's code refines the body with the loop's label
/// added at the start of the code, the code refines the `loop`.
pub proof fn lemma_loop(b: Node, nl: nat, h: nat, offs: Seq<int>, cb: Seq<x64::Instr>)
    requires
        cf_refines(b@, nl, h, seq![0int] + offs, cb),
    ensures
        cf_refines(Node::Loop(Box::new(b))@, nl, h, offs, cb),
{
    let t = Node::Loop(Box::new(b));
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, cb, cu, m, lir::eval(lay, t@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, cb) implies cf_post(
        lay,
        base,
        nl,
        offs,
        cb,
        cu,
        m,
        lir::eval(lay, t@, a, fuel),
    ) by {
        lemma_loop_fuel(b, nl, h, offs, cb, lay, cu, base, a, m, fuel);
    }
}

} // verus!
