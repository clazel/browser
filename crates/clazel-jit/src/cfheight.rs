//! The static analysis [`cf_flow`] is sound for LIR's evaluation: where
//! it says an instruction falls through at height `h1`, a `Normal` outcome is a
//! stack of that height; where it says `Dead`, there is no `Normal` outcome.
//! Heights are counted from `hb`, the number of values below the instruction's
//! own (fresh) stack, which is what [`crate::cfspec::rel_base`]'s `base` holds.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A straight-line instruction changes the height as `pops` and `pushes`
/// say, counted from `hb`.
pub proof fn lemma_op_height_off(
    op: Op,
    nl: nat,
    h: nat,
    hb: nat,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    fuel: nat,
)
    requires
        op_ok(op, nl, h),
        hb + a.stack.len() == h,
        lir::eval(lay, op@, a, fuel) == lir::Outcome::Normal(a2),
    ensures
        hb + a2.stack.len() == height_after_op(op, h),
{
    assert(fuel > 0);
    let n = a.stack.len();
    match op {
        Op::Nop => {},
        Op::Drop => {},
        Op::Const(v) => {},
        Op::LocalGet(x) => {},
        Op::LocalSet(x) => {},
        Op::LocalTee(x) => {},
        Op::Select => {
            match a.stack[n - 1] {
                lir::Val::I32(c) => {
                    assert(a2.stack.len() == (n - 3) + 1);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Op::Bin(b) => {
            match lir::bin_eval(b, a.stack[n - 2], a.stack[n - 1]) {
                Some(v) => {
                    assert(a2.stack.len() == (n - 2) + 1);
                },
                None => {
                    assert(false);
                },
            }
        },
        Op::Un(u) => {
            match lir::un_eval(u, a.stack[n - 1]) {
                Some(v) => {
                    assert(a2.stack.len() == (n - 1) + 1);
                },
                None => {
                    assert(false);
                },
            }
        },
    }
}

/// An instruction the analysis calls [`Flow::Dead`] never has a `Normal`
/// outcome: it branches, exits, or is stuck.
pub proof fn lemma_dead_not_normal(
    n: Node,
    nl: nat,
    h: nat,
    depth: nat,
    lay: lir::Layout,
    a: lir::St,
    fuel: nat,
)
    requires
        cf_flow(n, nl, h, depth) == Some(Flow::Dead),
    ensures
        !(lir::eval(lay, n@, a, fuel) is Normal),
    decreases n,
{
    match n {
        Node::Then(x, y) => {
            if fuel > 0 {
                let f = (fuel - 1) as nat;
                match cf_flow(*x, nl, h, depth) {
                    Some(Flow::Falls(h1)) => {
                        match lir::eval(lay, (*x)@, a, f) {
                            lir::Outcome::Normal(a1) => {
                                lemma_dead_not_normal(*y, nl, h1, depth, lay, a1, f);
                            },
                            _ => {},
                        }
                    },
                    Some(Flow::Dead) => {
                        lemma_dead_not_normal(*x, nl, h, depth, lay, a, f);
                    },
                    None => {},
                }
            }
        },
        _ => {},
    }
}

/// The stack a block or loop body runs on: empty (a void block has no
/// parameters).
pub open spec fn fresh(a: lir::St) -> lir::St {
    a.with_stack(seq![])
}

/// What `eval` makes of a `block` (`restart == None`) or `loop`
/// (`restart == Some(it)`) with void type, in terms of its body's outcome.
pub open spec fn label_out(
    lay: lir::Layout,
    body: Node,
    st: lir::St,
    restart: Option<lir::Instr>,
    f: nat,
) -> lir::Outcome {
    lir::finish_label(lay, st.stack, 0, restart, lir::eval(lay, body@, fresh(st), f), f)
}

/// `eval` of a void `block` is [`label_out`].
pub proof fn lemma_eval_block(lay: lir::Layout, body: Node, st: lir::St, fuel: nat)
    requires
        fuel > 0,
    ensures
        lir::eval(lay, lir::Instr::Block(void_bt(), Box::new(body@)), st, fuel) == label_out(
            lay,
            body,
            st,
            None,
            (fuel - 1) as nat,
        ),
{
    assert(lir::below(st.stack, 0) =~= st.stack);
    assert(lir::top(st.stack, 0) =~= seq![]);
    assert(st.with_stack(lir::top(st.stack, 0)) == fresh(st));
}

/// `eval` of a void `loop` is [`label_out`], restarting the loop.
pub proof fn lemma_eval_loop(lay: lir::Layout, body: Node, st: lir::St, fuel: nat)
    requires
        fuel > 0,
    ensures
        lir::eval(lay, lir::Instr::Loop(void_bt(), Box::new(body@)), st, fuel) == label_out(
            lay,
            body,
            st,
            Some(lir::Instr::Loop(void_bt(), Box::new(body@))),
            (fuel - 1) as nat,
        ),
{
    assert(lir::below(st.stack, 0) =~= st.stack);
    assert(lir::top(st.stack, 0) =~= seq![]);
    assert(st.with_stack(lir::top(st.stack, 0)) == fresh(st));
}

/// The body of a block or loop is well formed: its analysis, entered at height
/// `hh` one label deeper, falls through at `hh` or is dead.
pub open spec fn body_fits(body: Node, nl: nat, hh: nat, depth: nat) -> bool {
    match cf_flow(body, nl, hh, depth + 1) {
        Some(fl) => flow_fits(fl, hh),
        None => false,
    }
}

/// **The static heights are right.** If the analysis says `n` falls through
/// at height `h1` when entered at `h`, and the stack has `hb` values under
/// `n`'s own, then a `Normal` outcome's stack has `h1 - hb` values.
#[verifier::rlimit(200)]
pub proof fn lemma_cf_height(
    n: Node,
    nl: nat,
    h: nat,
    depth: nat,
    h1: nat,
    hb: nat,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    fuel: nat,
)
    requires
        cf_flow(n, nl, h, depth) == Some(Flow::Falls(h1)),
        hb + a.stack.len() == h,
        lir::eval(lay, n@, a, fuel) == lir::Outcome::Normal(a2),
    ensures
        hb + a2.stack.len() == h1,
    decreases fuel, 2nat,
{
    assert(fuel > 0);
    let f = (fuel - 1) as nat;
    match n {
        Node::Op(o) => {
            lemma_op_height_off(o, nl, h, hb, lay, a, a2, fuel);
        },
        Node::Mem(m) => {
            let k = a.stack.len();
            match m {
                MemOp::BoundsCheck { region, size, code } => {
                    assert(a2 == a);
                },
                MemOp::Load { region, ty } => {
                    assert(a2.stack.len() == k);
                },
                MemOp::Store { region, ty } => {
                    assert(a2.stack.len() == k - 2);
                },
            }
        },
        Node::Then(x, y) => {
            match cf_flow(*x, nl, h, depth) {
                Some(Flow::Falls(hx)) => {
                    match lir::eval(lay, (*x)@, a, f) {
                        lir::Outcome::Normal(a1) => {
                            lemma_cf_height(*x, nl, h, depth, hx, hb, lay, a, a1, f);
                            lemma_cf_height(*y, nl, hx, depth, h1, hb, lay, a1, a2, f);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        Node::Block(b) => {
            lemma_eval_block(lay, *b, a, fuel);
            lemma_label_height(*b, nl, h, depth, hb, lay, a, a2, f, false);
        },
        Node::Loop(b) => {
            lemma_eval_loop(lay, *b, a, fuel);
            lemma_label_height(*b, nl, h, depth, hb, lay, a, a2, f, true);
        },
        Node::If(t, e) => {
            let k = a.stack.len();
            match a.stack[k - 1 as int] {
                lir::Val::I32(c) => {
                    let a0 = a.with_stack(lir::below(a.stack, 1));
                    let arm = if c != 0 { *t } else { *e };
                    assert(k >= 1);
                    assert(f > 0) by {
                        if f == 0 {
                            assert(lir::eval(lay, lir::Instr::Block(void_bt(), Box::new(arm@)), a0, 0)
                                == lir::Outcome::OutOfFuel);
                        }
                    }
                    lemma_eval_block(lay, arm, a0, f);
                    lemma_label_height(arm, nl, (h - 1) as nat, depth, hb, lay, a0, a2, (f - 1) as nat, false);
                },
                _ => {},
            }
        },
        Node::BrIf(l) => {
            let k = a.stack.len();
            match a.stack[k - 1 as int] {
                lir::Val::I32(c) => {},
                _ => {},
            }
        },
        _ => {},
    }
}

/// The body of a block or loop leaves the stack as it found it, or branches
/// to the label (which truncates it to what was below): a `Normal` outcome of
/// [`label_out`] has the height `hh`, counted from `hb`.
#[verifier::rlimit(200)]
pub proof fn lemma_label_height(
    body: Node,
    nl: nat,
    hh: nat,
    depth: nat,
    hb: nat,
    lay: lir::Layout,
    st: lir::St,
    a2: lir::St,
    f: nat,
    is_loop: bool,
)
    requires
        body_fits(body, nl, hh, depth),
        hb + st.stack.len() == hh,
        label_out(
            lay,
            body,
            st,
            if is_loop {
                Some(lir::Instr::Loop(void_bt(), Box::new(body@)))
            } else {
                None
            },
            f,
        ) == lir::Outcome::Normal(a2),
    ensures
        hb + a2.stack.len() == hh,
    decreases f + 1, 1nat,
{
    let restart = if is_loop {
        Some(lir::Instr::Loop(void_bt(), Box::new(body@)))
    } else {
        None
    };
    match lir::eval(lay, body@, fresh(st), f) {
        lir::Outcome::Normal(s) => {
            match cf_flow(body, nl, hh, depth + 1) {
                Some(Flow::Falls(hb1)) => {
                    lemma_cf_height(body, nl, hh, depth + 1, hb1, hh, lay, fresh(st), s, f);
                    assert(s.stack.len() == 0);
                    assert(a2.stack =~= st.stack + s.stack);
                },
                Some(Flow::Dead) => {
                    lemma_dead_not_normal(body, nl, hh, depth + 1, lay, fresh(st), f);
                },
                None => {},
            }
        },
        lir::Outcome::Branch(m, s) => {
            if m == 0 {
                assert(lir::top(s.stack, 0) =~= seq![]);
                let carried = st.stack + lir::top(s.stack, 0);
                assert(carried =~= st.stack);
                match restart {
                    None => {
                        assert(a2.stack =~= st.stack);
                    },
                    Some(i) => {
                        if f > 0 {
                            let st1 = s.with_stack(carried);
                            assert(lir::eval(lay, i, st1, (f - 1) as nat) == lir::Outcome::Normal(a2));
                            lemma_cf_height(
                                Node::Loop(Box::new(body)),
                                nl,
                                hh,
                                depth,
                                hh,
                                hb,
                                lay,
                                st1,
                                a2,
                                (f - 1) as nat,
                            );
                        }
                    },
                }
            }
        },
        _ => {},
    }
}

} // verus!
