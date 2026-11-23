//! The soundness of LIR's typing (docs/phases/jit.md item J.5): `tc_sound`.
//!
//! If `tc(lay, ctx, i, stk) == Some(fl)` and the state conforms to `stk` and
//! to the locals' types, then for every amount of fuel, `eval` of `i`:
//!
//! - is never [`Outcome::Stuck`]. So every operand exists and has the right
//!   type, every local index is in range, and every `load` and `store` names
//!   an existing region and an address inside it;
//! - if it falls through (`Normal`), `fl` was `Falls(rs)` and the new state
//!   conforms to `rs` (a `Diverges` instruction never falls through);
//! - if it branches, the label exists and the values it carries conform to
//!   the label's types, so the label's handler is never `Stuck` either;
//! - if it exits, the locals still conform (this is what lets a resume
//!   point trust them).
//!
//! The proof is by induction on the fuel, the same measure `eval` recurses
//! on. `tc_sound` and `lemma_finish` (what happens when a block's body
//! has produced its outcome) call each other.
//!
//! Proof status: everything here is proven, with no assumption and no axiom.

#[allow(unused_imports)]
use super::spec::*;
pub use super::typing::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The state conforms to the context's locals and to the stack types.
pub open spec fn state_ok(lay: Layout, ctx: Ctx, st: St, stk: Seq<Ty>) -> bool {
    vals_conform(lay, st.stack, stk) && vals_conform(lay, st.locals, ctx.locals)
}

/// What the typing promises about an outcome, given the flow it computed.
pub open spec fn outcome_ok(lay: Layout, ctx: Ctx, fl: Flow, o: Outcome) -> bool {
    match o {
        Outcome::Stuck => false,
        Outcome::OutOfFuel => true,
        Outcome::Normal(s) => match fl {
            Flow::Falls(rs) => state_ok(lay, ctx, s, rs),
            Flow::Diverges => false,
        },
        Outcome::Branch(n, s) => n < ctx.labels.len() && vals_conform(lay, s.locals, ctx.locals)
            && s.stack.len() >= ctx.labels[n as int].len() && vals_conform(
            lay,
            top(s.stack, ctx.labels[n as int].len()),
            ctx.labels[n as int],
        ),
        Outcome::Exit(_, _, s) => vals_conform(lay, s.locals, ctx.locals),
    }
}

// ---------------------------------------------------------------------
// Facts about sequences of values and types
// ---------------------------------------------------------------------

proof fn lemma_sub_refl(t: Ty)
    ensures
        ty_sub(t, t),
{
}

/// `stack_sub` (stated by recursion so that it can be evaluated) is `ty_sub`
/// pointwise on sequences of equal length.
pub proof fn lemma_stack_sub_pointwise(a: Seq<Ty>, b: Seq<Ty>)
    ensures
        stack_sub(a, b) <==> (a.len() == b.len() && forall|j: int|
            0 <= j < a.len() ==> ty_sub(#[trigger] a[j], b[j])),
    decreases a.len(),
{
    if a.len() == b.len() && a.len() > 0 {
        let (a0, b0) = (a.drop_last(), b.drop_last());
        lemma_stack_sub_pointwise(a0, b0);
        assert forall|j: int| 0 <= j < a0.len() implies a0[j] == a[j] && b0[j] == b[j] by {}
        if stack_sub(a, b) {
            assert forall|j: int| 0 <= j < a.len() implies ty_sub(#[trigger] a[j], b[j]) by {
                if j < a0.len() {
                    assert(ty_sub(a0[j], b0[j]));
                }
            }
        }
        if forall|j: int| 0 <= j < a.len() ==> ty_sub(#[trigger] a[j], b[j]) {
            assert(ty_sub(a[a.len() - 1], b[b.len() - 1]));
            assert forall|j: int| 0 <= j < a0.len() implies ty_sub(#[trigger] a0[j], b0[j]) by {
                assert(ty_sub(a[j], b[j]));
            }
        }
    }
}

proof fn lemma_stack_sub_refl(s: Seq<Ty>)
    ensures
        stack_sub(s, s),
{
    assert forall|j: int| 0 <= j < s.len() implies ty_sub(#[trigger] s[j], s[j]) by {
        lemma_sub_refl(s[j]);
    }
    lemma_stack_sub_pointwise(s, s);
}

proof fn lemma_conf_sub(lay: Layout, v: Val, t: Ty, u: Ty)
    requires
        conforms(lay, v, t),
        ty_sub(t, u),
    ensures
        conforms(lay, v, u),
{
}

proof fn lemma_vals_sub(lay: Layout, vs: Seq<Val>, ts: Seq<Ty>, us: Seq<Ty>)
    requires
        vals_conform(lay, vs, ts),
        stack_sub(ts, us),
    ensures
        vals_conform(lay, vs, us),
{
    lemma_stack_sub_pointwise(ts, us);
    assert forall|j: int| 0 <= j < vs.len() implies conforms(lay, #[trigger] vs[j], us[j]) by {
        lemma_conf_sub(lay, vs[j], ts[j], us[j]);
    }
}

proof fn lemma_vals_push(lay: Layout, vs: Seq<Val>, ts: Seq<Ty>, v: Val, t: Ty)
    requires
        vals_conform(lay, vs, ts),
        conforms(lay, v, t),
    ensures
        vals_conform(lay, vs.push(v), ts.push(t)),
{
    assert forall|j: int| 0 <= j < vs.push(v).len() implies conforms(
        lay,
        #[trigger] vs.push(v)[j],
        ts.push(t)[j],
    ) by {
        if j < vs.len() {
            assert(vs.push(v)[j] == vs[j]);
            assert(ts.push(t)[j] == ts[j]);
        } else {
            assert(vs.push(v)[j] == v);
            assert(ts.push(t)[j] == t);
        }
    }
}

proof fn lemma_vals_below_top(lay: Layout, vs: Seq<Val>, ts: Seq<Ty>, k: nat)
    requires
        vals_conform(lay, vs, ts),
        k <= vs.len(),
    ensures
        vals_conform(lay, below(vs, k), below(ts, k)),
        vals_conform(lay, top(vs, k), top(ts, k)),
{
    assert forall|j: int| 0 <= j < below(vs, k).len() implies conforms(
        lay,
        #[trigger] below(vs, k)[j],
        below(ts, k)[j],
    ) by {
        assert(below(vs, k)[j] == vs[j]);
        assert(below(ts, k)[j] == ts[j]);
    }
    assert forall|j: int| 0 <= j < top(vs, k).len() implies conforms(
        lay,
        #[trigger] top(vs, k)[j],
        top(ts, k)[j],
    ) by {
        assert(top(vs, k)[j] == vs[vs.len() - k + j]);
        assert(top(ts, k)[j] == ts[vs.len() - k + j]);
    }
}

proof fn lemma_vals_concat(lay: Layout, a: Seq<Val>, x: Seq<Ty>, b: Seq<Val>, y: Seq<Ty>)
    requires
        vals_conform(lay, a, x),
        vals_conform(lay, b, y),
    ensures
        vals_conform(lay, a + b, x + y),
{
    assert forall|j: int| 0 <= j < (a + b).len() implies conforms(
        lay,
        #[trigger] (a + b)[j],
        (x + y)[j],
    ) by {
        if j < a.len() {
            assert((a + b)[j] == a[j]);
            assert((x + y)[j] == x[j]);
        } else {
            assert((a + b)[j] == b[j - a.len()]);
            assert((x + y)[j] == y[j - a.len()]);
        }
    }
}

/// The top values of a conforming stack conform to the types the stack's
/// top types are subtypes of.
proof fn lemma_top_conform(lay: Layout, vs: Seq<Val>, stk: Seq<Ty>, tys: Seq<Ty>)
    requires
        vals_conform(lay, vs, stk),
        top_sub(stk, tys),
    ensures
        vs.len() >= tys.len(),
        vals_conform(lay, top(vs, tys.len()), tys),
{
    lemma_vals_below_top(lay, vs, stk, tys.len());
    lemma_vals_sub(lay, top(vs, tys.len()), top(stk, tys.len()), tys);
}

/// Popping one element with `below` is `drop_last`.
proof fn lemma_below1<A>(s: Seq<A>)
    requires
        s.len() >= 1,
    ensures
        below(s, 1) == s.drop_last(),
{
    assert(below(s, 1) =~= s.drop_last());
}

/// A sequence is its `below(.., k)` followed by its `top(.., k)`.
proof fn lemma_split<A>(s: Seq<A>, k: nat)
    requires
        k <= s.len(),
    ensures
        below(s, k) + top(s, k) == s,
{
    assert(below(s, k) + top(s, k) =~= s);
}

// ---------------------------------------------------------------------
// Numeric operators
// ---------------------------------------------------------------------

proof fn lemma_bin_sound(lay: Layout, op: BinOp, a: Val, b: Val, ta: Ty, tb: Ty)
    requires
        conforms(lay, a, ta),
        conforms(lay, b, tb),
        ty_sub(ta, bin_arg(op)),
        ty_sub(tb, bin_arg(op)),
    ensures
        bin_eval(op, a, b) is Some,
        conforms(lay, bin_eval(op, a, b).unwrap(), bin_res(op)),
{
    lemma_conf_sub(lay, a, ta, bin_arg(op));
    lemma_conf_sub(lay, b, tb, bin_arg(op));
}

proof fn lemma_un_sound(lay: Layout, op: UnOp, a: Val, ta: Ty)
    requires
        conforms(lay, a, ta),
        ty_sub(ta, un_arg(op)),
    ensures
        un_eval(op, a) is Some,
        conforms(lay, un_eval(op, a).unwrap(), un_res(op)),
{
    lemma_conf_sub(lay, a, ta, un_arg(op));
}

// ---------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------

/// Whatever `tc_blk` accepts, it types as `below(stk, k) + results`.
proof fn lemma_blk_form(
    lay: Layout,
    ctx: Ctx,
    bt: BlockType,
    body: Instr,
    stk: Seq<Ty>,
    is_loop: bool,
    fl: Flow,
)
    requires
        tc_blk(lay, ctx, bt, body, stk, is_loop) == Some(fl),
    ensures
        fl == Flow::Falls(below(stk, bt.params.len()) + bt.results),
        top_sub(stk, bt.params),
{
}

/// The label context inside a block's body.
pub open spec fn body_ctx(ctx: Ctx, bt: BlockType, is_loop: bool) -> Ctx {
    Ctx {
        locals: ctx.locals,
        labels: seq![if is_loop {
            bt.params
        } else {
            bt.results
        }] + ctx.labels,
    }
}

/// The body's typing, if the block's is `Some`: there is a flow `fb` for it,
/// with a `Falls` having a stack that is a subtype of the results.
proof fn lemma_blk_body(
    lay: Layout,
    ctx: Ctx,
    bt: BlockType,
    body: Instr,
    stk: Seq<Ty>,
    is_loop: bool,
    fl: Flow,
) -> (fb: Flow)
    requires
        tc_blk(lay, ctx, bt, body, stk, is_loop) == Some(fl),
    ensures
        tc(lay, body_ctx(ctx, bt, is_loop), body, bt.params) == Some(fb),
        match fb {
            Flow::Falls(s) => stack_sub(s, bt.results),
            Flow::Diverges => true,
        },
{
    let ctx2 = body_ctx(ctx, bt, is_loop);
    match tc(lay, ctx2, body, bt.params) {
        Some(fb) => fb,
        None => {
            assert(false);
            Flow::Diverges
        },
    }
}

/// The block's body produced the outcome `o` (which conforms to the body's
/// typing); the block-like instruction then finishes. This is `finish_label`
/// of `eval`, for the `block` (`is_loop` false) and the `loop`.
proof fn lemma_finish(
    lay: Layout,
    ctx: Ctx,
    bt: BlockType,
    body: Instr,
    is_loop: bool,
    stk: Seq<Ty>,
    st: St,
    fb: Flow,
    o: Outcome,
    fuel: nat,
    fl: Flow,
)
    requires
        tc_blk(lay, ctx, bt, body, stk, is_loop) == Some(fl),
        state_ok(lay, ctx, st, stk),
        tc(lay, body_ctx(ctx, bt, is_loop), body, bt.params) == Some(fb),
        match fb {
            Flow::Falls(s) => stack_sub(s, bt.results),
            Flow::Diverges => true,
        },
        outcome_ok(lay, body_ctx(ctx, bt, is_loop), fb, o),
    ensures
        outcome_ok(
            lay,
            ctx,
            fl,
            finish_label(
                lay,
                below(st.stack, bt.params.len()),
                if is_loop {
                    bt.params.len()
                } else {
                    bt.results.len()
                },
                if is_loop {
                    Some(Instr::Loop(bt, Box::new(body)))
                } else {
                    None
                },
                o,
                fuel,
            ),
        ),
    decreases fuel, 0nat,
{
    let k = bt.params.len();
    let ctx2 = body_ctx(ctx, bt, is_loop);
    lemma_blk_form(lay, ctx, bt, body, stk, is_loop, fl);
    lemma_vals_below_top(lay, st.stack, stk, k);
    let lbl = if is_loop {
        bt.params
    } else {
        bt.results
    };
    assert(ctx2.labels[0] == lbl);
    match o {
        Outcome::Normal(s) => {
            // The body fell through, so its flow was `Falls(s_ty)`.
            match fb {
                Flow::Falls(sty) => {
                    lemma_vals_sub(lay, s.stack, sty, bt.results);
                    lemma_vals_concat(
                        lay,
                        below(st.stack, k),
                        below(stk, k),
                        s.stack,
                        bt.results,
                    );
                },
                Flow::Diverges => {},
            }
        },
        Outcome::Branch(n, s) => {
            if n > 0 {
                assert(ctx2.labels[n as int] == ctx.labels[n - 1]);
            } else {
                // The label is this block: it carries `lbl.len()` values.
                assert(ctx2.labels[0].len() == lbl.len());
                lemma_vals_concat(
                    lay,
                    below(st.stack, k),
                    below(stk, k),
                    top(s.stack, lbl.len()),
                    lbl,
                );
                if is_loop {
                    // Branching to a loop restarts it, in the stack
                    // `below(stk, k) + params`.
                    if fuel > 0 {
                        let stk2 = below(stk, k) + bt.params;
                        let carried = below(st.stack, k) + top(s.stack, k);
                        let st2 = s.with_stack(carried);
                        assert(below(stk2, k) =~= below(stk, k));
                        assert(top(stk2, k) =~= bt.params);
                        lemma_stack_sub_refl(bt.params);
                        assert(top_sub(stk2, bt.params));
                        assert(tc_blk(lay, ctx, bt, body, stk2, true) == tc_blk(
                            lay,
                            ctx,
                            bt,
                            body,
                            stk,
                            true,
                        ));
                        assert(state_ok(lay, ctx, st2, stk2));
                        tc_sound(
                            lay,
                            ctx,
                            Instr::Loop(bt, Box::new(body)),
                            stk2,
                            st2,
                            (fuel - 1) as nat,
                            fl,
                        );
                    }
                }
            }
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------

/// **A whole function.** The body type-checks with the single label
/// `results` (the return), and either diverges or falls through to a stack
/// that is a subtype of `results`. Then `run` of it, from a conforming state,
/// is never stuck, and if it returns (falls through or branches to the
/// return) the top values conform to the results.
pub proof fn run_sound(
    lay: Layout,
    locals: Seq<Ty>,
    results: Seq<Ty>,
    body: Instr,
    params: Seq<Ty>,
    st: St,
    fuel: nat,
    fl: Flow,
)
    requires
        tc(lay, Ctx { locals: locals, labels: seq![results] }, body, params) == Some(fl),
        match fl {
            Flow::Falls(rs) => stack_sub(rs, results),
            Flow::Diverges => true,
        },
        state_ok(lay, Ctx { locals: locals, labels: seq![results] }, st, params),
    ensures
        !(run(lay, body, st, fuel) is Stuck),
        match run(lay, body, st, fuel) {
            Outcome::Normal(s) => s.stack.len() >= results.len() && vals_conform(
                lay,
                top(s.stack, results.len()),
                results,
            ),
            _ => true,
        },
{
    let ctx = Ctx { locals: locals, labels: seq![results] };
    tc_sound(lay, ctx, body, params, st, fuel, fl);
    match eval(lay, body, st, fuel) {
        Outcome::Normal(s) => {
            match fl {
                Flow::Falls(rs) => {
                    lemma_vals_sub(lay, s.stack, rs, results);
                    assert(top(s.stack, results.len()) =~= s.stack);
                },
                Flow::Diverges => {},
            }
        },
        _ => {},
    }
}

/// **Soundness of the typing.**A well-typed instruction, started in a
/// conforming state, with any amount of fuel, is never stuck and does what
/// its typing says (see the module docs and [`outcome_ok`]).
pub proof fn tc_sound(lay: Layout, ctx: Ctx, i: Instr, stk: Seq<Ty>, st: St, fuel: nat, fl: Flow)
    requires
        tc(lay, ctx, i, stk) == Some(fl),
        state_ok(lay, ctx, st, stk),
    ensures
        outcome_ok(lay, ctx, fl, eval(lay, i, st, fuel)),
    decreases fuel, 1nat,
{
    if fuel == 0 {
        return ;
    }
    let f = (fuel - 1) as nat;
    let n = st.stack.len();
    assert(n == stk.len());
    match i {
        Instr::Nop => {},
        Instr::Then(a, b) => {
            match tc(lay, ctx, *a, stk) {
                Some(Flow::Falls(s1)) => {
                    tc_sound(lay, ctx, *a, stk, st, f, Flow::Falls(s1));
                    match eval(lay, *a, st, f) {
                        Outcome::Normal(s2) => {
                            tc_sound(lay, ctx, *b, s1, s2, f, fl);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        Instr::Const(v) => {
            lemma_vals_push(lay, st.stack, stk, v, val_ty(v));
        },
        Instr::LocalGet(x) => {
            assert(conforms(lay, st.locals[x as int], ctx.locals[x as int]));
            lemma_vals_push(lay, st.stack, stk, st.locals[x as int], ctx.locals[x as int]);
        },
        Instr::LocalSet(x) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], ctx.locals[x as int]);
            lemma_vals_below_top(lay, st.stack, stk, 1);
            lemma_below1(st.stack);
            lemma_below1(stk);
            let nl = st.locals.update(x as int, st.stack.last());
            assert forall|j: int| 0 <= j < nl.len() implies conforms(
                lay,
                #[trigger] nl[j],
                ctx.locals[j],
            ) by {
                if j == x as int {
                } else {
                    assert(nl[j] == st.locals[j]);
                }
            }
        },
        Instr::LocalTee(x) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], ctx.locals[x as int]);
            let nl = st.locals.update(x as int, st.stack.last());
            assert forall|j: int| 0 <= j < nl.len() implies conforms(
                lay,
                #[trigger] nl[j],
                ctx.locals[j],
            ) by {
                if j == x as int {
                } else {
                    assert(nl[j] == st.locals[j]);
                }
            }
        },
        Instr::Drop => {
            lemma_vals_below_top(lay, st.stack, stk, 1);
            lemma_below1(st.stack);
            lemma_below1(stk);
        },
        Instr::Select => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            assert(conforms(lay, st.stack[n - 2], stk[n - 2]));
            assert(conforms(lay, st.stack[n - 3], stk[n - 3]));
            lemma_vals_below_top(lay, st.stack, stk, 3);
            match st.stack[n - 1] {
                Val::I32(c) => {
                    let v = if c != 0 {
                        st.stack[n - 3]
                    } else {
                        st.stack[n - 2]
                    };
                    assert(conforms(lay, v, stk[n - 3]));
                    lemma_vals_push(lay, below(st.stack, 3), below(stk, 3), v, stk[n - 3]);
                },
                _ => {},
            }
        },
        Instr::Bin(op) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            assert(conforms(lay, st.stack[n - 2], stk[n - 2]));
            lemma_bin_sound(lay, op, st.stack[n - 2], st.stack[n - 1], stk[n - 2], stk[n - 1]);
            lemma_vals_below_top(lay, st.stack, stk, 2);
            lemma_vals_push(
                lay,
                below(st.stack, 2),
                below(stk, 2),
                bin_eval(op, st.stack[n - 2], st.stack[n - 1]).unwrap(),
                bin_res(op),
            );
        },
        Instr::Un(op) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_un_sound(lay, op, st.stack[n - 1], stk[n - 1]);
            lemma_vals_below_top(lay, st.stack, stk, 1);
            lemma_vals_push(
                lay,
                below(st.stack, 1),
                below(stk, 1),
                un_eval(op, st.stack[n - 1]).unwrap(),
                un_res(op),
            );
        },
        Instr::BoundsCheck { region, size, code } => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], Ty::I64);
            lemma_vals_below_top(lay, st.stack, stk, 1);
            match st.stack[n - 1] {
                Val::I64(ix) => {
                    if ix as nat + size <= lay[region as int].bound {
                        assert(st.stack =~= below(st.stack, 1).push(st.stack[n - 1]));
                        lemma_vals_push(
                            lay,
                            below(st.stack, 1),
                            below(stk, 1),
                            st.stack[n - 1],
                            Ty::Idx(region, size),
                        );
                    }
                },
                _ => {},
            }
        },
        Instr::Load { region, ty } => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], Ty::Idx(region, ty_size(ty)));
            lemma_vals_below_top(lay, st.stack, stk, 1);
            match st.stack[n - 1] {
                Val::I64(ix) => {
                    let r = lay[region as int];
                    assert(ix as nat + ty_size(ty) <= r.bound);
                    let v = val_of_bits(ty, read_le(st.mem, r.base + masked(r.bound, ix as nat), ty_size(ty)));
                    assert(conforms(lay, v, ty));
                    lemma_vals_push(lay, below(st.stack, 1), below(stk, 1), v, ty);
                },
                _ => {},
            }
        },
        Instr::Store { region, ty } => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            assert(conforms(lay, st.stack[n - 2], stk[n - 2]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], ty);
            lemma_conf_sub(lay, st.stack[n - 2], stk[n - 2], Ty::Idx(region, ty_size(ty)));
            lemma_vals_below_top(lay, st.stack, stk, 2);
            match st.stack[n - 2] {
                Val::I64(ix) => {
                    let r = lay[region as int];
                    assert(ix as nat + ty_size(ty) <= r.bound);
                },
                _ => {},
            }
        },
        Instr::Block(bt, body) => {
            let k = bt.params.len();
            let fb = lemma_blk_body(lay, ctx, bt, *body, stk, false, fl);
            lemma_blk_form(lay, ctx, bt, *body, stk, false, fl);
            lemma_top_conform(lay, st.stack, stk, bt.params);
            let sb = st.with_stack(top(st.stack, k));
            tc_sound(lay, body_ctx(ctx, bt, false), *body, bt.params, sb, f, fb);
            lemma_finish(
                lay,
                ctx,
                bt,
                *body,
                false,
                stk,
                st,
                fb,
                eval(lay, *body, sb, f),
                f,
                fl,
            );
        },
        Instr::Loop(bt, body) => {
            let k = bt.params.len();
            let fb = lemma_blk_body(lay, ctx, bt, *body, stk, true, fl);
            lemma_blk_form(lay, ctx, bt, *body, stk, true, fl);
            lemma_top_conform(lay, st.stack, stk, bt.params);
            let sb = st.with_stack(top(st.stack, k));
            tc_sound(lay, body_ctx(ctx, bt, true), *body, bt.params, sb, f, fb);
            lemma_finish(lay, ctx, bt, *body, true, stk, st, fb, eval(lay, *body, sb, f), f, fl);
        },
        Instr::If(bt, t, e) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], Ty::I32);
            lemma_vals_below_top(lay, st.stack, stk, 1);
            lemma_below1(st.stack);
            lemma_below1(stk);
            let stk1 = stk.drop_last();
            let st1 = st.with_stack(below(st.stack, 1));
            match st.stack[n - 1] {
                Val::I32(c) => {
                    let chosen = if c != 0 {
                        t
                    } else {
                        e
                    };
                    if let (Some(f1), Some(f2)) = (
                        tc_blk(lay, ctx, bt, *t, stk1, false),
                        tc_blk(lay, ctx, bt, *e, stk1, false),
                    ) {
                        lemma_blk_form(lay, ctx, bt, *t, stk1, false, f1);
                        lemma_blk_form(lay, ctx, bt, *e, stk1, false, f2);
                        tc_sound(lay, ctx, Instr::Block(bt, chosen), stk1, st1, f, fl);
                    }
                },
                _ => {},
            }
        },
        Instr::Br(l) => {
            lemma_top_conform(lay, st.stack, stk, ctx.labels[l as int]);
        },
        Instr::BrIf(l) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], Ty::I32);
            lemma_vals_below_top(lay, st.stack, stk, 1);
            lemma_below1(st.stack);
            lemma_below1(stk);
            lemma_top_conform(lay, below(st.stack, 1), below(stk, 1), ctx.labels[l as int]);
        },
        Instr::BrTable(ls, d) => {
            assert(conforms(lay, st.stack[n - 1], stk[n - 1]));
            lemma_conf_sub(lay, st.stack[n - 1], stk[n - 1], Ty::I32);
            lemma_vals_below_top(lay, st.stack, stk, 1);
            lemma_below1(st.stack);
            lemma_below1(stk);
            match st.stack[n - 1] {
                Val::I32(c) => {
                    if (c as nat) < ls.len() {
                        lemma_top_conform(
                            lay,
                            below(st.stack, 1),
                            below(stk, 1),
                            ctx.labels[ls[c as int] as int],
                        );
                    } else {
                        lemma_top_conform(
                            lay,
                            below(st.stack, 1),
                            below(stk, 1),
                            ctx.labels[d as int],
                        );
                    }
                },
                _ => {},
            }
        },
        Instr::Exit(code, tys) => {
            lemma_top_conform(lay, st.stack, stk, tys);
        },
    }
}

} // verus!
