//! LIR's typing judgment and its soundness theorem (docs/phases/jit.md item
//! J.5).
//!
//! The judgment is `tc`: given the layout, a context (the types of the
//! locals and of the enclosing labels) and the types of the operand stack,
//! it says whether an instruction is well-typed and what it leaves on the
//! stack. It is Wasm core 2.0 §3.3 "Instructions" (validation), written as
//! a checking function in the style of the algorithm of Appendix A
//! "Validation Algorithm", with three differences:
//!
//! 1. **No stack-polymorphic dead code.** Wasm types the code after `br`,
//!    `br_table`, `return` and `unreachable` at any stack (§3.3.8,
//!    `[t1* t*] -> [t2*]`). LIR instead requires the instruction that never
//!    falls through ([`Flow::Diverges`]: `br`, `br_table`, `exit`) to be the
//!    last of its sequence, and rejects anything after it. A front end drops
//!    the dead code; the typing is then monomorphic, which is what the
//!    back ends' templates want.
//! 2. **`Idx` types** (see [`Ty`]): the only way to type a `load` or
//!    `store`. This is what makes "every access is inside its region" a
//!    type-level fact.
//! 3. **No function, table, global or reference instructions**; one body,
//!    with label 0 as its return (see `spec`).
//!
//! The soundness theorem, `soundness::tc_sound`, is proven in
//! [`crate::soundness`]: a well-typed instruction, started in a state that
//! conforms to its input types, is never [`Outcome::Stuck`] (so every load
//! and store is inside its region, every operand exists and has the right
//! type), and whatever it does conforms to what the typing said.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Subtyping and conformance
// ---------------------------------------------------------------------

/// `a` may be used where `b` is expected. `Idx(r, n)` is an `i64`, and it
/// is an `Idx(r, m)` for any smaller `m`; otherwise only equal types match.
pub open spec fn ty_sub(a: Ty, b: Ty) -> bool {
    match (a, b) {
        (Ty::Idx(r, n), Ty::Idx(s, m)) => r == s && m <= n,
        (Ty::Idx(_, _), Ty::I64) => true,
        _ => a == b,
    }
}

/// `sub` pointwise, on sequences of equal length.
pub open spec fn stack_sub(a: Seq<Ty>, b: Seq<Ty>) -> bool {
    a.len() == b.len() && forall|j: int| 0 <= j < a.len() ==> ty_sub(#[trigger] a[j], b[j])
}

/// The top `tys.len()` types of `stk` are subtypes of `tys`.
pub open spec fn top_sub(stk: Seq<Ty>, tys: Seq<Ty>) -> bool {
    stk.len() >= tys.len() && stack_sub(top(stk, tys.len()), tys)
}

/// The value `v` has type `t` under the layout `lay`: its shape matches, and
/// for `Idx(r, n)` it is an index of `r` with room for `n` bytes.
pub open spec fn conforms(lay: Layout, v: Val, t: Ty) -> bool {
    match (v, t) {
        (Val::I32(_), Ty::I32) => true,
        (Val::I64(_), Ty::I64) => true,
        (Val::F64(_), Ty::F64) => true,
        (Val::I64(i), Ty::Idx(r, n)) => r < lay.len() && i as nat + n <= lay[r as int].bound,
        _ => false,
    }
}

/// The values conform to the types, pointwise.
pub open spec fn vals_conform(lay: Layout, vs: Seq<Val>, ts: Seq<Ty>) -> bool {
    vs.len() == ts.len() && forall|j: int| 0 <= j < vs.len() ==> conforms(lay, #[trigger] vs[j], ts[j])
}

/// The type of a constant.
pub open spec fn val_ty(v: Val) -> Ty {
    match v {
        Val::I32(_) => Ty::I32,
        Val::I64(_) => Ty::I64,
        Val::F64(_) => Ty::F64,
    }
}

// ---------------------------------------------------------------------
// Numeric operator signatures (Wasm core §3.3.1 "Numeric Instructions")
// ---------------------------------------------------------------------

/// The type of both operands of a binary operator.
pub open spec fn bin_arg(op: BinOp) -> Ty {
    match op {
        BinOp::I32(_) | BinOp::I32Cmp(_) => Ty::I32,
        BinOp::I64(_) | BinOp::I64Cmp(_) => Ty::I64,
        BinOp::F64(_) | BinOp::F64Cmp(_) => Ty::F64,
    }
}

/// The result type of a binary operator (comparisons give `i32`).
pub open spec fn bin_res(op: BinOp) -> Ty {
    match op {
        BinOp::I32(_) => Ty::I32,
        BinOp::I64(_) => Ty::I64,
        BinOp::F64(_) => Ty::F64,
        BinOp::I32Cmp(_) | BinOp::I64Cmp(_) | BinOp::F64Cmp(_) => Ty::I32,
    }
}

/// The operand type of a unary operator.
pub open spec fn un_arg(op: UnOp) -> Ty {
    match op {
        UnOp::I32Eqz | UnOp::I64ExtendI32S | UnOp::I64ExtendI32U | UnOp::F64ConvertI32S
        | UnOp::F64ConvertI32U => Ty::I32,
        UnOp::I64Eqz | UnOp::I32WrapI64 | UnOp::F64ConvertI64S | UnOp::F64ConvertI64U
        | UnOp::F64ReinterpretI64 => Ty::I64,
        UnOp::F64Neg | UnOp::F64Abs | UnOp::F64Sqrt | UnOp::I64ReinterpretF64 => Ty::F64,
    }
}

/// The result type of a unary operator.
pub open spec fn un_res(op: UnOp) -> Ty {
    match op {
        UnOp::I32Eqz | UnOp::I64Eqz | UnOp::I32WrapI64 => Ty::I32,
        UnOp::I64ExtendI32S | UnOp::I64ExtendI32U | UnOp::I64ReinterpretF64 => Ty::I64,
        UnOp::F64Neg | UnOp::F64Abs | UnOp::F64Sqrt | UnOp::F64ConvertI32S
        | UnOp::F64ConvertI32U | UnOp::F64ConvertI64S | UnOp::F64ConvertI64U
        | UnOp::F64ReinterpretI64 => Ty::F64,
    }
}

// ---------------------------------------------------------------------
// The typing judgment
// ---------------------------------------------------------------------

/// What an instruction's typing context holds.
pub struct Ctx {
    /// The types of the locals.
    pub locals: Seq<Ty>,
    /// The types a branch to each enclosing label carries; index 0 is the
    /// innermost label, and the last is the function's return.
    pub labels: Seq<Seq<Ty>>,
}

/// What a well-typed instruction does to the stack.
pub enum Flow {
    /// It can fall through, leaving a stack of these types.
    Falls(Seq<Ty>),
    /// It never falls through (it branches or exits), so it must end its
    /// sequence.
    Diverges,
}

/// The number of nodes of an instruction, the measure of `tc`.
pub open spec fn isize(i: Instr) -> nat
    decreases i,
{
    match i {
        Instr::Then(a, b) => 1 + isize(*a) + isize(*b),
        Instr::Block(_, b) => 1 + isize(*b),
        Instr::Loop(_, b) => 1 + isize(*b),
        Instr::If(_, t, e) => 1 + isize(*t) + isize(*e),
        _ => 1,
    }
}

/// Type-check `i` against the stack types `stk`, giving what it leaves.
/// `None` means the instruction is ill-typed.
pub open spec fn tc(lay: Layout, ctx: Ctx, i: Instr, stk: Seq<Ty>) -> Option<Flow>
    decreases isize(i), 1nat,
{
    let n = stk.len();
    match i {
        // Wasm core §3.3.8 `nop`: [] -> [].
        Instr::Nop => Some(Flow::Falls(stk)),
        // Wasm core §3.3.8 instruction sequences; a diverging instruction
        // may not be followed by anything (difference 1).
        Instr::Then(a, b) => {
            match tc(lay, ctx, *a, stk) {
                Some(Flow::Falls(s1)) => tc(lay, ctx, *b, s1),
                _ => None,
            }
        },
        // Wasm core §3.3.1 `t.const c`: [] -> [t].
        Instr::Const(v) => Some(Flow::Falls(stk.push(val_ty(v)))),
        // Wasm core §3.3.5 `local.get x`: [] -> [t].
        Instr::LocalGet(x) => {
            if x < ctx.locals.len() {
                Some(Flow::Falls(stk.push(ctx.locals[x as int])))
            } else {
                None
            }
        },
        // Wasm core §3.3.5 `local.set x`: [t] -> [].
        Instr::LocalSet(x) => {
            if x < ctx.locals.len() && n >= 1 && ty_sub(stk.last(), ctx.locals[x as int]) {
                Some(Flow::Falls(stk.drop_last()))
            } else {
                None
            }
        },
        // Wasm core §3.3.5 `local.tee x`: [t] -> [t].
        Instr::LocalTee(x) => {
            if x < ctx.locals.len() && n >= 1 && ty_sub(stk.last(), ctx.locals[x as int]) {
                Some(Flow::Falls(stk))
            } else {
                None
            }
        },
        // Wasm core §3.3.4 `drop`: [t] -> [].
        Instr::Drop => {
            if n >= 1 {
                Some(Flow::Falls(stk.drop_last()))
            } else {
                None
            }
        },
        // Wasm core §3.3.4 `select`: [t t i32] -> [t].
        Instr::Select => {
            if n >= 3 && stk[n - 1] == Ty::I32 && stk[n - 3] == stk[n - 2] {
                Some(Flow::Falls(below(stk, 3).push(stk[n - 3])))
            } else {
                None
            }
        },
        // Wasm core §3.3.1 `t.binop`, `t.relop`: [t t] -> [t] or [i32].
        Instr::Bin(op) => {
            if n >= 2 && ty_sub(stk[n - 2], bin_arg(op)) && ty_sub(stk[n - 1], bin_arg(op)) {
                Some(Flow::Falls(below(stk, 2).push(bin_res(op))))
            } else {
                None
            }
        },
        // Wasm core §3.3.1 `t.unop`, `t.testop`, `t2.cvtop`: [t1] -> [t2].
        Instr::Un(op) => {
            if n >= 1 && ty_sub(stk[n - 1], un_arg(op)) {
                Some(Flow::Falls(below(stk, 1).push(un_res(op))))
            } else {
                None
            }
        },
        // LIR's `bounds_check`: [i64] -> [Idx(region, size)].
        Instr::BoundsCheck { region, size, code } => {
            if region < lay.len() && n >= 1 && ty_sub(stk[n - 1], Ty::I64) {
                Some(Flow::Falls(below(stk, 1).push(Ty::Idx(region, size))))
            } else {
                None
            }
        },
        // Wasm core §3.3.6 `t.load`: [i32] -> [t], with the address an
        // `Idx` of the region for the size of `t`.
        Instr::Load { region, ty } => {
            if ty_size(ty) > 0 && region < lay.len() && n >= 1 && ty_sub(
                stk[n - 1],
                Ty::Idx(region, ty_size(ty)),
            ) {
                Some(Flow::Falls(below(stk, 1).push(ty)))
            } else {
                None
            }
        },
        // Wasm core §3.3.6 `t.store`: [i32 t] -> [].
        Instr::Store { region, ty } => {
            if ty_size(ty) > 0 && region < lay.len() && n >= 2 && ty_sub(
                stk[n - 2],
                Ty::Idx(region, ty_size(ty)),
            ) && ty_sub(stk[n - 1], ty) {
                Some(Flow::Falls(below(stk, 2)))
            } else {
                None
            }
        },
        // Wasm core §3.3.8 `block`, `loop`.
        Instr::Block(bt, body) => tc_blk(lay, ctx, bt, *body, stk, false),
        Instr::Loop(bt, body) => tc_blk(lay, ctx, bt, *body, stk, true),
        // Wasm core §3.3.8 `if`: [t1* i32] -> [t2*], both arms typed as
        // blocks.
        Instr::If(bt, t, e) => {
            if n >= 1 && ty_sub(stk[n - 1], Ty::I32) {
                match (
                    tc_blk(lay, ctx, bt, *t, stk.drop_last(), false),
                    tc_blk(lay, ctx, bt, *e, stk.drop_last(), false),
                ) {
                    (Some(f1), Some(_)) => Some(f1),
                    _ => None,
                }
            } else {
                None
            }
        },
        // Wasm core §3.3.8 `br l`: [t1* t*] -> [t2*], with `t*` the label's
        // types; here it ends its sequence.
        Instr::Br(l) => {
            if l < ctx.labels.len() && top_sub(stk, ctx.labels[l as int]) {
                Some(Flow::Diverges)
            } else {
                None
            }
        },
        // Wasm core §3.3.8 `br_if l`: [t* i32] -> [t*].
        Instr::BrIf(l) => {
            if n >= 1 && ty_sub(stk[n - 1], Ty::I32) && l < ctx.labels.len() && top_sub(
                stk.drop_last(),
                ctx.labels[l as int],
            ) {
                Some(Flow::Falls(stk.drop_last()))
            } else {
                None
            }
        },
        // Wasm core §3.3.8 `br_table l* l_N`: every label must take the
        // values on the stack.
        Instr::BrTable(ls, d) => {
            if n >= 1 && ty_sub(stk[n - 1], Ty::I32) && d < ctx.labels.len() && top_sub(
                stk.drop_last(),
                ctx.labels[d as int],
            ) && (forall|j: int|
                0 <= j < ls.len() ==> (#[trigger] ls[j]) < ctx.labels.len() && top_sub(
                    stk.drop_last(),
                    ctx.labels[ls[j] as int],
                )) {
                Some(Flow::Diverges)
            } else {
                None
            }
        },
        // LIR's `exit`: takes the operands, never falls through.
        Instr::Exit(code, tys) => {
            if top_sub(stk, tys) {
                Some(Flow::Diverges)
            } else {
                None
            }
        },
    }
}

/// The typing of `block` (`is_loop` false) and `loop` (`is_loop` true): the
/// body is checked on a stack of just the parameters, with a new innermost
/// label whose types are the results (a block) or the parameters (a loop).
pub open spec fn tc_blk(
    lay: Layout,
    ctx: Ctx,
    bt: BlockType,
    body: Instr,
    stk: Seq<Ty>,
    is_loop: bool,
) -> Option<Flow>
    decreases isize(body) + 1, 0nat,
{
    if top_sub(stk, bt.params) {
        let lbl = if is_loop {
            bt.params
        } else {
            bt.results
        };
        let ctx2 = Ctx { locals: ctx.locals, labels: seq![lbl] + ctx.labels };
        let out = Flow::Falls(below(stk, bt.params.len()) + bt.results);
        match tc(lay, ctx2, body, bt.params) {
            Some(Flow::Falls(s)) => if stack_sub(s, bt.results) {
                Some(out)
            } else {
                None
            },
            Some(Flow::Diverges) => Some(out),
            None => None,
        }
    } else {
        None
    }
}

} // verus!
