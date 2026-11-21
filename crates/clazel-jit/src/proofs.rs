//! **The per-template refinement proofs.** For each instruction of the first
//! slice, [`lemma_op_refines`] proves [`refines`] of its template
//! ([`tmpl`]): running the x86-64 code from a related state reaches a state
//! related to what LIR's [`lir::eval`] says the instruction does.
//!
//! Each case unpacks LIR's semantics for the instruction (the operand
//! values, the new state), shows which slots change ([`crate::agree`]), proves
//! the template's register-only middle correct ([`crate::mid`]), and applies
//! the skeleton ([`crate::skel`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The common hypotheses of a case: the LIR state has height `h`, the machine
/// state is related to it, the code ends at a canonical address, and LIR
/// falls through to `a2`.
pub open spec fn case_pre(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    code: Seq<x64::Instr>,
    i: lir::Instr,
    fuel: nat,
) -> bool {
    a.stack.len() == h && rel(lay, a, m, nl) && x64::canonical(m.rip + code_len(code))
        && lir::eval(lay, i, a, fuel) == lir::Outcome::Normal(a2)
}

/// A word in a slot, as the `u64` register value.
pub proof fn lemma_bits_u64(v: lir::Val)
    ensures
        lir::val_bits(v) < 0x1_0000_0000_0000_0000,
        v is I32 ==> lir::val_bits(v) < 0x1_0000_0000,
{
    match v {
        lir::Val::I32(x) => {},
        lir::Val::I64(x) => {},
        lir::Val::F64(x) => {},
    }
}

// ----------------------------------------------------------------------------
// Constants, locals, drop and nop
// ----------------------------------------------------------------------------

/// `t.const v`.
#[verifier::rlimit(200)]
pub proof fn lemma_case_const(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    v: lir::Val,
    fuel: nat,
)
    requires
        op_ok(Op::Const(v), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Const(v), nl, h), Op::Const(v)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Const(v), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Const(v), nl, h)),
        ),
{
    assert(a2 == a.with_stack(a.stack.push(v)));
    super::agree::lemma_agree_push(a, a2, nl, h, v);
    let mid = seq![super::templates::const_instr(v)];
    let ls = Seq::<(u8, nat)>::empty();
    assert(super::templates::tmpl(Op::Const(v), nl, h) == super::templates::shape(ls, mid, nl + h));
    assert(super::skel::loads_ok(ls, nl, a.stack.len()));
    assert(super::skel::mid_prop(cu, a, nl, ls, mid, lir::val_bits(v))) by {
        assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
            cu,
            mid,
            lir::val_bits(v),
            s,
        ) by {
            super::mid::lemma_mid_const(cu, s, v);
        }
    }
    super::steps::lemma_abi_consts();
    super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, nl + h, lir::val_bits(v));
}

/// `local.get x`.
#[verifier::rlimit(200)]
pub proof fn lemma_case_local_get(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    x: usize,
    fuel: nat,
)
    requires
        op_ok(Op::LocalGet(x), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::LocalGet(x), nl, h), Op::LocalGet(x)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::LocalGet(x), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::LocalGet(x), nl, h)),
        ),
{
    let xn = x as nat;
    assert(xn < a.locals.len());
    let v = a.locals[xn as int];
    assert(a2 == a.with_stack(a.stack.push(v)));
    super::agree::lemma_agree_push(a, a2, nl, h, v);
    let mid = Seq::<x64::Instr>::empty();
    let ls = seq![(rax(), xn)];
    assert(super::templates::tmpl(Op::LocalGet(x), nl, h) == super::templates::shape(ls, mid, nl + h));
    assert(slot_val(a, nl, xn) == v);
    assert(super::skel::loads_ok(ls, nl, a.stack.len())) by {
        assert(super::rel::scratch(rax())) by {
            super::steps::lemma_abi_consts();
        }
        assert forall|k: int| 0 <= k < ls.len() implies super::rel::scratch((#[trigger] ls[k]).0) && ls[k].1
            < nl + a.stack.len() by {
            assert(k == 0);
        }
    }
    assert(super::skel::mid_prop(cu, a, nl, ls, mid, lir::val_bits(v))) by {
        assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
            cu,
            mid,
            lir::val_bits(v),
            s,
        ) by {
            assert(s.rgf[ls[0].0 as int] as nat == lir::val_bits(slot_val(a, nl, xn)));
            assert(code_len(mid) == 0);
            assert(run_seq(cu, s, mid) == Some(s));
        }
    }
    super::steps::lemma_abi_consts();
    super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, nl + h, lir::val_bits(v));
}

/// `local.set x` and `local.tee x`: the top's word goes to local `x`.
#[verifier::rlimit(200)]
pub proof fn lemma_case_local_set_tee(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    op: Op,
    x: usize,
    fuel: nat,
)
    requires
        op == Op::LocalSet(x) || op == Op::LocalTee(x),
        op_ok(op, nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(op, nl, h), op@, fuel),
    ensures
        super::contract::refines_post(lay, a2, m, nl, super::templates::tmpl(op, nl, h), run_seq(cu, m, super::templates::tmpl(op, nl, h))),
{
    let xn = x as nat;
    let top = (nl + h - 1) as nat;
    if op == Op::LocalSet(x) {
        assert(a2 == (lir::St {
            stack: a.stack.drop_last(),
            locals: a.locals.update(xn as int, a.stack.last()),
            mem: a.mem,
        }));
        super::agree::lemma_agree_set(a, a2, nl, h, xn);
    } else {
        assert(a2 == a.with_locals(a.locals.update(xn as int, a.stack.last())));
        super::agree::lemma_agree_tee(a, a2, nl, h, xn);
    }
    let mid = Seq::<x64::Instr>::empty();
    let ls = seq![(rax(), top)];
    let w = lir::val_bits(slot_val(a, nl, top));
    assert(super::templates::tmpl(op, nl, h) == super::templates::shape(ls, mid, xn));
    super::steps::lemma_abi_consts();
    assert(super::skel::loads_ok(ls, nl, a.stack.len())) by {
        assert(super::rel::scratch(rax()));
        assert forall|k: int| 0 <= k < ls.len() implies super::rel::scratch((#[trigger] ls[k]).0) && ls[k].1
            < nl + a.stack.len() by {
            assert(k == 0);
        }
    }
    assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
        assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(cu, mid, w, s) by {
            assert(s.rgf[ls[0].0 as int] as nat == lir::val_bits(slot_val(a, nl, top)));
            assert(code_len(mid) == 0);
            assert(run_seq(cu, s, mid) == Some(s));
        }
    }
    super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, xn, w);
}

/// `drop` and `nop`: no code. LIR changes only the stack, and the machine's
/// frame already holds every slot that is left.
pub proof fn lemma_case_drop_nop(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    op: Op,
    fuel: nat,
)
    requires
        op is Drop || op is Nop,
        op_ok(op, nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(op, nl, h), op@, fuel),
    ensures
        super::contract::refines_post(lay, a2, m, nl, super::templates::tmpl(op, nl, h), run_seq(cu, m, super::templates::tmpl(op, nl, h))),
{
    assert(super::templates::tmpl(op, nl, h) == Seq::<x64::Instr>::empty());
    assert(run_seq(cu, m, super::templates::tmpl(op, nl, h)) == Some(m));
    assert(code_len(super::templates::tmpl(op, nl, h)) == 0);
    if op is Drop {
        assert(a2 == a.with_stack(a.stack.drop_last()));
        super::agree::lemma_agree_drop(a, a2, nl, h);
    } else {
        assert(a2 == a);
        super::agree::lemma_agree_refl(a, nl);
    }
    super::rel::lemma_rel_agree(lay, a, a2, m, nl);
    super::agree::lemma_preserved_refl(m);
}

// ----------------------------------------------------------------------------
// Loads
// ----------------------------------------------------------------------------

/// `rax`, `rcx` and `rdx` are scratch registers.
pub proof fn lemma_scratch_regs()
    ensures
        super::rel::scratch(rax()),
        super::rel::scratch(rcx()),
        super::rel::scratch(rdx()),
        rax() != rcx() && rax() != rdx() && rcx() != rdx(),
{
    super::steps::lemma_abi_consts();
}

/// One load of a scratch register from an existing slot.
pub proof fn lemma_loads_ok1(r: u8, j: nat, nl: nat, n: nat)
    requires
        super::rel::scratch(r),
        j < nl + n,
    ensures
        super::skel::loads_ok(seq![(r, j)], nl, n),
{
    let ls = seq![(r, j)];
    assert forall|k: int| 0 <= k < ls.len() implies super::rel::scratch((#[trigger] ls[k]).0) && ls[k].1 < nl
        + n by {
        assert(k == 0);
    }
}

/// Two loads into distinct scratch registers from existing slots.
pub proof fn lemma_loads_ok2(r1: u8, j1: nat, r2: u8, j2: nat, nl: nat, n: nat)
    requires
        super::rel::scratch(r1),
        super::rel::scratch(r2),
        r1 != r2,
        j1 < nl + n,
        j2 < nl + n,
    ensures
        super::skel::loads_ok(seq![(r1, j1), (r2, j2)], nl, n),
{
    let ls = seq![(r1, j1), (r2, j2)];
    assert forall|k: int| 0 <= k < ls.len() implies super::rel::scratch((#[trigger] ls[k]).0) && ls[k].1 < nl
        + n by {
        assert(k == 0 || k == 1);
    }
    assert forall|k1: int, k2: int|
        0 <= k1 < k2 < ls.len() implies (#[trigger] ls[k1]).0 != (#[trigger] ls[k2]).0 by {
        assert(k1 == 0 && k2 == 1);
    }
}

/// Three loads into distinct scratch registers from existing slots.
pub proof fn lemma_loads_ok3(
    r1: u8,
    j1: nat,
    r2: u8,
    j2: nat,
    r3: u8,
    j3: nat,
    nl: nat,
    n: nat,
)
    requires
        super::rel::scratch(r1),
        super::rel::scratch(r2),
        super::rel::scratch(r3),
        r1 != r2 && r1 != r3 && r2 != r3,
        j1 < nl + n,
        j2 < nl + n,
        j3 < nl + n,
    ensures
        super::skel::loads_ok(seq![(r1, j1), (r2, j2), (r3, j3)], nl, n),
{
    let ls = seq![(r1, j1), (r2, j2), (r3, j3)];
    assert forall|k: int| 0 <= k < ls.len() implies super::rel::scratch((#[trigger] ls[k]).0) && ls[k].1 < nl
        + n by {
        assert(k == 0 || k == 1 || k == 2);
    }
    assert forall|k1: int, k2: int|
        0 <= k1 < k2 < ls.len() implies (#[trigger] ls[k1]).0 != (#[trigger] ls[k2]).0 by {
        assert(k1 == 0 || k1 == 1);
    }
}

// ----------------------------------------------------------------------------
// select
// ----------------------------------------------------------------------------

/// `select`: `c == 0` picks the second value.
#[verifier::rlimit(300)]
pub proof fn lemma_case_select(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Select, nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Select, nl, h), Op::Select@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Select, nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Select, nl, h)),
        ),
{
    lemma_scratch_regs();
    let t = (nl + h - 3) as nat;
    let v1 = a.stack[(h - 3) as int];
    let v2 = a.stack[(h - 2) as int];
    match a.stack[(h - 1) as int] {
        lir::Val::I32(c) => {
            let r = if c != 0 {
                v1
            } else {
                v2
            };
            assert(a2 == a.with_stack(lir::below(a.stack, 3).push(r)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 3, r);
            let ls = seq![(rax(), t), (rcx(), t + 1), (rdx(), t + 2)];
            let mid = super::templates::select_mid();
            let w = lir::val_bits(r);
            assert(super::templates::tmpl(Op::Select, nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok3(rax(), t, rcx(), t + 1, rdx(), t + 2, nl, a.stack.len());
            assert(slot_val(a, nl, t) == v1);
            assert(slot_val(a, nl, t + 1) == v2);
            assert(slot_val(a, nl, t + 2) == lir::Val::I32(c));
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == lir::val_bits(v1));
                    assert(s.rgf[ls[1].0 as int] as nat == lir::val_bits(v2));
                    assert(s.rgf[ls[2].0 as int] as nat == c as nat);
                    super::mid::lemma_mid_select(
                        cu,
                        s,
                        lir::val_bits(v1) as u64,
                        lir::val_bits(v2) as u64,
                        c,
                    );
                    assert(w == (if c != 0 {
                        lir::val_bits(v1)
                    } else {
                        lir::val_bits(v2)
                    }));
                }
            }
            super::steps::lemma_abi_consts();
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}


// ----------------------------------------------------------------------------
// Binary instructions
// ----------------------------------------------------------------------------

/// A 32-bit integer arithmetic, logic or shift instruction.
#[verifier::rlimit(500)]
pub proof fn lemma_case_bin_i32(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    o: lir::IBin,
    fuel: nat,
)
    requires
        op_ok(Op::Bin(lir::BinOp::I32(o)), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Bin(lir::BinOp::I32(o)), nl, h), Op::Bin(lir::BinOp::I32(o))@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Bin(lir::BinOp::I32(o)), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Bin(lir::BinOp::I32(o)), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 2) as nat;
    match (a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
        (lir::Val::I32(x), lir::Val::I32(y)) => {
            let v = lir::Val::I32(lir::ibin32(o, x, y));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let ls = seq![(rax(), t), (rcx(), t + 1)];
            let mid = seq![super::templates::int_op_instr(o, x64::Size::W32)];
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Bin(lir::BinOp::I32(o)), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok2(ls[0].0, t, ls[1].0, t + 1, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 2) as int]);
            assert(slot_val(a, nl, t + 1) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[ls[1].0 as int] as nat == y as nat);
                    assert(s.rgf[0] == x as u64);
                    assert(s.rgf[1] == y as u64);
                    super::runseq::lemma_code_len_one(super::templates::int_op_instr(o, x64::Size::W32));
                    super::mid::lemma_mid_int32(cu, s, o, x, y);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// A 64-bit integer arithmetic, logic or shift instruction.
#[verifier::rlimit(500)]
pub proof fn lemma_case_bin_i64(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    o: lir::IBin,
    fuel: nat,
)
    requires
        op_ok(Op::Bin(lir::BinOp::I64(o)), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Bin(lir::BinOp::I64(o)), nl, h), Op::Bin(lir::BinOp::I64(o))@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Bin(lir::BinOp::I64(o)), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Bin(lir::BinOp::I64(o)), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 2) as nat;
    match (a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
        (lir::Val::I64(x), lir::Val::I64(y)) => {
            let v = lir::Val::I64(lir::ibin64(o, x, y));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let ls = seq![(rax(), t), (rcx(), t + 1)];
            let mid = seq![super::templates::int_op_instr(o, x64::Size::W64)];
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Bin(lir::BinOp::I64(o)), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok2(ls[0].0, t, ls[1].0, t + 1, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 2) as int]);
            assert(slot_val(a, nl, t + 1) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[ls[1].0 as int] as nat == y as nat);
                    assert(s.rgf[0] == x);
                    assert(s.rgf[1] == y);
                    super::runseq::lemma_code_len_one(super::templates::int_op_instr(o, x64::Size::W64));
                    super::mid::lemma_mid_int64(cu, s, o, x, y);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// A 32-bit integer comparison.
#[verifier::rlimit(500)]
pub proof fn lemma_case_cmp_i32(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    c: lir::ICmp,
    fuel: nat,
)
    requires
        op_ok(Op::Bin(lir::BinOp::I32Cmp(c)), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Bin(lir::BinOp::I32Cmp(c)), nl, h), Op::Bin(lir::BinOp::I32Cmp(c))@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Bin(lir::BinOp::I32Cmp(c)), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Bin(lir::BinOp::I32Cmp(c)), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 2) as nat;
    match (a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
        (lir::Val::I32(x), lir::Val::I32(y)) => {
            let v = lir::Val::I32(lir::bool_i32(lir::icmp(c, 32, x as int, y as int)));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let ls = seq![(rcx(), t), (rdx(), t + 1)];
            let mid = super::templates::cmp_mid(c, x64::Size::W32);
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Bin(lir::BinOp::I32Cmp(c)), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok2(ls[0].0, t, ls[1].0, t + 1, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 2) as int]);
            assert(slot_val(a, nl, t + 1) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[ls[1].0 as int] as nat == y as nat);
                    assert(s.rgf[1] == x as u64);
                    assert(s.rgf[2] == y as u64);
                    assert(x64::nbits(x64::Size::W32) == 32);
                    super::mid::lemma_mid_cmp(cu, s, c, x64::Size::W32, x as u64, y as u64);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// A 64-bit integer comparison.
#[verifier::rlimit(500)]
pub proof fn lemma_case_cmp_i64(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    c: lir::ICmp,
    fuel: nat,
)
    requires
        op_ok(Op::Bin(lir::BinOp::I64Cmp(c)), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Bin(lir::BinOp::I64Cmp(c)), nl, h), Op::Bin(lir::BinOp::I64Cmp(c))@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Bin(lir::BinOp::I64Cmp(c)), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Bin(lir::BinOp::I64Cmp(c)), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 2) as nat;
    match (a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
        (lir::Val::I64(x), lir::Val::I64(y)) => {
            let v = lir::Val::I32(lir::bool_i32(lir::icmp(c, 64, x as int, y as int)));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let ls = seq![(rcx(), t), (rdx(), t + 1)];
            let mid = super::templates::cmp_mid(c, x64::Size::W64);
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Bin(lir::BinOp::I64Cmp(c)), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok2(ls[0].0, t, ls[1].0, t + 1, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 2) as int]);
            assert(slot_val(a, nl, t + 1) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[ls[1].0 as int] as nat == y as nat);
                    assert(s.rgf[1] == x);
                    assert(s.rgf[2] == y);
                    assert(x64::nbits(x64::Size::W64) == 64);
                    super::mid::lemma_mid_cmp(cu, s, c, x64::Size::W64, x, y);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i32.eqz`.
#[verifier::rlimit(500)]
pub proof fn lemma_case_eqz_i32(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::I32Eqz), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::I32Eqz), nl, h), Op::Un(lir::UnOp::I32Eqz)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::I32Eqz), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I32Eqz), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::I32(x) => {
            let v = lir::Val::I32(lir::bool_i32(x == 0));
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(rcx(), t)];
            let mid = super::templates::eqz_mid(x64::Size::W32);
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I32Eqz), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(ls[0].0, t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[1] == x as u64);
                    super::mid::lemma_mid_eqz(cu, s, x64::Size::W32, x as u64);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i64.eqz`.
#[verifier::rlimit(500)]
pub proof fn lemma_case_eqz_i64(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::I64Eqz), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::I64Eqz), nl, h), Op::Un(lir::UnOp::I64Eqz)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::I64Eqz), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I64Eqz), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::I64(x) => {
            let v = lir::Val::I32(lir::bool_i32(x == 0));
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(rcx(), t)];
            let mid = super::templates::eqz_mid(x64::Size::W64);
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I64Eqz), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(ls[0].0, t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[1] == x);
                    super::mid::lemma_mid_eqz(cu, s, x64::Size::W64, x);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `f64.neg`: flip the sign bit of the word.
#[verifier::rlimit(500)]
pub proof fn lemma_case_f64_neg(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::F64Neg), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::F64Neg), nl, h), Op::Un(lir::UnOp::F64Neg)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::F64Neg), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::F64Neg), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::F64(x) => {
            let v = lir::Val::F64(x ^ 0x8000_0000_0000_0000);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(rax(), t)];
            let mid = super::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000);
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::F64Neg), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(ls[0].0, t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[0] == x);
                    super::mid::lemma_mid_mask(cu, s, x64::AluOp::Xor, 0x8000_0000_0000_0000, x);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `f64.abs`: clear the sign bit of the word.
#[verifier::rlimit(500)]
pub proof fn lemma_case_f64_abs(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::F64Abs), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::F64Abs), nl, h), Op::Un(lir::UnOp::F64Abs)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::F64Abs), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::F64Abs), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::F64(x) => {
            let v = lir::Val::F64(x & 0x7FFF_FFFF_FFFF_FFFF);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(rax(), t)];
            let mid = super::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF);
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::F64Abs), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(ls[0].0, t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[0] == x);
                    super::mid::lemma_mid_mask(cu, s, x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF, x);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i32.wrap_i64`.
#[verifier::rlimit(500)]
pub proof fn lemma_case_wrap(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::I32WrapI64), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::I32WrapI64), nl, h), Op::Un(lir::UnOp::I32WrapI64)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::I32WrapI64), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I32WrapI64), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::I64(x) => {
            let v = lir::Val::I32((x & 0xFFFF_FFFF) as u32);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(rax(), t)];
            let mid = super::templates::wrap_mid();
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I32WrapI64), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(ls[0].0, t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[0] == x);
                    super::mid::lemma_mid_wrap(cu, s, x);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i64.extend_i32_s`.
#[verifier::rlimit(500)]
pub proof fn lemma_case_extend_s(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::I64ExtendI32S), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32S), nl, h), Op::Un(lir::UnOp::I64ExtendI32S)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32S), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32S), nl, h)),
        ),
{
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::I32(x) => {
            let v = lir::Val::I64(lir::wrap(64, lir::signed_of(32, x as int)) as u64);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            super::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(rax(), t)];
            let mid = super::templates::exts_mid();
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32S), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(ls[0].0, t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(cu, a, nl, ls, mid, w)) by {
                assert forall|s: x64::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    cu,
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.rgf[ls[0].0 as int] as nat == x as nat);
                    assert(s.rgf[0] == x as u64);
                    super::mid::lemma_mid_exts(cu, s, x);
                }
            }
            super::skel::lemma_shape(cu, lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i64.extend_i32_u`: the word is already zero-extended.
pub proof fn lemma_case_extend_u(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::I64ExtendI32U), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32U), nl, h), Op::Un(lir::UnOp::I64ExtendI32U)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32U), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32U), nl, h)),
        ),
{
    match a.stack[(h - 1) as int] {
        lir::Val::I32(x) => {
            let v = lir::Val::I64(x as u64);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32U), nl, h) == Seq::<x64::Instr>::empty());
            assert(run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32U), nl, h)) == Some(m));
            assert(code_len(super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32U), nl, h)) == 0);
            assert(a.stack.last() == a.stack[(h - 1) as int]);
            super::agree::lemma_agree_same_word(a, a2, nl, h, v);
            super::rel::lemma_rel_agree(lay, a, a2, m, nl);
            super::agree::lemma_preserved_refl(m);
        },
        _ => {
            assert(false);
        },
    }
}

/// `f64.reinterpret_i64`: the same bits.
pub proof fn lemma_case_reinterpret_i64(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h), Op::Un(lir::UnOp::F64ReinterpretI64)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h)),
        ),
{
    match a.stack[(h - 1) as int] {
        lir::Val::I64(x) => {
            let v = lir::Val::F64(x);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            assert(super::templates::tmpl(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h) == Seq::<x64::Instr>::empty());
            assert(run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h)) == Some(m));
            assert(code_len(super::templates::tmpl(Op::Un(lir::UnOp::F64ReinterpretI64), nl, h)) == 0);
            assert(a.stack.last() == a.stack[(h - 1) as int]);
            super::agree::lemma_agree_same_word(a, a2, nl, h, v);
            super::rel::lemma_rel_agree(lay, a, a2, m, nl);
            super::agree::lemma_preserved_refl(m);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i64.reinterpret_f64`: the same bits.
pub proof fn lemma_case_reinterpret_f64(
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    fuel: nat,
)
    requires
        op_ok(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h), Op::Un(lir::UnOp::I64ReinterpretF64)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h),
            run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h)),
        ),
{
    match a.stack[(h - 1) as int] {
        lir::Val::F64(x) => {
            let v = lir::Val::I64(x);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h) == Seq::<x64::Instr>::empty());
            assert(run_seq(cu, m, super::templates::tmpl(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h)) == Some(m));
            assert(code_len(super::templates::tmpl(Op::Un(lir::UnOp::I64ReinterpretF64), nl, h)) == 0);
            assert(a.stack.last() == a.stack[(h - 1) as int]);
            super::agree::lemma_agree_same_word(a, a2, nl, h, v);
            super::rel::lemma_rel_agree(lay, a, a2, m, nl);
            super::agree::lemma_preserved_refl(m);
        },
        _ => {
            assert(false);
        },
    }
}

// ----------------------------------------------------------------------------
// Every instruction of the slice
// ----------------------------------------------------------------------------

/// Instantiating [`refines`] at one state.
pub proof fn lemma_use_refines(
    i: lir::Instr,
    nl: nat,
    h: nat,
    code: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    m: x64::State,
    fuel: nat,
)
    requires
        super::contract::refines(i, nl, h, code),
    ensures
        a.stack.len() == h && rel(lay, a, m, nl) && x64::canonical(m.rip + code_len(code))
            ==> match lir::eval(lay, i, a, fuel) {
            lir::Outcome::Normal(a2) => super::contract::refines_post(lay, a2, m, nl, code, run_seq(cu, m, code)),
            _ => true,
        },
{
}

/// **The refinement of every template of the slice.** An instruction with a
/// template ([`op_ok`]) is refined by it ([`refines`]).
#[verifier::rlimit(1000)]
pub proof fn lemma_op_refines(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        super::contract::refines(op@, nl, h, super::templates::tmpl(op, nl, h)),
{
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger lir::eval(lay, op@, a, fuel), run_seq(cu, m, super::templates::tmpl(op, nl, h))]
        a.stack.len() == h && rel(lay, a, m, nl) && x64::canonical(m.rip + code_len(super::templates::tmpl(op, nl, h)))
            implies match lir::eval(lay, op@, a, fuel) {
        lir::Outcome::Normal(a2) => super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(op, nl, h),
            run_seq(cu, m, super::templates::tmpl(op, nl, h)),
        ),
        _ => true,
    } by {
        match lir::eval(lay, op@, a, fuel) {
            lir::Outcome::Normal(a2) => {
                assert(case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(op, nl, h), op@, fuel));
                match op {
                    Op::Nop => lemma_case_drop_nop(lay, cu, a, a2, m, nl, h, op, fuel),
                    Op::Drop => lemma_case_drop_nop(lay, cu, a, a2, m, nl, h, op, fuel),
                    Op::Const(v) => lemma_case_const(lay, cu, a, a2, m, nl, h, v, fuel),
                    Op::LocalGet(x) => lemma_case_local_get(lay, cu, a, a2, m, nl, h, x, fuel),
                    Op::LocalSet(x) => lemma_case_local_set_tee(
                        lay,
                        cu,
                        a,
                        a2,
                        m,
                        nl,
                        h,
                        op,
                        x,
                        fuel,
                    ),
                    Op::LocalTee(x) => lemma_case_local_set_tee(
                        lay,
                        cu,
                        a,
                        a2,
                        m,
                        nl,
                        h,
                        op,
                        x,
                        fuel,
                    ),
                    Op::Select => lemma_case_select(lay, cu, a, a2, m, nl, h, fuel),
                    Op::Bin(b) => match b {
                        lir::BinOp::I32(o) => lemma_case_bin_i32(lay, cu, a, a2, m, nl, h, o, fuel),
                        lir::BinOp::I64(o) => lemma_case_bin_i64(lay, cu, a, a2, m, nl, h, o, fuel),
                        lir::BinOp::I32Cmp(c) => lemma_case_cmp_i32(
                            lay,
                            cu,
                            a,
                            a2,
                            m,
                            nl,
                            h,
                            c,
                            fuel,
                        ),
                        lir::BinOp::I64Cmp(c) => lemma_case_cmp_i64(
                            lay,
                            cu,
                            a,
                            a2,
                            m,
                            nl,
                            h,
                            c,
                            fuel,
                        ),
                        lir::BinOp::F64(_) => {
                            assert(false);
                        },
                        lir::BinOp::F64Cmp(_) => {
                            assert(false);
                        },
                    },
                    Op::Un(u) => match u {
                        lir::UnOp::I32Eqz => lemma_case_eqz_i32(lay, cu, a, a2, m, nl, h, fuel),
                        lir::UnOp::I64Eqz => lemma_case_eqz_i64(lay, cu, a, a2, m, nl, h, fuel),
                        lir::UnOp::F64Neg => lemma_case_f64_neg(lay, cu, a, a2, m, nl, h, fuel),
                        lir::UnOp::F64Abs => lemma_case_f64_abs(lay, cu, a, a2, m, nl, h, fuel),
                        lir::UnOp::I32WrapI64 => lemma_case_wrap(lay, cu, a, a2, m, nl, h, fuel),
                        lir::UnOp::I64ExtendI32S => lemma_case_extend_s(
                            lay,
                            cu,
                            a,
                            a2,
                            m,
                            nl,
                            h,
                            fuel,
                        ),
                        lir::UnOp::I64ExtendI32U => lemma_case_extend_u(
                            lay,
                            cu,
                            a,
                            a2,
                            m,
                            nl,
                            h,
                            fuel,
                        ),
                        lir::UnOp::F64ReinterpretI64 => lemma_case_reinterpret_i64(
                            lay,
                            cu,
                            a,
                            a2,
                            m,
                            nl,
                            h,
                            fuel,
                        ),
                        lir::UnOp::I64ReinterpretF64 => lemma_case_reinterpret_f64(
                            lay,
                            cu,
                            a,
                            a2,
                            m,
                            nl,
                            h,
                            fuel,
                        ),
                        lir::UnOp::F64Sqrt => {
                            assert(false);
                        },
                        lir::UnOp::F64ConvertI32S => {
                            assert(false);
                        },
                        lir::UnOp::F64ConvertI32U => {
                            assert(false);
                        },
                        lir::UnOp::F64ConvertI64S => {
                            assert(false);
                        },
                        lir::UnOp::F64ConvertI64U => {
                            assert(false);
                        },
                    },
                }
            },
            _ => {},
        }
    }
}

/// An instruction with a template changes the operand stack's height as
/// `pops` and `pushes` say, keeps the locals' count and memory.
pub proof fn lemma_op_height(
    op: Op,
    nl: nat,
    h: nat,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    fuel: nat,
)
    requires
        op_ok(op, nl, h),
        a.stack.len() == h,
        lir::eval(lay, op@, a, fuel) == lir::Outcome::Normal(a2),
    ensures
        a2.stack.len() == height_after_op(op, h),
{
    assert(fuel > 0);
    match op {
        Op::Nop => {},
        Op::Drop => {},
        Op::Const(v) => {},
        Op::LocalGet(x) => {},
        Op::LocalSet(x) => {},
        Op::LocalTee(x) => {},
        Op::Select => {
            match a.stack[(h - 1) as int] {
                lir::Val::I32(c) => {
                    assert(a2.stack.len() == (h - 3) + 1);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Op::Bin(b) => {
            match lir::bin_eval(b, a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
                Some(v) => {
                    assert(a2.stack.len() == (h - 2) + 1);
                },
                None => {
                    assert(false);
                },
            }
        },
        Op::Un(u) => {
            match lir::un_eval(u, a.stack[(h - 1) as int]) {
                Some(v) => {
                    assert(a2.stack.len() == (h - 1) + 1);
                },
                None => {
                    assert(false);
                },
            }
        },
    }
}

} // verus!
