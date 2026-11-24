//! The refinement of each template ([`lemma_op_refines`]): for every
//! instruction of the slice, its template satisfies [`refines`]. One lemma per
//! kind of instruction, each an instance of [`super::skel::lemma_shape`] with
//! the middle's lemma from [`super::mid`] or [`super::bitmid`]. The A64
//! counterpart of [`crate::proofs`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The hypotheses every case starts from: the stack has `h` values, the states
/// are related, the end of the code does not wrap, and LIR's step fell through
/// to `a2`.
pub open spec fn case_pre(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    code: Seq<isa::Instr>,
    i: lir::Instr,
    fuel: nat,
) -> bool {
    a.stack.len() == h && rel(lay, a, m, nl) && (m.pc as int) + code_len(code)
        < 0x1_0000_0000_0000_0000 && lir::eval(lay, i, a, fuel) == lir::Outcome::Normal(a2)
}

/// A value's stored word is below `2^64`, and below `2^32` for an `i32`.
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

/// `x0`, `x1`, `x2` are distinct scratch registers.
pub proof fn lemma_scratch_regs()
    ensures
        super::rel::scratch(x0()),
        super::rel::scratch(x1()),
        super::rel::scratch(x2()),
        x0() != x1() && x0() != x2() && x1() != x2(),
{
    super::steps::lemma_abi_consts();
}

/// One load of a scratch register from an existing slot is [`super::skel::loads_ok`].
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

/// Two loads into different scratch registers.
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

/// Three loads into different scratch registers.
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

/// The length of a list of `k` instructions, in bytes.
pub proof fn lemma_len_seq(code: Seq<isa::Instr>)
    ensures
        code_len(code) == 4 * code.len(),
{
}

// ----------------------------------------------------------------------------
// Constants, locals, drop and nop
// ----------------------------------------------------------------------------

/// `t.const v` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_const(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::Const(v), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    assert(a2 == a.with_stack(a.stack.push(v)));
    crate::agree::lemma_agree_push(a, a2, nl, h, v);
    let mid = super::templates::const_mid(v);
    let ls = Seq::<(u8, nat)>::empty();
    assert(super::templates::tmpl(Op::Const(v), nl, h) == super::templates::shape(ls, mid, nl + h));
    assert(super::skel::loads_ok(ls, nl, a.stack.len()));
    assert(super::skel::mid_prop(a, nl, ls, mid, lir::val_bits(v))) by {
        assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
            mid,
            lir::val_bits(v),
            s,
        ) by {
            super::bitmid::lemma_mid_const(s, v);
        }
    }
    super::steps::lemma_abi_consts();
    super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, nl + h, lir::val_bits(v));
}

/// `local.get x` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_local_get(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::LocalGet(x), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    let xn = x as nat;
    assert(xn < a.locals.len());
    let v = a.locals[xn as int];
    assert(a2 == a.with_stack(a.stack.push(v)));
    crate::agree::lemma_agree_push(a, a2, nl, h, v);
    let mid = Seq::<isa::Instr>::empty();
    let ls = seq![(x0(), xn)];
    assert(super::templates::tmpl(Op::LocalGet(x), nl, h) == super::templates::shape(ls, mid, nl + h));
    assert(slot_val(a, nl, xn) == v);
    lemma_scratch_regs();
    lemma_loads_ok1(x0(), xn, nl, a.stack.len());
    assert(super::skel::mid_prop(a, nl, ls, mid, lir::val_bits(v))) by {
        assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
            mid,
            lir::val_bits(v),
            s,
        ) by {
            assert(s.r[ls[0].0 as int] as nat == lir::val_bits(slot_val(a, nl, xn)));
            assert(run_seq(s, mid) == Some(s));
        }
    }
    super::steps::lemma_abi_consts();
    super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, nl + h, lir::val_bits(v));
}

/// `local.set x` and `local.tee x` refine.
#[verifier::rlimit(500)]
pub proof fn lemma_case_local_set_tee(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
        super::contract::refines_post(lay, a2, m, nl, super::templates::tmpl(op, nl, h), run_seq(m, super::templates::tmpl(op, nl, h))),
{
    super::steps::lemma_frame_agrees();
    let xn = x as nat;
    let top = (nl + h - 1) as nat;
    if op == Op::LocalSet(x) {
        assert(a2 == (lir::St {
            stack: a.stack.drop_last(),
            locals: a.locals.update(xn as int, a.stack.last()),
            mem: a.mem,
        }));
        crate::agree::lemma_agree_set(a, a2, nl, h, xn);
    } else {
        assert(a2 == a.with_locals(a.locals.update(xn as int, a.stack.last())));
        crate::agree::lemma_agree_tee(a, a2, nl, h, xn);
    }
    let mid = Seq::<isa::Instr>::empty();
    let ls = seq![(x0(), top)];
    let w = lir::val_bits(slot_val(a, nl, top));
    assert(super::templates::tmpl(op, nl, h) == super::templates::shape(ls, mid, xn));
    super::steps::lemma_abi_consts();
    lemma_scratch_regs();
    lemma_loads_ok1(x0(), top, nl, a.stack.len());
    assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
        assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(mid, w, s) by {
            assert(s.r[ls[0].0 as int] as nat == lir::val_bits(slot_val(a, nl, top)));
            assert(run_seq(s, mid) == Some(s));
        }
    }
    super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, xn, w);
}

/// `drop` and `nop` refine (no code).
pub proof fn lemma_case_drop_nop(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
        super::contract::refines_post(lay, a2, m, nl, super::templates::tmpl(op, nl, h), run_seq(m, super::templates::tmpl(op, nl, h))),
{
    super::steps::lemma_frame_agrees();
    assert(super::templates::tmpl(op, nl, h) == Seq::<isa::Instr>::empty());
    assert(run_seq(m, super::templates::tmpl(op, nl, h)) == Some(m));
    if op is Drop {
        assert(a2 == a.with_stack(a.stack.drop_last()));
        crate::agree::lemma_agree_drop(a, a2, nl, h);
    } else {
        assert(a2 == a);
        crate::agree::lemma_agree_refl(a, nl);
    }
    super::rel::lemma_rel_agree(lay, a, a2, m, nl);
    assert(preserved(m, m));
}

// ----------------------------------------------------------------------------
// select
// ----------------------------------------------------------------------------

/// `select` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_select(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::Select, nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
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
            crate::agree::lemma_agree_replace(a, a2, nl, h, 3, r);
            let ls = seq![(x0(), t), (x1(), t + 1), (x2(), t + 2)];
            let mid = super::templates::select_mid();
            let w = lir::val_bits(r);
            assert(super::templates::tmpl(Op::Select, nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok3(x0(), t, x1(), t + 1, x2(), t + 2, nl, a.stack.len());
            assert(slot_val(a, nl, t) == v1);
            assert(slot_val(a, nl, t + 1) == v2);
            assert(slot_val(a, nl, t + 2) == lir::Val::I32(c));
            lemma_bits_u64(v1);
            lemma_bits_u64(v2);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == lir::val_bits(v1));
                    assert(s.r[ls[1].0 as int] as nat == lir::val_bits(v2));
                    assert(s.r[ls[2].0 as int] as nat == c as nat);
                    assert(s.pc as int + 8 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_select(s, lir::val_bits(v1) as u64, lir::val_bits(v2) as u64, c);
                    assert(code_len(mid) == 8);
                }
            }
            super::steps::lemma_abi_consts();
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

// ----------------------------------------------------------------------------
// Binary instructions
// ----------------------------------------------------------------------------

/// An `i32` or `i64` arithmetic, logic or shift instruction refines: `sf` is
/// the width, `v1`, `v2` the operand values and `r` the result value.
#[verifier::rlimit(500)]
pub proof fn lemma_case_bin_int(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    b: lir::BinOp,
    o: lir::IBin,
    sf: isa::Width,
    fuel: nat,
)
    requires
        b == lir::BinOp::I32(o) && sf is W32 || b == lir::BinOp::I64(o) && sf is W64,
        op_ok(Op::Bin(b), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Bin(b), nl, h), Op::Bin(b)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Bin(b), nl, h),
            run_seq(m, super::templates::tmpl(Op::Bin(b), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    let t = (nl + h - 2) as nat;
    let ls = seq![(x0(), t), (x1(), t + 1)];
    let mid = seq![super::templates::int_op_instr(o, sf)];
    assert(super::templates::tmpl(Op::Bin(b), nl, h) == super::templates::shape(ls, mid, t));
    lemma_loads_ok2(x0(), t, x1(), t + 1, nl, a.stack.len());
    assert(slot_val(a, nl, t) == a.stack[(h - 2) as int]);
    assert(slot_val(a, nl, t + 1) == a.stack[(h - 1) as int]);
    match (a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
        (lir::Val::I32(x), lir::Val::I32(y)) => {
            assert(sf is W32);
            let v = lir::Val::I32(lir::ibin32(o, x, y));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let w = lir::val_bits(v);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.r[ls[1].0 as int] as nat == y as nat);
                    assert(super::alu::bits(sf) == 32);
                    assert(s.pc as int + 4 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_int(s, sf, o, x as u64, y as u64);
                    assert(((x as u64) as u32) == x && ((y as u64) as u32) == y);
                    assert(code_len(mid) == 4);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        (lir::Val::I64(x), lir::Val::I64(y)) => {
            assert(sf is W64);
            let v = lir::Val::I64(lir::ibin64(o, x, y));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let w = lir::val_bits(v);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.r[ls[1].0 as int] as nat == y as nat);
                    assert(super::alu::bits(sf) == 64);
                    assert(s.pc as int + 4 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_int(s, sf, o, x, y);
                    assert(code_len(mid) == 4);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// An `i32` or `i64` comparison refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_cmp_int(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    b: lir::BinOp,
    c: lir::ICmp,
    sf: isa::Width,
    fuel: nat,
)
    requires
        b == lir::BinOp::I32Cmp(c) && sf is W32 || b == lir::BinOp::I64Cmp(c) && sf is W64,
        op_ok(Op::Bin(b), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Bin(b), nl, h), Op::Bin(b)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Bin(b), nl, h),
            run_seq(m, super::templates::tmpl(Op::Bin(b), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    let t = (nl + h - 2) as nat;
    let ls = seq![(x0(), t), (x1(), t + 1)];
    let mid = super::templates::cmp_mid(c, sf);
    assert(super::templates::tmpl(Op::Bin(b), nl, h) == super::templates::shape(ls, mid, t));
    lemma_loads_ok2(x0(), t, x1(), t + 1, nl, a.stack.len());
    assert(slot_val(a, nl, t) == a.stack[(h - 2) as int]);
    assert(slot_val(a, nl, t + 1) == a.stack[(h - 1) as int]);
    match (a.stack[(h - 2) as int], a.stack[(h - 1) as int]) {
        (lir::Val::I32(x), lir::Val::I32(y)) => {
            assert(sf is W32);
            let v = lir::Val::I32(lir::bool_i32(lir::icmp(c, 32, x as int, y as int)));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let w = lir::val_bits(v);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.r[ls[1].0 as int] as nat == y as nat);
                    assert(super::alu::bits(sf) == 32);
                    assert(s.pc as int + 8 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_cmp(s, c, sf, x as u64, y as u64);
                    assert(code_len(mid) == 8);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        (lir::Val::I64(x), lir::Val::I64(y)) => {
            assert(sf is W64);
            let v = lir::Val::I32(lir::bool_i32(lir::icmp(c, 64, x as int, y as int)));
            assert(a2 == a.with_stack(lir::below(a.stack, 2).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 2, v);
            let w = lir::val_bits(v);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.r[ls[1].0 as int] as nat == y as nat);
                    assert(super::alu::bits(sf) == 64);
                    assert(s.pc as int + 8 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_cmp(s, c, sf, x, y);
                    assert(code_len(mid) == 8);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

// ----------------------------------------------------------------------------
// Unary instructions
// ----------------------------------------------------------------------------

/// `i32.eqz` and `i64.eqz` refine.
#[verifier::rlimit(500)]
pub proof fn lemma_case_eqz(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    u: lir::UnOp,
    sf: isa::Width,
    fuel: nat,
)
    requires
        u == lir::UnOp::I32Eqz && sf is W32 || u == lir::UnOp::I64Eqz && sf is W64,
        op_ok(Op::Un(u), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(u), nl, h), Op::Un(u)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(u), nl, h),
            run_seq(m, super::templates::tmpl(Op::Un(u), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    let t = (nl + h - 1) as nat;
    let ls = seq![(x0(), t)];
    let mid = super::templates::eqz_mid(sf);
    assert(super::templates::tmpl(Op::Un(u), nl, h) == super::templates::shape(ls, mid, t));
    lemma_loads_ok1(x0(), t, nl, a.stack.len());
    assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
    match a.stack[(h - 1) as int] {
        lir::Val::I32(x) => {
            assert(sf is W32);
            let v = lir::Val::I32(lir::bool_i32(x == 0));
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let w = lir::val_bits(v);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(super::alu::bits(sf) == 32);
                    assert(s.pc as int + 8 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_eqz(s, sf, x as u64);
                    assert(code_len(mid) == 8);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        lir::Val::I64(x) => {
            assert(sf is W64);
            let v = lir::Val::I32(lir::bool_i32(x == 0));
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let w = lir::val_bits(v);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(super::alu::bits(sf) == 64);
                    assert(s.pc as int + 8 < 0x1_0000_0000_0000_0000);
                    super::mid::lemma_mid_eqz(s, sf, x);
                    assert(code_len(mid) == 8);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `f64.neg` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_f64_neg(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::Un(lir::UnOp::F64Neg), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::F64(x) => {
            let v = lir::Val::F64(x ^ 0x8000_0000_0000_0000);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(x0(), t)];
            let mid = super::templates::neg_mid();
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::F64Neg), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(x0(), t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.pc as int + 8 < 0x1_0000_0000_0000_0000);
                    super::bitmid::lemma_mid_neg(s, x);
                    assert(code_len(mid) == 8);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `f64.abs` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_f64_abs(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::Un(lir::UnOp::F64Abs), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::F64(x) => {
            let v = lir::Val::F64(x & 0x7FFF_FFFF_FFFF_FFFF);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(x0(), t)];
            let mid = super::templates::abs_mid();
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::F64Abs), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(x0(), t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.pc as int + 4 < 0x1_0000_0000_0000_0000);
                    super::bitmid::lemma_mid_abs(s, x);
                    assert(code_len(mid) == 4);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i32.wrap_i64` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_wrap(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::Un(lir::UnOp::I32WrapI64), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::I64(x) => {
            let v = lir::Val::I32((x & 0xFFFF_FFFF) as u32);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(x0(), t)];
            let mid = super::templates::wrap_mid();
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I32WrapI64), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(x0(), t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.pc as int + 4 < 0x1_0000_0000_0000_0000);
                    super::bitmid::lemma_mid_wrap(s, x);
                    assert(code_len(mid) == 4);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i64.extend_i32_s` refines.
#[verifier::rlimit(500)]
pub proof fn lemma_case_extend_s(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
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
            run_seq(m, super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32S), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    lemma_scratch_regs();
    super::steps::lemma_abi_consts();
    let t = (nl + h - 1) as nat;
    match a.stack[(h - 1) as int] {
        lir::Val::I32(x) => {
            let v = lir::Val::I64(lir::wrap(64, lir::signed_of(32, x as int)) as u64);
            assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
            crate::agree::lemma_agree_replace(a, a2, nl, h, 1, v);
            let ls = seq![(x0(), t)];
            let mid = super::templates::exts_mid();
            let w = lir::val_bits(v);
            assert(super::templates::tmpl(Op::Un(lir::UnOp::I64ExtendI32S), nl, h) == super::templates::shape(ls, mid, t));
            lemma_loads_ok1(x0(), t, nl, a.stack.len());
            assert(slot_val(a, nl, t) == a.stack[(h - 1) as int]);
            assert(super::skel::mid_prop(a, nl, ls, mid, w)) by {
                assert forall|s: isa::State| super::skel::mid_pre(a, nl, ls, mid, s) implies super::skel::mid_goal(
                    mid,
                    w,
                    s,
                ) by {
                    assert(s.r[ls[0].0 as int] as nat == x as nat);
                    assert(s.r[0] == x as u64);
                    assert(s.pc as int + 4 < 0x1_0000_0000_0000_0000);
                    super::bitmid::lemma_mid_exts(s, x);
                    assert(code_len(mid) == 4);
                }
            }
            super::skel::lemma_shape(lay, a, a2, m, nl, ls, mid, t, w);
        },
        _ => {
            assert(false);
        },
    }
}

/// `i64.extend_i32_u` and the two `reinterpret`s refine (no code): the word is
/// the same.
pub proof fn lemma_case_same_word(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    u: lir::UnOp,
    fuel: nat,
)
    requires
        u is I64ExtendI32U || u is F64ReinterpretI64 || u is I64ReinterpretF64,
        op_ok(Op::Un(u), nl, h),
        case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(Op::Un(u), nl, h), Op::Un(u)@, fuel),
    ensures
        super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(Op::Un(u), nl, h),
            run_seq(m, super::templates::tmpl(Op::Un(u), nl, h)),
        ),
{
    super::steps::lemma_frame_agrees();
    assert(super::templates::tmpl(Op::Un(u), nl, h) == Seq::<isa::Instr>::empty());
    assert(run_seq(m, super::templates::tmpl(Op::Un(u), nl, h)) == Some(m));
    assert(a.stack.last() == a.stack[(h - 1) as int]);
    let v = match (u, a.stack[(h - 1) as int]) {
        (lir::UnOp::I64ExtendI32U, lir::Val::I32(x)) => lir::Val::I64(x as u64),
        (lir::UnOp::F64ReinterpretI64, lir::Val::I64(x)) => lir::Val::F64(x),
        (lir::UnOp::I64ReinterpretF64, lir::Val::F64(x)) => lir::Val::I64(x),
        _ => lir::Val::I32(0),
    };
    match (u, a.stack[(h - 1) as int]) {
        (lir::UnOp::I64ExtendI32U, lir::Val::I32(x)) => {},
        (lir::UnOp::F64ReinterpretI64, lir::Val::I64(x)) => {},
        (lir::UnOp::I64ReinterpretF64, lir::Val::F64(x)) => {},
        _ => {
            assert(false);
        },
    }
    assert(a2 == a.with_stack(lir::below(a.stack, 1).push(v)));
    crate::agree::lemma_agree_same_word(a, a2, nl, h, v);
    super::rel::lemma_rel_agree(lay, a, a2, m, nl);
    assert(preserved(m, m));
}

// ----------------------------------------------------------------------------
// Every instruction of the slice
// ----------------------------------------------------------------------------

/// [`refines`] used at a state.
pub proof fn lemma_use_refines(
    i: lir::Instr,
    nl: nat,
    h: nat,
    code: Seq<isa::Instr>,
    lay: lir::Layout,
    a: lir::St,
    m: isa::State,
    fuel: nat,
)
    requires
        super::contract::refines(i, nl, h, code),
    ensures
        a.stack.len() == h && rel(lay, a, m, nl) && (m.pc as int) + code_len(code)
            < 0x1_0000_0000_0000_0000 ==> match lir::eval(lay, i, a, fuel) {
            lir::Outcome::Normal(a2) => super::contract::refines_post(lay, a2, m, nl, code, run_seq(m, code)),
            _ => true,
        },
{
    super::memlemmas::lemma_p2_consts();
}

/// **Every instruction of the slice has a template that refines it.**
#[verifier::rlimit(1000)]
pub proof fn lemma_op_refines(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        super::contract::refines(op@, nl, h, super::templates::tmpl(op, nl, h)),
{
    super::memlemmas::lemma_p2_consts();
    assert forall|lay: lir::Layout, a: lir::St, m: isa::State, fuel: nat|
        #![trigger lir::eval(lay, op@, a, fuel), run_seq(m, super::templates::tmpl(op, nl, h))]
        a.stack.len() == h && rel(lay, a, m, nl) && (m.pc as int) + code_len(super::templates::tmpl(op, nl, h))
            < 0x1_0000_0000_0000_0000 implies match lir::eval(lay, op@, a, fuel) {
        lir::Outcome::Normal(a2) => super::contract::refines_post(
            lay,
            a2,
            m,
            nl,
            super::templates::tmpl(op, nl, h),
            run_seq(m, super::templates::tmpl(op, nl, h)),
        ),
        _ => true,
    } by {
        match lir::eval(lay, op@, a, fuel) {
            lir::Outcome::Normal(a2) => {
                assert(case_pre(lay, a, a2, m, nl, h, super::templates::tmpl(op, nl, h), op@, fuel));
                match op {
                    Op::Nop => lemma_case_drop_nop(lay, a, a2, m, nl, h, op, fuel),
                    Op::Drop => lemma_case_drop_nop(lay, a, a2, m, nl, h, op, fuel),
                    Op::Const(v) => lemma_case_const(lay, a, a2, m, nl, h, v, fuel),
                    Op::LocalGet(x) => lemma_case_local_get(lay, a, a2, m, nl, h, x, fuel),
                    Op::LocalSet(x) => lemma_case_local_set_tee(lay, a, a2, m, nl, h, op, x, fuel),
                    Op::LocalTee(x) => lemma_case_local_set_tee(lay, a, a2, m, nl, h, op, x, fuel),
                    Op::Select => lemma_case_select(lay, a, a2, m, nl, h, fuel),
                    Op::Bin(b) => match b {
                        lir::BinOp::I32(o) => lemma_case_bin_int(lay, a, a2, m, nl, h, b, o, isa::Width::W32, fuel),
                        lir::BinOp::I64(o) => lemma_case_bin_int(lay, a, a2, m, nl, h, b, o, isa::Width::W64, fuel),
                        lir::BinOp::I32Cmp(c) => lemma_case_cmp_int(lay, a, a2, m, nl, h, b, c, isa::Width::W32, fuel),
                        lir::BinOp::I64Cmp(c) => lemma_case_cmp_int(lay, a, a2, m, nl, h, b, c, isa::Width::W64, fuel),
                        lir::BinOp::F64(_) => {
                            assert(false);
                        },
                        lir::BinOp::F64Cmp(_) => {
                            assert(false);
                        },
                    },
                    Op::Un(u) => match u {
                        lir::UnOp::I32Eqz => lemma_case_eqz(lay, a, a2, m, nl, h, u, isa::Width::W32, fuel),
                        lir::UnOp::I64Eqz => lemma_case_eqz(lay, a, a2, m, nl, h, u, isa::Width::W64, fuel),
                        lir::UnOp::F64Neg => lemma_case_f64_neg(lay, a, a2, m, nl, h, fuel),
                        lir::UnOp::F64Abs => lemma_case_f64_abs(lay, a, a2, m, nl, h, fuel),
                        lir::UnOp::I32WrapI64 => lemma_case_wrap(lay, a, a2, m, nl, h, fuel),
                        lir::UnOp::I64ExtendI32S => lemma_case_extend_s(lay, a, a2, m, nl, h, fuel),
                        lir::UnOp::I64ExtendI32U => lemma_case_same_word(lay, a, a2, m, nl, h, u, fuel),
                        lir::UnOp::F64ReinterpretI64 => lemma_case_same_word(lay, a, a2, m, nl, h, u, fuel),
                        lir::UnOp::I64ReinterpretF64 => lemma_case_same_word(lay, a, a2, m, nl, h, u, fuel),
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

/// The stack height after a step that fell through is the one the static
/// analysis computes.
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
        a2.stack.len() == crate::spec::height_after_op(op, h),
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
