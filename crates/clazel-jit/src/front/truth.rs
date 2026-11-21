//! Truthiness: `Not`, `JumpIfTrue`, `JumpIfFalse`, on booleans and int32s.
//!
//! The guard is "the operand is an int32, or a boolean" (`(v | 1) == true`
//! holds for `false` and `true` and no other value); every other operand
//! (`undefined`, `null`, doubles, heap references, ...) exits to the handler,
//! which for `undefined`, `null` and doubles includes cases where `fast_path`
//! holds and so relies on [`handler_complete`]. For an int32 or a boolean the
//! truth value is `isint & (payload != 0) | (v == true)`: an int32 word is
//! never `true`'s word and a boolean word is never an int32's.
//!
//! `Not` stores the encoded boolean of the negation; `JumpIfTrue` and
//! `JumpIfFalse` are a `br_if` on the truth value (or its negation).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The guard's instructions after the tag test: is the word `false` or
/// `true`, and `or` that into the tag test's flag.
pub open spec fn tr_guard_tail() -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(1),
        super::lower::i64c(1),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
        super::lower::i64c(js::TRUE),
        super::lower::cmp64(lir::ICmp::Eq),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::Or)),
    ]
}

/// The guard: an int32 or a boolean.
pub open spec fn tr_guard() -> Seq<lir::Instr> {
    super::lower::tag_test(1) + tr_guard_tail()
}

/// The truth flag's instructions after the tag test.
pub open spec fn tflag_tail() -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(1),
        lir::Instr::Un(lir::UnOp::I32WrapI64),
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
        lir::Instr::LocalGet(1),
        super::lower::i64c(js::TRUE),
        super::lower::cmp64(lir::ICmp::Eq),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::Or)),
    ]
}

/// The truth flag of the word in local 1 (right for an int32 or a boolean).
pub open spec fn tflag() -> Seq<lir::Instr> {
    super::lower::tag_test(1) + tflag_tail()
}

/// The `Not` value block: the encoded negation of the truth flag.
pub open spec fn not_val() -> Seq<lir::Instr> {
    tflag() + seq![
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Un(lir::UnOp::I64ExtendI32U),
        super::lower::i64c(js::FALSE),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Add)),
    ]
}

/// The `Not` lowering.
pub open spec fn lower_not(dst: nat, src: nat, op: js::Op, pc: nat) -> lir::Instr {
    super::blocks::lower_un(tr_guard(), not_val(), dst, src, op, pc)
}

/// What follows the guard in a conditional jump: the truth flag (negated for
/// `JumpIfFalse`), then a `br_if`.
pub open spec fn jump_rest(jf: bool, lbl: nat) -> Seq<lir::Instr> {
    tflag() + (if jf {
        seq![lir::Instr::Un(lir::UnOp::I32Eqz), lir::Instr::BrIf(lbl)]
    } else {
        seq![lir::Instr::BrIf(lbl)]
    })
}

/// The conditional jump lowering: `jf` is `JumpIfFalse`.
pub open spec fn lower_jump(jf: bool, cond: nat, lbl: nat, op: js::Op, pc: nat) -> lir::Instr {
    super::blocks::guarded(
        super::blocks::un_pre(cond, tr_guard()),
        op,
        pc,
        super::run::chain(jump_rest(jf, lbl)),
    )
}

/// The guard's flag for the operand word `va`.
pub open spec fn tr_g(va: u64) -> u32 {
    lir::ibin32(
        lir::IBin::Or,
        lir::bool_i32((va >> 32u64) == super::arith::tag_hi()),
        lir::bool_i32(lir::icmp(lir::ICmp::Eq, 64, (va | 1u64) as int, js::TRUE as int)),
    )
}

/// The truth flag for the operand word `va`.
pub open spec fn tr_t(va: u64) -> u32 {
    lir::ibin32(
        lir::IBin::Or,
        lir::ibin32(
            lir::IBin::And,
            lir::bool_i32((va >> 32u64) == super::arith::tag_hi()),
            lir::bool_i32(lir::bool_i32(super::arith::lo32(va) == 0) == 0),
        ),
        lir::bool_i32(lir::icmp(lir::ICmp::Eq, 64, va as int, js::TRUE as int)),
    )
}

/// The value block of `Not`.
pub open spec fn not_word(va: u64) -> u64 {
    (lir::bool_i32(tr_t(va) == 0) as u64 + js::FALSE) as u64
}

/// `or` of two flags: non-zero when either is.
pub proof fn lemma_or01(e1: u32, e2: u32)
    requires
        e1 == 0 || e1 == 1,
        e2 == 0 || e2 == 1,
    ensures
        ((e1 | e2) != 0) <==> (e1 == 1 || e2 == 1),
        (e1 | e2) == 0 || (e1 | e2) == 1,
{
    assert((((e1 | e2) != 0) <==> (e1 == 1 || e2 == 1)) && ((e1 | e2) == 0 || (e1 | e2) == 1))
        by (bit_vector)
        requires
            e1 == 0 || e1 == 1,
            e2 == 0 || e2 == 1,
    ;
}

/// The guard, truth flag and value blocks are simple and short.
pub proof fn lemma_tr_simple()
    ensures
        super::run::all_simple(tr_guard()),
        tr_guard().len() < 40,
        super::run::all_simple(tflag()),
        tflag().len() == 14,
        super::run::all_simple(not_val()),
        not_val().len() < 40,
        forall|jf: bool, lbl: nat|
            #![trigger jump_rest(jf, lbl)]
            super::run::all_simple(jump_rest(jf, lbl)) && jump_rest(jf, lbl).len() <= 16,
{
    super::intops::lemma_literals_simple(0);
    let g = tr_guard_tail();
    assert(super::run::all_simple(g)) by {
        assert forall|i: int| 0 <= i < g.len() implies super::run::is_simple(#[trigger] g[i]) by {
            assert(0 <= i < 6);
        }
    }
    super::intops::lemma_simple_concat(super::lower::tag_test(1), g);
    let t = tflag_tail();
    assert(super::run::all_simple(t)) by {
        assert forall|i: int| 0 <= i < t.len() implies super::run::is_simple(#[trigger] t[i]) by {
            assert(0 <= i < 9);
        }
    }
    super::intops::lemma_simple_concat(super::lower::tag_test(1), t);
    let nv = seq![
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Un(lir::UnOp::I64ExtendI32U),
        super::lower::i64c(js::FALSE),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Add)),
    ];
    assert(super::run::all_simple(nv)) by {
        assert forall|i: int| 0 <= i < nv.len() implies super::run::is_simple(#[trigger] nv[i]) by {
            assert(0 <= i < 4);
        }
    }
    super::intops::lemma_simple_concat(tflag(), nv);
    assert forall|jf: bool, lbl: nat| #![trigger jump_rest(jf, lbl)]
        super::run::all_simple(jump_rest(jf, lbl)) && jump_rest(jf, lbl).len() <= 16 by {
        let tl = if jf {
            seq![lir::Instr::Un(lir::UnOp::I32Eqz), lir::Instr::BrIf(lbl)]
        } else {
            seq![lir::Instr::BrIf(lbl)]
        };
        assert(super::run::all_simple(tl)) by {
            assert forall|i: int| 0 <= i < tl.len() implies super::run::is_simple(#[trigger] tl[i]) by {
                assert(0 <= i < 2);
            }
        }
        super::intops::lemma_simple_concat(tflag(), tl);
    }
}

/// The guard block's trace.
pub proof fn lemma_tr_guard_trace(lay: lir::Layout, va: u64)
    ensures
        super::blocks::flag_computes(lay, tr_guard(), va, tr_g(va)),
{
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, tr_guard(), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) implies super::run::exec(
        lay,
        tr_guard(),
        st1,
    ) == lir::Outcome::Normal(st1.with_stack(st1.stack.push(lir::Val::I32(tr_g(va))))) by {
        broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

        super::trace::lemma_exec_tag_test(lay, st1, 1, va);
        let s1 = st1.with_stack(st1.stack.push(lir::Val::I32(isint)));
        super::trace::lemma_exec_app(lay, super::lower::tag_test(1), tr_guard_tail(), st1, s1);
        reveal_with_fuel(super::run::exec, 7);
        assert(super::run::exec(lay, tr_guard_tail(), s1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I32(tr_g(va)))),
        ));
    }
}

/// The truth flag block's trace.
pub proof fn lemma_tflag_trace(lay: lir::Layout, va: u64)
    ensures
        super::blocks::flag_computes(lay, tflag(), va, tr_t(va)),
{
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, tflag(), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) implies super::run::exec(
        lay,
        tflag(),
        st1,
    ) == lir::Outcome::Normal(st1.with_stack(st1.stack.push(lir::Val::I32(tr_t(va))))) by {
        broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

        super::trace::lemma_exec_tag_test(lay, st1, 1, va);
        let s1 = st1.with_stack(st1.stack.push(lir::Val::I32(isint)));
        super::trace::lemma_exec_app(lay, super::lower::tag_test(1), tflag_tail(), st1, s1);
        reveal_with_fuel(super::run::exec, 10);
        assert(super::run::exec(lay, tflag_tail(), s1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I32(tr_t(va)))),
        ));
    }
}

/// The `Not` value block's trace.
pub proof fn lemma_not_val_trace(lay: lir::Layout, va: u64)
    ensures
        super::blocks::val_computes1(lay, not_val(), va, not_word(va)),
{
    lemma_tflag_trace(lay, va);
    let tail = seq![
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Un(lir::UnOp::I64ExtendI32U),
        super::lower::i64c(js::FALSE),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Add)),
    ];
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, not_val(), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) implies super::run::exec(
        lay,
        not_val(),
        st1,
    ) == lir::Outcome::Normal(st1.with_stack(st1.stack.push(lir::Val::I64(not_word(va))))) by {
        broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

        let t = tr_t(va);
        assert(super::run::exec(lay, tflag(), st1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I32(t))),
        ));
        let s1 = st1.with_stack(st1.stack.push(lir::Val::I32(t)));
        super::trace::lemma_exec_app(lay, tflag(), tail, st1, s1);
        super::frame::lemma_add_small(lir::bool_i32(t == 0) as u64, js::FALSE);
        reveal_with_fuel(super::run::exec, 5);
        assert(super::run::exec(lay, tail, s1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I64(not_word(va)))),
        ));
    }
}

/// The guard's flag is non-zero for an int32 or a boolean only.
pub proof fn lemma_tr_g(va: u64)
    ensures
        (tr_g(va) != 0) <==> (js::is_int32(va) || va == js::FALSE || va == js::TRUE),
{
    super::trace::lemma_tag_test(va);
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    let isbool = lir::bool_i32(lir::icmp(lir::ICmp::Eq, 64, (va | 1u64) as int, js::TRUE as int));
    assert(isint == 0 || isint == 1);
    assert(isbool == 0 || isbool == 1);
    lemma_or01(isint, isbool);
    assert(((va | 1u64) == js::TRUE) <==> (va == js::FALSE || va == js::TRUE)) by (bit_vector);
}

/// For an operand the guard lets through, `to_boolean_fast` is `Some`, and
/// the truth flag says which.
pub proof fn lemma_tr_t(va: u64)
    requires
        tr_g(va) != 0,
    ensures
        js::to_boolean_fast(va) is Some,
        (tr_t(va) != 0) <==> (js::to_boolean_fast(va) == Some(true)),
{
    lemma_tr_g(va);
    clazel_js_vm::lemmas::lemma_specials();
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    super::trace::lemma_tag_test(va);
    let nz = lir::bool_i32(lir::bool_i32(super::arith::lo32(va) == 0) == 0);
    let eqt = lir::bool_i32(lir::icmp(lir::ICmp::Eq, 64, va as int, js::TRUE as int));
    assert(isint == 0 || isint == 1);
    assert(nz == 0 || nz == 1);
    assert(eqt == 0 || eqt == 1);
    lemma_and01_local(isint, nz);
    let a = lir::ibin32(lir::IBin::And, isint, nz);
    lemma_or01(a, eqt);
    if js::is_int32(va) {
        super::arith::lemma_payload(va);
        let ia = js::int32_of(va);
        assert(isint == 1);
        assert((super::arith::lo32(va) == 0) <==> (ia == 0)) by (bit_vector)
            requires
                ia == (super::arith::lo32(va) as i32),
        ;
        assert(va != js::TRUE) by {
            assert((va >> 48u64) == 0xFFF9u64 ==> va != js::TRUE) by (bit_vector);
        }
        assert(eqt == 0);
        assert(js::to_boolean_fast(va) == Some(ia != 0));
    } else {
        assert(va == js::FALSE || va == js::TRUE);
        assert(isint == 0) by {
            assert((va == js::FALSE || va == js::TRUE) ==> (va >> 32u64) != super::arith::tag_hi()) by (bit_vector);
        }
        assert(a == 0);
        if va == js::TRUE {
            assert(eqt == 1);
        } else {
            assert(eqt == 0);
        }
    }
}

/// `and` of two flags, non-zero exactly when both are.
pub proof fn lemma_and01_local(e1: u32, e2: u32)
    requires
        e1 == 0 || e1 == 1,
        e2 == 0 || e2 == 1,
    ensures
        ((e1 & e2) != 0) <==> (e1 == 1 && e2 == 1),
        (e1 & e2) == 0 || (e1 & e2) == 1,
{
    assert((((e1 & e2) != 0) <==> (e1 == 1 && e2 == 1)) && ((e1 & e2) == 0 || (e1 & e2) == 1))
        by (bit_vector)
        requires
            e1 == 0 || e1 == 1,
            e2 == 0 || e2 == 1,
    ;
}

/// `Not` on an operand the guard lets through.
pub proof fn lemma_not_sem(s: js::State, dst: nat, src: nat)
    requires
        tr_g(js::reg(s, src)) != 0,
    ensures
        js::fast_path(s, js::Op::Not { dst, src }),
        js::fast_step(s, js::Op::Not { dst, src }) == js::next(
            js::set_reg(s, dst, not_word(js::reg(s, src))),
        ),
{
    let va = js::reg(s, src);
    lemma_tr_t(va);
    let t = tr_t(va);
    assert(js::FALSE + 1 == js::TRUE);
    assert(not_word(va) == js::enc_bool(js::to_boolean_fast(va) != Some(true)));
}

/// A `Not` op: the lowering refines `step`.
pub proof fn lemma_not_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    src: nat,
)
    requires
        super::proofs::pre(c, op, pc, lay, s, st, fuel),
        op == (js::Op::Not { dst, src }),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), src),
        super::lower::lower(c, op, pc, lbl) == lower_not(dst, src, op, pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_tr_simple();
    let va = js::reg(s, src);
    lemma_tr_guard_trace(lay, va);
    if tr_g(va) != 0 {
        lemma_not_sem(s, dst, src);
        lemma_not_val_trace(lay, va);
    }
    super::blocks::lemma_un_op(
        op,
        pc,
        lbl,
        lay,
        s,
        st,
        fuel,
        dst,
        src,
        tr_guard(),
        not_val(),
        tr_g(va),
        not_word(va),
    );
}

/// The rest of a conditional jump, after the guard: from a state with the
/// operand in local 1 and an empty stack, a branch to `lbl` when the
/// (possibly negated) truth flag is non-zero, otherwise a fall through.
pub proof fn lemma_jump_rest(lay: lir::Layout, st: lir::St, va: u64, jf: bool, lbl: nat, fuel: nat)
    requires
        st.stack == Seq::<lir::Val>::empty(),
        st.locals.len() == nlocals(),
        st.locals[1] == lir::Val::I64(va),
        fuel > 20,
    ensures
        ({
            let t = tr_t(va);
            let cond = if jf {
                lir::bool_i32(t == 0)
            } else {
                t
            };
            lir::eval(lay, super::run::chain(jump_rest(jf, lbl)), st, fuel) == (if cond != 0 {
                lir::Outcome::Branch(lbl, st)
            } else {
                lir::Outcome::Normal(st)
            })
        }),
{
    broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

    lemma_tr_simple();
    lemma_tflag_trace(lay, va);
    let t = tr_t(va);
    let ins = jump_rest(jf, lbl);
    super::run::lemma_chain(lay, ins, st, fuel);
    let tl = if jf {
        seq![lir::Instr::Un(lir::UnOp::I32Eqz), lir::Instr::BrIf(lbl)]
    } else {
        seq![lir::Instr::BrIf(lbl)]
    };
    assert(ins == tflag() + tl);
    let s1 = st.with_stack(st.stack.push(lir::Val::I32(t)));
    super::trace::lemma_exec_app(lay, tflag(), tl, st, s1);
    reveal_with_fuel(super::run::exec, 3);
    assert(st.stack.push(lir::Val::I32(t)) =~= seq![lir::Val::I32(t)]);
    assert(lir::below(seq![lir::Val::I32(t)], 1) =~= Seq::<lir::Val>::empty());
}

/// A conditional jump on the truth of a register.
pub proof fn lemma_jump_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    jf: bool,
    cond: nat,
    target: nat,
)
    requires
        super::proofs::pre(c, op, pc, lay, s, st, fuel),
        op == (if jf {
            js::Op::JumpIfFalse { cond, target }
        } else {
            js::Op::JumpIfTrue { cond, target }
        }),
        js::reg_ok(js::cur_code(s), cond),
        super::lower::lower(c, op, pc, lbl) == lower_jump(jf, cond, lbl, op, pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_tr_simple();
    let va = js::reg(s, cond);
    lemma_tr_guard_trace(lay, va);
    let g = tr_g(va);
    super::blocks::lemma_pre_un(lay, s, st, cond, tr_guard(), g);
    let pre = super::blocks::un_pre(cond, tr_guard());
    let st3 = lir::St {
        stack: seq![lir::Val::I32(g)],
        locals: st.locals.update(1, lir::Val::I64(va)),
        mem: st.mem,
    };
    let rest = super::run::chain(jump_rest(jf, lbl));
    super::blocks::lemma_guarded(op, pc, lbl, lay, s, st, st3, pre, rest, g, fuel);
    if g != 0 {
        lemma_tr_t(va);
        let t = tr_t(va);
        let st4 = st3.with_stack(Seq::<lir::Val>::empty());
        assert(rel(lay, s, st4));
        lemma_jump_rest(lay, st4, va, jf, lbl, (fuel - 2) as nat);
        let cnd = if jf {
            lir::bool_i32(t == 0)
        } else {
            t
        };
        let tb = js::to_boolean_fast(va);
        assert(tb is Some);
        assert(jump_target(op) == Some(target));
        let take = if jf {
            tb == Some(false)
        } else {
            tb == Some(true)
        };
        assert((cnd != 0) <==> take);
        assert(js::fast_path(s, op));
        assert(js::fast_step(s, op) == (if take {
            js::jump(s, target)
        } else {
            js::next(s)
        }));
        super::proofs::lemma_rel_pc(lay, s, st4, target);
        super::proofs::lemma_rel_pc(lay, s, st4, s.pc + 1);
    }
}

} // verus!
