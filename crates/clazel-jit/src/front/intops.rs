//! The refinement proof of the small-integer lowerings (add, subtract,
//! multiply): the blocks are simple, the traces of [`super::trace`] give the
//! state after each, and the arithmetic of [`super::arith`] says what the
//! guards and the stored word are.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// An exit chain from a related state exits with the handler's code and
/// `pc`, and the handler's result is `step`'s (by [`handler_complete`]).
pub proof fn lemma_exit_chain(
    op: js::Op,
    pc: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
)
    requires
        rel(lay, s, st),
        fuel > 2,
        s.pc == pc,
        handler_complete(s, op),
    ensures
        ({
            let o = lir::eval(lay, super::run::chain(super::lower::exit_ins(js::op_handler(op), pc)), st, fuel);
            &&& o is Exit
            &&& match o {
                lir::Outcome::Exit(code, vals, st2) => {
                    &&& code == handler_index(js::op_handler(op))
                    &&& vals == seq![lir::Val::I32(s.pc as u32)]
                    &&& rel(lay, s, st2)
                    &&& js::handler(js::op_handler(op), s, op) == js::step(s, op)
                },
                _ => false,
            }
        }),
{
    let h = js::op_handler(op);
    let ins = super::lower::exit_ins(h, pc);
    assert(super::run::all_simple(ins)) by {
        assert forall|i: int| 0 <= i < ins.len() implies super::run::is_simple(#[trigger] ins[i]) by {
            assert(i == 0 || i == 1);
        }
    }
    super::run::lemma_chain(lay, ins, st, fuel);
    reveal_with_fuel(super::run::exec, 3);
    let st1 = st.with_stack(st.stack.push(lir::Val::I32(pc as u32)));
    assert(lir::top(st1.stack, 1) =~= seq![lir::Val::I32(pc as u32)]);
}

/// `if` with the empty block type, the condition alone on the stack: the
/// chosen branch runs from the state with the stack empty, and a normal
/// completion or an exit of the branch is the instruction's.
pub proof fn lemma_if0(
    lay: lir::Layout,
    t: lir::Instr,
    e: lir::Instr,
    st: lir::St,
    c: u32,
    fuel: nat,
)
    requires
        fuel >= 3,
        st.stack == seq![lir::Val::I32(c)],
    ensures
        ({
            let br = if c != 0 {
                t
            } else {
                e
            };
            let o = lir::eval(lay, br, st.with_stack(Seq::<lir::Val>::empty()), (fuel - 2) as nat);
            let r = lir::eval(
                lay,
                lir::Instr::If(super::lower::bt0(), Box::new(t), Box::new(e)),
                st,
                fuel,
            );
            &&& (o is Normal ==> r == o)
            &&& (o is Exit ==> r == o)
        }),
{
    let br = if c != 0 {
        t
    } else {
        e
    };
    let o = lir::eval(lay, br, st.with_stack(Seq::<lir::Val>::empty()), (fuel - 2) as nat);
    assert(lir::below(st.stack, 1) =~= Seq::<lir::Val>::empty());
    assert(lir::top(Seq::<lir::Val>::empty(), 0) =~= Seq::<lir::Val>::empty());
    reveal_with_fuel(lir::eval, 3);
    match o {
        lir::Outcome::Normal(s1) => {
            assert(Seq::<lir::Val>::empty() + s1.stack =~= s1.stack);
            assert(s1.with_stack(s1.stack) == s1);
        },
        _ => {},
    }
}

/// The scratch locals after the operands are loaded, as the traces want them.
pub proof fn lemma_locals_after_operands(s: js::State, l: Seq<lir::Val>, va: u64, vb: u64)
    requires
        locals_rel(s, l),
    ensures
        ({
            let l2 = l.update(1, lir::Val::I64(va)).update(2, lir::Val::I64(vb));
            &&& l2.len() == nlocals()
            &&& l2[1] == lir::Val::I64(va)
            &&& l2[2] == lir::Val::I64(vb)
            &&& locals_rel(s, l2)
        }),
{
    super::trace::lemma_locals_set(s, l, 1, va);
    super::trace::lemma_locals_set(s, l.update(1, lir::Val::I64(va)), 2, vb);
}

/// Two lists of simple instructions make one.
pub proof fn lemma_simple_concat(a: Seq<lir::Instr>, b: Seq<lir::Instr>)
    requires
        super::run::all_simple(a),
        super::run::all_simple(b),
    ensures
        super::run::all_simple(a + b),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies super::run::is_simple(#[trigger] (a + b)[i]) by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// The small literal blocks of the arithmetic lowerings are simple.
pub proof fn lemma_literals_simple(k: nat)
    ensures
        super::run::all_simple(super::lower::tag_test(1)),
        super::run::all_simple(super::lower::tag_test(2)),
        super::run::all_simple(super::lower::sext_local(1)),
        super::run::all_simple(super::lower::sext_local(2)),
        super::run::all_simple(super::lower::fits_ins()),
        super::run::all_simple(super::lower::tagged_ins()),
        super::run::all_simple(seq![lir::Instr::LocalSet(1)]),
        super::run::all_simple(seq![lir::Instr::LocalSet(2)]),
        super::run::all_simple(seq![lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And))]),
        super::run::all_simple(seq![lir::Instr::Bin(lir::BinOp::I64(super::arith::ibin_of(k))), lir::Instr::LocalSet(3)]),
        super::run::all_simple(seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)]),
        super::run::all_simple(
            seq![
                lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
                super::lower::i64c(0),
                super::lower::cmp64(lir::ICmp::LtS),
            ] + seq![
                lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
                lir::Instr::Un(lir::UnOp::I32Eqz),
                lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
            ],
        ),
{
    let g1 = super::lower::tag_test(1);
    assert(super::run::all_simple(g1)) by {
        assert forall|i: int| 0 <= i < g1.len() implies super::run::is_simple(#[trigger] g1[i]) by {
            assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4);
        }
    }
    let g2 = super::lower::tag_test(2);
    assert(super::run::all_simple(g2)) by {
        assert forall|i: int| 0 <= i < g2.len() implies super::run::is_simple(#[trigger] g2[i]) by {
            assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4);
        }
    }
    let x1 = super::lower::sext_local(1);
    assert(super::run::all_simple(x1)) by {
        assert forall|i: int| 0 <= i < x1.len() implies super::run::is_simple(#[trigger] x1[i]) by {
            assert(i == 0 || i == 1 || i == 2);
        }
    }
    let x2 = super::lower::sext_local(2);
    assert(super::run::all_simple(x2)) by {
        assert forall|i: int| 0 <= i < x2.len() implies super::run::is_simple(#[trigger] x2[i]) by {
            assert(i == 0 || i == 1 || i == 2);
        }
    }
    let f = super::lower::fits_ins();
    assert(super::run::all_simple(f)) by {
        assert forall|i: int| 0 <= i < f.len() implies super::run::is_simple(#[trigger] f[i]) by {
            assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4);
        }
    }
    let t = super::lower::tagged_ins();
    assert(super::run::all_simple(t)) by {
        assert forall|i: int| 0 <= i < t.len() implies super::run::is_simple(#[trigger] t[i]) by {
            assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4);
        }
    }
    let s1 = seq![lir::Instr::LocalSet(1)];
    assert(super::run::all_simple(s1)) by {
        assert forall|i: int| 0 <= i < s1.len() implies super::run::is_simple(#[trigger] s1[i]) by {
            assert(i == 0);
        }
    }
    let s2 = seq![lir::Instr::LocalSet(2)];
    assert(super::run::all_simple(s2)) by {
        assert forall|i: int| 0 <= i < s2.len() implies super::run::is_simple(#[trigger] s2[i]) by {
            assert(i == 0);
        }
    }
    let a1 = seq![lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And))];
    assert(super::run::all_simple(a1)) by {
        assert forall|i: int| 0 <= i < a1.len() implies super::run::is_simple(#[trigger] a1[i]) by {
            assert(i == 0);
        }
    }
    let c3 = seq![lir::Instr::Bin(lir::BinOp::I64(super::arith::ibin_of(k))), lir::Instr::LocalSet(3)];
    assert(super::run::all_simple(c3)) by {
        assert forall|i: int| 0 <= i < c3.len() implies super::run::is_simple(#[trigger] c3[i]) by {
            assert(i == 0 || i == 1);
        }
    }
    let e3 = seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)];
    assert(super::run::all_simple(e3)) by {
        assert forall|i: int| 0 <= i < e3.len() implies super::run::is_simple(#[trigger] e3[i]) by {
            assert(i == 0 || i == 1);
        }
    }
    let ta = seq![lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)), super::lower::i64c(0), super::lower::cmp64(lir::ICmp::LtS)];
    let tb = seq![
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ];
    assert(super::run::all_simple(ta)) by {
        assert forall|i: int| 0 <= i < ta.len() implies super::run::is_simple(#[trigger] ta[i]) by {
            assert(i == 0 || i == 1 || i == 2);
        }
    }
    assert(super::run::all_simple(tb)) by {
        assert forall|i: int| 0 <= i < tb.len() implies super::run::is_simple(#[trigger] tb[i]) by {
            assert(i == 0 || i == 1 || i == 2);
        }
    }
    lemma_simple_concat(ta, tb);
}

/// The blocks of an arithmetic lowering are simple, and of known length.
pub proof fn lemma_arith_blocks_simple(k: nat, a: nat, b: nat, dst: nat)
    requires
        k <= 2,
    ensures
        super::run::all_simple(super::lower::operands_ins(a, b) + super::lower::guard1_ins()),
        (super::lower::operands_ins(a, b) + super::lower::guard1_ins()).len() == 23,
        super::run::all_simple(super::lower::compute_ins(k) + super::lower::guard2_ins(k)),
        (super::lower::compute_ins(k) + super::lower::guard2_ins(k)).len() <= 27,
        super::run::all_simple(super::lower::store_ins(reg_off(dst), super::lower::tagged_ins())),
        super::lower::store_ins(reg_off(dst), super::lower::tagged_ins()).len() == 10,
{
    lemma_literals_simple(k);
    super::proofs::lemma_blocks_simple(reg_off(a), 0);
    super::proofs::lemma_blocks_simple(reg_off(b), 0);
    super::proofs::lemma_blocks_simple(reg_off(dst), 0);
    let s1 = seq![lir::Instr::LocalSet(1)];
    let s2 = seq![lir::Instr::LocalSet(2)];
    lemma_simple_concat(super::lower::load_ins(reg_off(a)), s1);
    lemma_simple_concat(super::lower::load_ins(reg_off(a)) + s1, super::lower::load_ins(reg_off(b)));
    lemma_simple_concat((super::lower::load_ins(reg_off(a)) + s1) + super::lower::load_ins(reg_off(b)), s2);
    assert(super::lower::operands_ins(a, b) =~= ((super::lower::load_ins(reg_off(a)) + s1) + super::lower::load_ins(reg_off(b))) + s2);
    lemma_simple_concat(super::lower::tag_test(1), super::lower::tag_test(2));
    lemma_simple_concat(
        super::lower::tag_test(1) + super::lower::tag_test(2),
        seq![lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And))],
    );
    assert(super::lower::guard1_ins() =~= (super::lower::tag_test(1) + super::lower::tag_test(2)) + seq![
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ]);
    lemma_simple_concat(super::lower::operands_ins(a, b), super::lower::guard1_ins());
    // compute and guard2
    lemma_simple_concat(super::lower::sext_local(1), super::lower::sext_local(2));
    let c3 = seq![lir::Instr::Bin(lir::BinOp::I64(super::arith::ibin_of(k))), lir::Instr::LocalSet(3)];
    lemma_simple_concat(super::lower::sext_local(1) + super::lower::sext_local(2), c3);
    assert(super::lower::compute_ins(k) =~= (super::lower::sext_local(1) + super::lower::sext_local(2)) + c3);
    let e3 = seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)];
    let tail = seq![
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
        super::lower::i64c(0),
        super::lower::cmp64(lir::ICmp::LtS),
    ] + seq![
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ];
    if k == 2 {
        lemma_simple_concat(e3, super::lower::sext_local(1));
        lemma_simple_concat(e3 + super::lower::sext_local(1), super::lower::sext_local(2));
        lemma_simple_concat((e3 + super::lower::sext_local(1)) + super::lower::sext_local(2), tail);
        assert(super::lower::mul_tail_ins() =~= ((e3 + super::lower::sext_local(1)) + super::lower::sext_local(2)) + tail);
        lemma_simple_concat(super::lower::fits_ins(), super::lower::mul_tail_ins());
    }
    assert(super::run::all_simple(super::lower::guard2_ins(k)));
    assert(super::lower::guard2_ins(k).len() <= 19);
    lemma_simple_concat(super::lower::compute_ins(k), super::lower::guard2_ins(k));
    // the store
    let sto = seq![lir::Instr::Store { region: 0, ty: lir::Ty::I64 }];
    assert(super::run::all_simple(sto)) by {
        assert forall|i: int| 0 <= i < sto.len() implies super::run::is_simple(#[trigger] sto[i]) by {
            assert(i == 0);
        }
    }
    lemma_simple_concat(super::lower::addr_ins(reg_off(dst)), super::lower::tagged_ins());
    lemma_simple_concat(super::lower::addr_ins(reg_off(dst)) + super::lower::tagged_ins(), sto);
}

/// The facts about `op` and `s` the three stages share.
pub open spec fn arith_ctx(
    op: js::Op,
    s: js::State,
    k: nat,
    dst: nat,
    a: nat,
    b: nat,
) -> bool {
    &&& k <= 2
    &&& jump_target(op) is None
    &&& js::reg_ok(js::cur_code(s), dst)
    &&& js::reg_ok(js::cur_code(s), a)
    &&& js::reg_ok(js::cur_code(s), b)
    &&& js::fast_path(s, op) <==> (js::is_number(js::reg(s, a)) && js::is_number(js::reg(s, b)))
    &&& js::fast_step(s, op) == js::next(
        js::set_reg(s, dst, super::arith::spec_arith(k, js::reg(s, a), js::reg(s, b))),
    )
}

/// The last stage: the result is an int32, so the tagged word is stored.
pub proof fn lemma_arith_store(
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st4: lir::St,
    fuel: nat,
    k: nat,
    dst: nat,
    a: nat,
    b: nat,
)
    requires
        arith_ctx(op, s, k, dst, a, b),
        js::state_wf(s),
        rel(lay, s, st4),
        st4.stack == Seq::<lir::Val>::empty(),
        fuel >= 12,
        s.pc == pc,
        js::is_int32(js::reg(s, a)),
        js::is_int32(js::reg(s, b)),
        st4.locals[3] == lir::Val::I64(super::arith::s64(k, js::reg(s, a), js::reg(s, b))),
        super::arith::int_ok(k, js::int32_of(js::reg(s, a)) as int, js::int32_of(js::reg(s, b)) as int),
    ensures
        outcome_refines(
            lay,
            s,
            op,
            lbl,
            lir::eval(lay, super::run::chain(super::lower::store_ins(reg_off(dst), super::lower::tagged_ins())), st4, fuel),
        ),
{
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    lemma_arith_blocks_simple(k, a, b, dst);
    super::proofs::lemma_reg_slot_ok(s, dst);
    super::arith::lemma_arith_facts(k, va, vb);
    let sum = super::arith::s64(k, va, vb);
    let v = super::arith::tagged(sum);
    assert(v == super::arith::spec_arith(k, va, vb));
    let off = reg_off(dst);
    let sa = st4.with_stack(st4.stack.push(lir::Val::I64((8 * s.fp + off) as u64)));
    reveal_with_fuel(super::run::exec, 6);
    let m1 = sa.with_stack(sa.stack.push(lir::Val::I64(sum)));
    let m2 = sa.with_stack(sa.stack.push(lir::Val::I64(sum)).push(lir::Val::I64(0xFFFF_FFFF)));
    let m3 = sa.with_stack(sa.stack.push(lir::Val::I64(sum & 0xFFFF_FFFFu64)));
    let m4 = sa.with_stack(
        sa.stack.push(lir::Val::I64(sum & 0xFFFF_FFFFu64)).push(lir::Val::I64(super::arith::tag_bits())),
    );
    let mid = sa.with_stack(sa.stack.push(lir::Val::I64(v)));
    assert(lir::below(m2.stack, 2) =~= sa.stack);
    assert(lir::below(m4.stack, 2) =~= sa.stack);
    assert(super::run::exec(lay, super::lower::tagged_ins(), sa) == lir::Outcome::Normal(mid));
    super::frame::lemma_exec_store(lay, s, st4, off, super::lower::tagged_ins(), v, mid);
    let j = (s.fp + off / 8) as int;
    let s2 = js::fast_step(s, op);
    assert(s2.region == s.region.update(j, v));
    assert(s2 == js::State { pc: s.pc + 1, ..js::State { region: s.region.update(j, v), ..s } });
    let ins3 = super::lower::store_ins(off, super::lower::tagged_ins());
    super::run::lemma_chain(lay, ins3, st4, fuel);
    let st6 = lir::St {
        stack: st4.stack,
        locals: mid.locals,
        mem: lir::write_le(st4.mem, slot_addr(lay, j), v as nat, 8),
    };
    super::proofs::lemma_rel_pc(lay, js::State { region: s.region.update(j, v), ..s }, st6, s.pc + 1);
}

/// The second stage, with both operands int32: compute, test the result,
/// then store or exit.
pub proof fn lemma_arith_inner(
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st2: lir::St,
    fuel: nat,
    k: nat,
    dst: nat,
    a: nat,
    b: nat,
)
    requires
        arith_ctx(op, s, k, dst, a, b),
        js::state_wf(s),
        rel(lay, s, st2),
        st2.stack == Seq::<lir::Val>::empty(),
        fuel >= 100,
        s.pc == pc,
        handler_complete(s, op),
        st2.locals[1] == lir::Val::I64(js::reg(s, a)),
        st2.locals[2] == lir::Val::I64(js::reg(s, b)),
        js::is_int32(js::reg(s, a)),
        js::is_int32(js::reg(s, b)),
    ensures
        ({
            let h = js::op_handler(op);
            let exit = super::run::chain(super::lower::exit_ins(h, pc));
            let store = super::run::chain(super::lower::store_ins(reg_off(dst), super::lower::tagged_ins()));
            let inner = super::run::chain((super::lower::compute_ins(k) + super::lower::guard2_ins(k)).push(lir::Instr::If(
                super::lower::bt0(),
                Box::new(store),
                Box::new(exit),
            )));
            outcome_refines(lay, s, op, lbl, lir::eval(lay, inner, st2, fuel))
        }),
{
    let h = js::op_handler(op);
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    lemma_arith_blocks_simple(k, a, b, dst);
    let exit = super::run::chain(super::lower::exit_ins(h, pc));
    let store = super::run::chain(super::lower::store_ins(reg_off(dst), super::lower::tagged_ins()));
    let if2 = lir::Instr::If(super::lower::bt0(), Box::new(store), Box::new(exit));
    let ins2 = super::lower::compute_ins(k) + super::lower::guard2_ins(k);
    super::run::lemma_chain_last(lay, ins2, if2, st2, fuel);
    super::trace::lemma_compute_trace(lay, st2, k, va, vb);
    let sum = super::arith::s64(k, va, vb);
    let st4 = lir::St {
        stack: Seq::<lir::Val>::empty(),
        locals: st2.locals.update(3, lir::Val::I64(sum)),
        mem: st2.mem,
    };
    super::trace::lemma_locals_set(s, st2.locals, 3, sum);
    assert(rel(lay, s, st4));
    super::trace::lemma_exec_app(lay, super::lower::compute_ins(k), super::lower::guard2_ins(k), st2, st4);
    super::trace::lemma_guard2_trace(lay, st4, k, va, vb);
    let g2 = super::arith::guard2(k, va, vb);
    let st5 = st4.with_stack(seq![lir::Val::I32(g2)]);
    assert(super::run::exec(lay, ins2, st2) == lir::Outcome::Normal(st5));
    let f3 = (fuel - ins2.len()) as nat;
    lemma_if0(lay, store, exit, st5, g2, f3);
    assert(st5.with_stack(Seq::<lir::Val>::empty()) == st4);
    super::arith::lemma_arith_facts(k, va, vb);
    if g2 == 0 {
        lemma_exit_chain(op, pc, lay, s, st4, (f3 - 2) as nat);
        let o = lir::eval(lay, exit, st4, (f3 - 2) as nat);
        assert(o is Exit);
    } else {
        lemma_arith_store(op, pc, lbl, lay, s, st4, (f3 - 2) as nat, k, dst, a, b);
        let o = lir::eval(lay, store, st4, (f3 - 2) as nat);
        assert(o is Normal || o is Exit);
    }
}

/// Small-integer add, subtract or multiply of registers `a` and `b` into
/// `dst`: two guards and an exit, then a tagged store.
pub proof fn lemma_arith_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    k: nat,
    dst: nat,
    a: nat,
    b: nat,
)
    requires
        super::proofs::pre(c, op, pc, lay, s, st, fuel),
        arith_ctx(op, s, k, dst, a, b),
        super::lower::lower(c, op, pc, lbl) == super::lower::lower_arith(k, dst, a, b, js::op_handler(op), pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    let h = js::op_handler(op);
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    lemma_arith_blocks_simple(k, a, b, dst);
    let exit = super::run::chain(super::lower::exit_ins(h, pc));
    let store = super::run::chain(super::lower::store_ins(reg_off(dst), super::lower::tagged_ins()));
    let inner = super::run::chain((super::lower::compute_ins(k) + super::lower::guard2_ins(k)).push(lir::Instr::If(
        super::lower::bt0(),
        Box::new(store),
        Box::new(exit),
    )));
    let if1 = lir::Instr::If(super::lower::bt0(), Box::new(inner), Box::new(exit));
    let pre1 = super::lower::operands_ins(a, b) + super::lower::guard1_ins();
    assert(st.locals.len() == nlocals());
    super::run::lemma_chain_last(lay, pre1, if1, st, fuel);
    super::trace::lemma_operands_trace(lay, s, st, a, b);
    let st2 = lir::St {
        stack: Seq::<lir::Val>::empty(),
        locals: st.locals.update(1, lir::Val::I64(va)).update(2, lir::Val::I64(vb)),
        mem: st.mem,
    };
    lemma_locals_after_operands(s, st.locals, va, vb);
    super::trace::lemma_exec_app(lay, super::lower::operands_ins(a, b), super::lower::guard1_ins(), st, st2);
    super::trace::lemma_guard1_trace(lay, st2, va, vb);
    let g1 = lir::ibin32(
        lir::IBin::And,
        lir::bool_i32((va >> 32u64) == super::arith::tag_hi()),
        lir::bool_i32((vb >> 32u64) == super::arith::tag_hi()),
    );
    let st3 = st2.with_stack(seq![lir::Val::I32(g1)]);
    assert(super::run::exec(lay, pre1, st) == lir::Outcome::Normal(st3));
    let f1 = (fuel - 23) as nat;
    lemma_if0(lay, inner, exit, st3, g1, f1);
    assert(st3.with_stack(Seq::<lir::Val>::empty()) == st2);
    if g1 == 0 {
        lemma_exit_chain(op, pc, lay, s, st2, (f1 - 2) as nat);
        let o = lir::eval(lay, exit, st2, (f1 - 2) as nat);
        assert(o is Exit);
    } else {
        assert(js::is_int32(va) && js::is_int32(vb));
        assert(js::is_number(va) && js::is_number(vb));
        lemma_arith_inner(op, pc, lbl, lay, s, st2, (f1 - 2) as nat, k, dst, a, b);
        let o = lir::eval(lay, inner, st2, (f1 - 2) as nat);
        assert(o is Normal || o is Exit);
    }
}

} // verus!
