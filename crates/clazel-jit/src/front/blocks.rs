//! The generic pieces the second slice's lowerings are built from, and the
//! lemmas about them that do not depend on the op.
//!
//! # Shape of a lowering
//!
//! A lowering is a *prefix* of simple instructions that leaves a guard flag
//! (an `i32`) on the stack, then [`gx`], which falls through when the flag
//! is non-zero and exits to the op's handler otherwise, then the *rest*
//! ([`guarded`]). Guards nest by making the rest another [`guarded`]. This is
//! the form of the first slice's `if`-based lowerings with the exit moved
//! out of an `if` block: the rest then runs at the lowering's own label depth
//! (a `br_if` in it targets the same label the jumps of the first slice do),
//! and the proof is one lemma ([`lemma_guarded`]) instead of one per nesting.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `below` of a stack with one value pushed.
pub broadcast proof fn lemma_below_push1<A>(s: Seq<A>, x: A)
    ensures
        #[trigger] lir::below(s.push(x), 1) == s,
{
    assert(lir::below(s.push(x), 1) =~= s);
}

/// `below` of a stack with two values pushed.
pub broadcast proof fn lemma_below_push2<A>(s: Seq<A>, x: A, y: A)
    ensures
        #[trigger] lir::below(s.push(x).push(y), 2) == s,
{
    assert(lir::below(s.push(x).push(y), 2) =~= s);
}

/// `drop_last` of a stack with one value pushed.
pub broadcast proof fn lemma_drop_last_push<A>(s: Seq<A>, x: A)
    ensures
        #[trigger] s.push(x).drop_last() == s,
{
    assert(s.push(x).drop_last() =~= s);
}

/// The stack facts a straight-line block's proof needs.
pub broadcast group stack_shape {
    lemma_below_push1,
    lemma_below_push2,
    lemma_drop_last_push,
}

/// The guard's exit: fall through (`Nop`) when the flag on the stack is
/// non-zero, exit to the handler of `op` (from the op at `pc`) otherwise.
pub open spec fn gx(op: js::Op, pc: nat) -> lir::Instr {
    lir::Instr::If(
        super::lower::bt0(),
        Box::new(lir::Instr::Nop),
        Box::new(super::run::chain(super::lower::exit_ins(js::op_handler(op), pc))),
    )
}

/// The prefix `p` (simple instructions leaving the guard flag), the guard's
/// exit, then `rest`.
pub open spec fn guarded(p: Seq<lir::Instr>, op: js::Op, pc: nat, rest: lir::Instr) -> lir::Instr {
    super::run::then(super::run::chain(p), super::run::then(gx(op, pc), rest))
}

/// The meaning of [`guarded`]: when the prefix leaves a zero flag the
/// outcome is an exit that refines `step`; otherwise `rest` runs from the
/// state with the flag popped, with two units less fuel.
pub proof fn lemma_guarded(
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    st2: lir::St,
    p: Seq<lir::Instr>,
    rest: lir::Instr,
    g: u32,
    fuel: nat,
)
    requires
        rel(lay, s, st2),
        s.pc == pc,
        handler_complete(s, op),
        super::run::all_simple(p),
        fuel > p.len() + 8,
        super::run::exec(lay, p, st) == lir::Outcome::Normal(st2),
        st2.stack == seq![lir::Val::I32(g)],
    ensures
        g == 0 ==> outcome_refines(lay, s, op, lbl, lir::eval(lay, guarded(p, op, pc, rest), st, fuel)),
        g != 0 ==> lir::eval(lay, guarded(p, op, pc, rest), st, fuel) == lir::eval(
            lay,
            rest,
            st2.with_stack(Seq::<lir::Val>::empty()),
            (fuel - 2) as nat,
        ),
{
    super::run::lemma_chain(lay, p, st, (fuel - 1) as nat);
    let exit = super::run::chain(super::lower::exit_ins(js::op_handler(op), pc));
    let st3 = st2.with_stack(Seq::<lir::Val>::empty());
    reveal_with_fuel(lir::eval, 3);
    super::intops::lemma_if0(lay, lir::Instr::Nop, exit, st2, g, (fuel - 2) as nat);
    if g == 0 {
        assert(rel(lay, s, st3));
        super::intops::lemma_exit_chain(op, pc, lay, s, st3, (fuel - 4) as nat);
    } else {
        assert(lir::eval(lay, lir::Instr::Nop, st3, (fuel - 4) as nat) == lir::Outcome::Normal(st3));
    }
}

/// `eval` of a chain of simple instructions whose last element is not
/// needed by the caller: a thin wrapper that restates [`super::run::lemma_chain`]
/// for a chain that is the whole `rest` of a guard.
pub proof fn lemma_rest_chain(lay: lir::Layout, ins: Seq<lir::Instr>, st: lir::St, fuel: nat)
    requires
        super::run::all_simple(ins),
        fuel > ins.len(),
    ensures
        lir::eval(lay, super::run::chain(ins), st, fuel) == super::run::exec(lay, ins, st),
{
    super::run::lemma_chain(lay, ins, st, fuel);
}

/// A value block computes the word `w` from the operand words `va` and `vb`
/// held in scratch locals 1 and 2: from any state with those locals it
/// pushes `w` and changes nothing else.
pub open spec fn val_computes(lay: lir::Layout, val: Seq<lir::Instr>, va: u64, vb: u64, w: u64) -> bool {
    forall|st1: lir::St|
        #![trigger super::run::exec(lay, val, st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) && st1.locals[2]
            == lir::Val::I64(vb) ==> super::run::exec(lay, val, st1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I64(w))),
        )
}

/// A value block computes the word `w` from the one operand word `va` held
/// in scratch local 1.
pub open spec fn val_computes1(lay: lir::Layout, val: Seq<lir::Instr>, va: u64, w: u64) -> bool {
    forall|st1: lir::St|
        #![trigger super::run::exec(lay, val, st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va)
            ==> super::run::exec(lay, val, st1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I64(w))),
        )
}

/// A store of `v` in register `dst` by the value block `val`, after which the
/// op falls through. [`super::proofs::lemma_store_reg_outcome`] with a fuel
/// bound that a nested lowering can meet.
pub proof fn lemma_store_outcome(
    op: js::Op,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    val: Seq<lir::Instr>,
    v: u64,
)
    requires
        rel(lay, s, st),
        st.stack == Seq::<lir::Val>::empty(),
        js::state_wf(s),
        js::reg_ok(js::cur_code(s), dst),
        super::run::all_simple(val),
        val.len() < 40,
        fuel > 6 + val.len(),
        js::fast_path(s, op),
        js::fast_step(s, op) == js::next(js::set_reg(s, dst, v)),
        ({
            let sa = st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)));
            super::run::exec(lay, val, sa) == lir::Outcome::Normal(
                sa.with_stack(sa.stack.push(lir::Val::I64(v))),
            )
        }),
    ensures
        outcome_refines(
            lay,
            s,
            op,
            lbl,
            lir::eval(lay, super::run::chain(super::lower::store_ins(reg_off(dst), val)), st, fuel),
        ),
{
    super::proofs::lemma_reg_slot_ok(s, dst);
    let off = reg_off(dst);
    let ins = super::lower::store_ins(off, val);
    super::proofs::lemma_blocks_simple(off, 0);
    assert(super::run::all_simple(ins)) by {
        assert forall|i: int| 0 <= i < ins.len() implies super::run::is_simple(#[trigger] ins[i]) by {
            if i < 4 {
                assert(ins[i] == super::lower::addr_ins(off)[i]);
            } else if i < 4 + val.len() {
                assert(ins[i] == val[i - 4]);
            } else {
                assert(i == 4 + val.len());
            }
        }
    }
    assert(ins.len() == 5 + val.len());
    super::run::lemma_chain(lay, ins, st, fuel);
    let sa = st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)));
    let mid = sa.with_stack(sa.stack.push(lir::Val::I64(v)));
    assert(locals_rel(s, mid.locals));
    super::frame::lemma_exec_store(lay, s, st, off, val, v, mid);
    let j = (s.fp + off / 8) as int;
    let s2 = js::fast_step(s, op);
    assert(s2.region == s.region.update(j, v));
    assert(s2 == js::State { pc: s.pc + 1, ..js::State { region: s.region.update(j, v), ..s } });
    super::proofs::lemma_rel_pc(lay, js::State { region: s.region.update(j, v), ..s }, lir::St {
        stack: st.stack,
        locals: mid.locals,
        mem: lir::write_le(st.mem, slot_addr(lay, j), v as nat, 8),
    }, s.pc + 1);
}

/// The binary prefix: both registers loaded into scratch locals 1 and 2 and
/// the flag "both are int32 words" left on the stack.
pub proof fn lemma_pre1(lay: lir::Layout, s: js::State, st: lir::St, a: nat, b: nat)
    requires
        rel(lay, s, st),
        st.stack == Seq::<lir::Val>::empty(),
        js::state_wf(s),
        js::reg_ok(js::cur_code(s), a),
        js::reg_ok(js::cur_code(s), b),
    ensures
        ({
            let va = js::reg(s, a);
            let vb = js::reg(s, b);
            let pre = super::lower::operands_ins(a, b) + super::lower::guard1_ins();
            let g1 = lir::ibin32(
                lir::IBin::And,
                lir::bool_i32((va >> 32u64) == super::arith::tag_hi()),
                lir::bool_i32((vb >> 32u64) == super::arith::tag_hi()),
            );
            let st3 = lir::St {
                stack: seq![lir::Val::I32(g1)],
                locals: st.locals.update(1, lir::Val::I64(va)).update(2, lir::Val::I64(vb)),
                mem: st.mem,
            };
            &&& super::run::all_simple(pre)
            &&& pre.len() == 23
            &&& super::run::exec(lay, pre, st) == lir::Outcome::Normal(st3)
            &&& (g1 != 0) <==> (js::is_int32(va) && js::is_int32(vb))
            &&& rel(lay, s, st3)
            &&& st3.locals.len() == nlocals()
            &&& st3.locals[1] == lir::Val::I64(va)
            &&& st3.locals[2] == lir::Val::I64(vb)
        }),
{
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    super::intops::lemma_arith_blocks_simple(0, a, b, 0);
    super::trace::lemma_operands_trace(lay, s, st, a, b);
    let st2 = lir::St {
        stack: Seq::<lir::Val>::empty(),
        locals: st.locals.update(1, lir::Val::I64(va)).update(2, lir::Val::I64(vb)),
        mem: st.mem,
    };
    super::intops::lemma_locals_after_operands(s, st.locals, va, vb);
    super::trace::lemma_exec_app(lay, super::lower::operands_ins(a, b), super::lower::guard1_ins(), st, st2);
    super::trace::lemma_guard1_trace(lay, st2, va, vb);
}

/// A binary lowering: the prefix of [`super::blocks::lemma_pre1`], the guard
/// exit, then a store of the value block's word in `dst`.
pub open spec fn lower_bin(val: Seq<lir::Instr>, dst: nat, a: nat, b: nat, op: js::Op, pc: nat) -> lir::Instr {
    guarded(
        super::lower::operands_ins(a, b) + super::lower::guard1_ins(),
        op,
        pc,
        super::run::chain(super::lower::store_ins(reg_off(dst), val)),
    )
}

/// A binary lowering of two int32 operands whose value block computes the
/// word `w` refines `step`: the guard sends everything but two int32 words to
/// the handler (whose result is `step`'s by [`handler_complete`]), and for two
/// int32 words the op's fast path holds and its result is `w` in `dst`.
pub proof fn lemma_bin_op(
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    a: nat,
    b: nat,
    val: Seq<lir::Instr>,
    w: u64,
)
    requires
        fuel >= 100,
        rel(lay, s, st),
        st.stack == Seq::<lir::Val>::empty(),
        js::state_wf(s),
        s.pc == pc,
        handler_complete(s, op),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), a),
        js::reg_ok(js::cur_code(s), b),
        super::run::all_simple(val),
        val.len() < 40,
        js::is_int32(js::reg(s, a)) && js::is_int32(js::reg(s, b)) ==> js::fast_path(s, op)
            && js::fast_step(s, op) == js::next(js::set_reg(s, dst, w)),
        js::is_int32(js::reg(s, a)) && js::is_int32(js::reg(s, b)) ==> val_computes(
            lay,
            val,
            js::reg(s, a),
            js::reg(s, b),
            w,
        ),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, lower_bin(val, dst, a, b, op, pc), st, fuel)),
{
    lemma_pre1(lay, s, st, a, b);
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let pre = super::lower::operands_ins(a, b) + super::lower::guard1_ins();
    let g1 = lir::ibin32(
        lir::IBin::And,
        lir::bool_i32((va >> 32u64) == super::arith::tag_hi()),
        lir::bool_i32((vb >> 32u64) == super::arith::tag_hi()),
    );
    let st3 = lir::St {
        stack: seq![lir::Val::I32(g1)],
        locals: st.locals.update(1, lir::Val::I64(va)).update(2, lir::Val::I64(vb)),
        mem: st.mem,
    };
    let rest = super::run::chain(super::lower::store_ins(reg_off(dst), val));
    lemma_guarded(op, pc, lbl, lay, s, st, st3, pre, rest, g1, fuel);
    if g1 != 0 {
        let st4 = st3.with_stack(Seq::<lir::Val>::empty());
        assert(rel(lay, s, st4));
        assert(js::is_int32(va) && js::is_int32(vb));
        super::proofs::lemma_reg_slot_ok(s, dst);
        let sa = st4.with_stack(st4.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)));
        assert(sa.locals == st3.locals);
        assert(sa.locals.len() == nlocals());
        assert(sa.locals[1] == lir::Val::I64(va));
        assert(sa.locals[2] == lir::Val::I64(vb));
        assert(super::run::exec(lay, val, sa) == lir::Outcome::Normal(
            sa.with_stack(sa.stack.push(lir::Val::I64(w))),
        ));
        lemma_store_outcome(op, lbl, lay, s, st4, (fuel - 2) as nat, dst, val, w);
    }
}

/// A flag block computes the `i32` flag `g` from the operand word `va` held
/// in scratch local 1: it pushes `g` and changes nothing else.
pub open spec fn flag_computes(lay: lir::Layout, fl: Seq<lir::Instr>, va: u64, g: u32) -> bool {
    forall|st1: lir::St|
        #![trigger super::run::exec(lay, fl, st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va)
            ==> super::run::exec(lay, fl, st1) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I32(g))),
        )
}

/// The unary prefix: the register loaded into scratch local 1, then the flag
/// block `fl`.
pub open spec fn un_pre(src: nat, fl: Seq<lir::Instr>) -> Seq<lir::Instr> {
    super::lower::load_ins(reg_off(src)) + (seq![lir::Instr::LocalSet(1)] + fl)
}

/// A unary lowering: the unary prefix, the guard exit, then a store of the
/// value block's word in `dst`.
pub open spec fn lower_un(
    fl: Seq<lir::Instr>,
    val: Seq<lir::Instr>,
    dst: nat,
    src: nat,
    op: js::Op,
    pc: nat,
) -> lir::Instr {
    guarded(
        un_pre(src, fl),
        op,
        pc,
        super::run::chain(super::lower::store_ins(reg_off(dst), val)),
    )
}

/// The unary prefix: leaves the flag `g` on the stack, with the operand in
/// local 1.
pub proof fn lemma_pre_un(
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    src: nat,
    fl: Seq<lir::Instr>,
    g: u32,
)
    requires
        rel(lay, s, st),
        st.stack == Seq::<lir::Val>::empty(),
        js::state_wf(s),
        js::reg_ok(js::cur_code(s), src),
        super::run::all_simple(fl),
        fl.len() < 40,
        flag_computes(lay, fl, js::reg(s, src), g),
    ensures
        ({
            let v = js::reg(s, src);
            let pre = un_pre(src, fl);
            let st3 = lir::St {
                stack: seq![lir::Val::I32(g)],
                locals: st.locals.update(1, lir::Val::I64(v)),
                mem: st.mem,
            };
            &&& super::run::all_simple(pre)
            &&& pre.len() == 6 + fl.len()
            &&& super::run::exec(lay, pre, st) == lir::Outcome::Normal(st3)
            &&& rel(lay, s, st3)
            &&& st3.locals.len() == nlocals()
            &&& st3.locals[1] == lir::Val::I64(v)
        }),
{
    broadcast use stack_shape;

    let v = js::reg(s, src);
    super::proofs::lemma_reg_slot_ok(s, src);
    super::proofs::lemma_blocks_simple(reg_off(src), 0);
    let l = super::lower::load_ins(reg_off(src));
    let set1 = seq![lir::Instr::LocalSet(1)];
    assert(super::run::all_simple(set1)) by {
        assert forall|i: int| 0 <= i < set1.len() implies super::run::is_simple(#[trigger] set1[i]) by {
            assert(i == 0);
        }
    }
    super::intops::lemma_simple_concat(set1, fl);
    super::intops::lemma_simple_concat(l, set1 + fl);
    super::frame::lemma_exec_load(lay, s, st, reg_off(src));
    let sl = st.with_stack(st.stack.push(lir::Val::I64(v)));
    super::trace::lemma_exec_app(lay, l, set1 + fl, st, sl);
    reveal_with_fuel(super::run::exec, 2);
    let loc = st.locals.update(1, lir::Val::I64(v));
    let sb = lir::St { stack: Seq::<lir::Val>::empty(), locals: loc, mem: st.mem };
    assert(super::run::exec(lay, set1, sl) == lir::Outcome::Normal(sb));
    super::trace::lemma_exec_app(lay, set1, fl, sl, sb);
    super::trace::lemma_locals_set(s, st.locals, 1, v);
    assert(rel(lay, s, sb));
    assert(sb.locals.len() == nlocals());
    assert(sb.locals[1] == lir::Val::I64(v));
    assert(super::run::exec(lay, fl, sb) == lir::Outcome::Normal(sb.with_stack(sb.stack.push(lir::Val::I32(g)))));
    assert(sb.stack.push(lir::Val::I32(g)) =~= seq![lir::Val::I32(g)]);
}

/// A unary lowering whose flag block computes `g` and whose value block
/// computes `w` refines `step`: a zero flag exits to the handler, otherwise
/// the op's fast path holds and its result is `w` in `dst`.
pub proof fn lemma_un_op(
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    src: nat,
    fl: Seq<lir::Instr>,
    val: Seq<lir::Instr>,
    g: u32,
    w: u64,
)
    requires
        fuel >= 100,
        rel(lay, s, st),
        st.stack == Seq::<lir::Val>::empty(),
        js::state_wf(s),
        s.pc == pc,
        handler_complete(s, op),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), src),
        super::run::all_simple(fl),
        fl.len() < 40,
        super::run::all_simple(val),
        val.len() < 40,
        flag_computes(lay, fl, js::reg(s, src), g),
        g != 0 ==> js::fast_path(s, op) && js::fast_step(s, op) == js::next(js::set_reg(s, dst, w)),
        g != 0 ==> val_computes1(lay, val, js::reg(s, src), w),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, lower_un(fl, val, dst, src, op, pc), st, fuel)),
{
    lemma_pre_un(lay, s, st, src, fl, g);
    let v = js::reg(s, src);
    let pre = un_pre(src, fl);
    let st3 = lir::St {
        stack: seq![lir::Val::I32(g)],
        locals: st.locals.update(1, lir::Val::I64(v)),
        mem: st.mem,
    };
    let rest = super::run::chain(super::lower::store_ins(reg_off(dst), val));
    lemma_guarded(op, pc, lbl, lay, s, st, st3, pre, rest, g, fuel);
    if g != 0 {
        let st4 = st3.with_stack(Seq::<lir::Val>::empty());
        assert(rel(lay, s, st4));
        super::proofs::lemma_reg_slot_ok(s, dst);
        let sa = st4.with_stack(st4.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)));
        assert(sa.locals == st3.locals);
        assert(sa.locals.len() == nlocals());
        assert(sa.locals[1] == lir::Val::I64(v));
        assert(super::run::exec(lay, val, sa) == lir::Outcome::Normal(
            sa.with_stack(sa.stack.push(lir::Val::I64(w))),
        ));
        lemma_store_outcome(op, lbl, lay, s, st4, (fuel - 2) as nat, dst, val, w);
    }
}

} // verus!
