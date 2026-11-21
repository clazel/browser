//! The refinement proofs: for each lowered op, [`lower`]'s instruction
//! satisfies [`lowers`] ([`lemma_lower_refines`]). Each case runs LIR's `eval`
//! on the instruction from a related state, with the block lemmas of
//! [`super::frame`], and compares the outcome with `step`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// What a lowering's proof may assume of the states (the hypotheses of
/// [`lowers`]).
pub open spec fn pre(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
) -> bool {
    &&& fuel >= lower_fuel()
    &&& rel(lay, s, st)
    &&& st.stack == Seq::<lir::Val>::empty()
    &&& js::state_wf(s)
    &&& js::cur_code(s) == c
    &&& s.pc == pc
    &&& js::fetch(s) == op
    &&& handler_complete(s, op)
}

/// What `state_wf` gives the proofs: the frame is inside the region, and the
/// op's operands are in range.
pub proof fn lemma_state_facts(s: js::State)
    requires
        js::state_wf(s),
    ensures
        s.fp + js::frame_size(js::cur_code(s)) <= s.region.len(),
        js::op_wf(js::cur_code(s), js::fetch(s)),
        s.fp + js::hdr_slots() <= s.region.len(),
{
    assert(js::frame_wf(s, s.fp));
    let c = js::cur_code(s);
    assert(js::code_wf(c));
    assert(0 <= s.pc < c.ops.len());
    assert(js::op_wf(c, c.ops[s.pc as int]));
}

/// A register of the frame is a slot of the region.
pub proof fn lemma_reg_slot_ok(s: js::State, r: nat)
    requires
        js::state_wf(s),
        js::reg_ok(js::cur_code(s), r),
    ensures
        super::frame::slot_ok(s, reg_off(r)),
        js::reg_slot(s.fp, r) == s.fp + reg_off(r) / 8,
        js::reg_slot(s.fp, r) < s.region.len(),
{
    lemma_state_facts(s);
    assert(reg_off(r) == 8 * (4 + r));
    assert(reg_off(r) / 8 == 4 + r) by (nonlinear_arith)
        requires
            reg_off(r) == 8 * (4 + r),
    ;
}

/// A header slot of the frame is a slot of the region.
pub proof fn lemma_hdr_slot_ok(s: js::State, k: nat)
    requires
        js::state_wf(s),
        k < js::hdr_slots(),
    ensures
        super::frame::slot_ok(s, hdr_off(k)),
        hdr_off(k) / 8 == k,
{
    lemma_state_facts(s);
    assert(hdr_off(k) / 8 == k) by (nonlinear_arith)
        requires
            hdr_off(k) == 8 * k,
    ;
}

/// `rel` does not look at `pc`.
pub proof fn lemma_rel_pc(lay: lir::Layout, s: js::State, st: lir::St, pc: nat)
    requires
        rel(lay, s, st),
    ensures
        rel(lay, js::State { pc: pc, ..s }, st),
{
}

/// A handler op is an exit to its handler.
pub proof fn lemma_handler_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        js::op_class(op) is Handler,
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    clazel_js_vm::lemmas::lemma_handler_never_fast(s, op);
    let h = js::op_handler(op);
    let ins = super::lower::exit_ins(h, pc);
    assert(super::run::all_simple(ins)) by {
        assert forall|i: int| 0 <= i < ins.len() implies super::run::is_simple(#[trigger] ins[i]) by {
            assert(i == 0 || i == 1);
        }
    }
    assert(super::lower::lower(c, op, pc, lbl) == super::run::chain(ins));
    super::run::lemma_chain(lay, ins, st, fuel);
    reveal_with_fuel(super::run::exec, 3);
    let st1 = st.with_stack(seq![lir::Val::I32(pc as u32)]);
    assert(st.stack.push(lir::Val::I32(pc as u32)) =~= seq![lir::Val::I32(pc as u32)]);
    assert(lir::top(st1.stack, 1) =~= seq![lir::Val::I32(pc as u32)]);
}


/// A store of `v` in register `dst`, by a value block `val`, after which the
/// op falls through: the outcome refines `step`, whose result is
/// `next(set_reg(s, dst, v))`.
pub proof fn lemma_store_reg_outcome(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    val: Seq<lir::Instr>,
    v: u64,
    mid: lir::St,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        js::reg_ok(js::cur_code(s), dst),
        super::lower::lower(c, op, pc, lbl) == super::run::chain(super::lower::store_ins(reg_off(dst), val)),
        super::run::all_simple(val),
        val.len() < 40,
        js::fast_path(s, op),
        js::fast_step(s, op) == js::next(js::set_reg(s, dst, v)),
        super::run::exec(
            lay,
            val,
            st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64))),
        ) == lir::Outcome::Normal(mid),
        mid.stack == st.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)).push(
            lir::Val::I64(v),
        ),
        mid.mem == st.mem,
        locals_rel(s, mid.locals),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_reg_slot_ok(s, dst);
    let off = reg_off(dst);
    let ins = super::lower::store_ins(off, val);
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
    super::frame::lemma_exec_store(lay, s, st, off, val, v, mid);
    let j = (s.fp + off / 8) as int;
    let s2 = js::fast_step(s, op);
    assert(s2.region == s.region.update(j, v));
    assert(s2 == js::State { pc: s.pc + 1, ..js::State { region: s.region.update(j, v), ..s } });
    lemma_rel_pc(lay, js::State { region: s.region.update(j, v), ..s }, lir::St {
        stack: st.stack,
        locals: mid.locals,
        mem: lir::write_le(st.mem, slot_addr(lay, j), v as nat, 8),
    }, s.pc + 1);
}


/// The address, load and constant blocks are simple.
pub proof fn lemma_blocks_simple(off: nat, v: u64)
    ensures
        super::run::all_simple(super::lower::addr_ins(off)),
        super::run::all_simple(super::lower::load_ins(off)),
        super::run::all_simple(seq![super::lower::i64c(v)]),
        super::lower::load_ins(off).len() == 5,
{
    let a = super::lower::addr_ins(off);
    assert(super::run::all_simple(a)) by {
        assert forall|i: int| 0 <= i < a.len() implies super::run::is_simple(#[trigger] a[i]) by {
            assert(0 <= i < 4);
        }
    }
    let l = super::lower::load_ins(off);
    assert(super::run::all_simple(l)) by {
        assert forall|i: int| 0 <= i < l.len() implies super::run::is_simple(#[trigger] l[i]) by {
            if i < 4 {
                assert(l[i] == a[i]);
            }
        }
    }
    assert(super::run::all_simple(seq![super::lower::i64c(v)])) by {
        assert forall|i: int| 0 <= i < 1 implies super::run::is_simple(#[trigger] seq![super::lower::i64c(v)][i]) by {}
    }
}

/// An op that stores a constant in a register.
pub proof fn lemma_const_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    v: u64,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        js::reg_ok(js::cur_code(s), dst),
        super::lower::lower(c, op, pc, lbl) == super::run::chain(super::lower::set_const(dst, v)),
        js::fast_path(s, op),
        js::fast_step(s, op) == js::next(js::set_reg(s, dst, v)),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_blocks_simple(0, v);
    lemma_reg_slot_ok(s, dst);
    let sa = st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)));
    reveal_with_fuel(super::run::exec, 2);
    let mid = sa.with_stack(sa.stack.push(lir::Val::I64(v)));
    assert(super::run::exec(lay, seq![super::lower::i64c(v)], sa) == lir::Outcome::Normal(mid));
    lemma_store_reg_outcome(c, op, pc, lbl, lay, s, st, fuel, dst, seq![super::lower::i64c(v)], v, mid);
}

/// An op that copies a slot (a register or a header slot) into a register.
pub proof fn lemma_copy_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    src_off: nat,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        js::reg_ok(js::cur_code(s), dst),
        super::frame::slot_ok(s, src_off),
        super::lower::lower(c, op, pc, lbl) == super::run::chain(super::lower::store_ins(reg_off(dst), super::lower::load_ins(src_off))),
        js::fast_path(s, op),
        js::fast_step(s, op) == js::next(
            js::set_reg(s, dst, s.region[(s.fp + src_off / 8) as int]),
        ),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_blocks_simple(src_off, 0);
    lemma_reg_slot_ok(s, dst);
    let sa = st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + reg_off(dst)) as u64)));
    assert(rel(lay, s, sa));
    super::frame::lemma_exec_load(lay, s, sa, src_off);
    let v = s.region[(s.fp + src_off / 8) as int];
    let mid = sa.with_stack(sa.stack.push(lir::Val::I64(v)));
    assert(super::run::exec(lay, super::lower::load_ins(src_off), sa) == lir::Outcome::Normal(mid));
    lemma_store_reg_outcome(
        c, op, pc, lbl, lay, s, st, fuel, dst, super::lower::load_ins(src_off), v, mid,
    );
}


/// `Jump`: a branch to the label.
pub proof fn lemma_jump_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    target: nat,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        op == (js::Op::Jump { target }),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    assert(js::op_class(op) is Core);
    clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
    assert(super::lower::lower(c, op, pc, lbl) == lir::Instr::Br(lbl));
    lemma_rel_pc(lay, s, st, target);
}

/// A conditional jump on the register `src` being (or not being) the value
/// `v`: `br_if` of a comparison with the constant.
///
/// The resource limit is raised: with the second slice's lowerings in scope
/// (`lower::lower` names them all) the proof is near the default limit.
#[verifier::rlimit(100)]
pub proof fn lemma_jump_if_is(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    src: nat,
    v: u64,
    eq: bool,
    target: nat,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        js::reg_ok(js::cur_code(s), src),
        super::lower::lower(c, op, pc, lbl) == super::run::chain(super::lower::jump_if_is(src, v, eq, lbl)),
        jump_target(op) == Some(target),
        js::fast_path(s, op),
        js::fast_step(s, op) == (if (js::reg(s, src) == v) == eq {
            js::jump(s, target)
        } else {
            js::next(s)
        }),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_blocks_simple(reg_off(src), v);
    lemma_reg_slot_ok(s, src);
    let rest = seq![
        super::lower::i64c(v),
        super::lower::cmp64(if eq { lir::ICmp::Eq } else { lir::ICmp::Ne }),
        lir::Instr::BrIf(lbl),
    ];
    let ins = super::lower::jump_if_is(src, v, eq, lbl);
    assert(super::run::all_simple(ins)) by {
        let l = super::lower::load_ins(reg_off(src));
        assert forall|i: int| 0 <= i < ins.len() implies super::run::is_simple(#[trigger] ins[i]) by {
            if i < 5 {
                assert(ins[i] == l[i]);
            } else {
                assert(ins[i] == rest[i - 5]);
            }
        }
    }
    super::run::lemma_chain(lay, ins, st, fuel);
    super::run::lemma_exec_concat(lay, super::lower::load_ins(reg_off(src)), rest, st);
    super::frame::lemma_exec_load(lay, s, st, reg_off(src));
    let x = js::reg(s, src);
    assert(x == s.region[(s.fp + reg_off(src) / 8) as int]);
    let sl = st.with_stack(st.stack.push(lir::Val::I64(x)));
    assert(st.stack.push(lir::Val::I64(x)) =~= seq![lir::Val::I64(x)]);
    reveal_with_fuel(super::run::exec, 4);
    let cond = lir::bool_i32(lir::icmp(if eq { lir::ICmp::Eq } else { lir::ICmp::Ne }, 64, x as int, v as int));
    assert(cond != 0 <==> ((x == v) == eq));
    let s1 = st.with_stack(Seq::<lir::Val>::empty());
    assert(lir::below(seq![lir::Val::I32(cond)], 1) =~= Seq::<lir::Val>::empty());
    assert(lir::below(seq![lir::Val::I64(x), lir::Val::I64(v)], 2) =~= Seq::<lir::Val>::empty());
    assert(st.stack =~= Seq::<lir::Val>::empty());
    let sc = sl.with_stack(seq![lir::Val::I64(x), lir::Val::I64(v)]);
    assert(sl.stack.push(lir::Val::I64(v)) =~= seq![lir::Val::I64(x), lir::Val::I64(v)]);
    assert(lir::eval(lay, super::lower::i64c(v), sl, 1) == lir::Outcome::Normal(sc));
    let sd = sl.with_stack(seq![lir::Val::I32(cond)]);
    assert(lir::eval(lay, rest[1], sc, 1) == lir::Outcome::Normal(sd));
    assert(super::run::exec(lay, rest, sl) == (if cond != 0 {
        lir::Outcome::Branch(lbl, s1)
    } else {
        lir::Outcome::Normal(s1)
    }));
    assert(s1 == sd.with_stack(lir::below(sd.stack, 1)));
    lemma_rel_pc(lay, s, s1, target);
    lemma_rel_pc(lay, s, s1, s.pc + 1);
}


/// The nullish test as a number: `e1`, `e2` are the two comparisons'
/// results, and `cond` their combination is non-zero exactly when the value is
/// (not) nullish.
pub proof fn lemma_nullish_cond(x: u64, not_nullish: bool)
    ensures
        ({
            let o1 = if not_nullish { lir::ICmp::Ne } else { lir::ICmp::Eq };
            let comb = if not_nullish { lir::IBin::And } else { lir::IBin::Or };
            let e1 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::UNDEFINED as int));
            let e2 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::NULL as int));
            lir::ibin32(comb, e1, e2) != 0 <==> (if not_nullish {
                x != js::UNDEFINED && x != js::NULL
            } else {
                x == js::UNDEFINED || x == js::NULL
            })
        }),
{
    let o1 = if not_nullish { lir::ICmp::Ne } else { lir::ICmp::Eq };
    let comb = if not_nullish { lir::IBin::And } else { lir::IBin::Or };
    let e1 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::UNDEFINED as int));
    let e2 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::NULL as int));
    assert(e1 == 0 || e1 == 1);
    assert(e2 == 0 || e2 == 1);
    if not_nullish {
        assert(lir::ibin32(comb, e1, e2) == (e1 & e2));
        assert((e1 & e2) != 0 <==> (e1 == 1 && e2 == 1)) by (bit_vector)
            requires
                e1 == 0 || e1 == 1,
                e2 == 0 || e2 == 1,
        ;
    } else {
        assert(lir::ibin32(comb, e1, e2) == (e1 | e2));
        assert((e1 | e2) != 0 <==> (e1 == 1 || e2 == 1)) by (bit_vector)
            requires
                e1 == 0 || e1 == 1,
                e2 == 0 || e2 == 1,
        ;
    }
}

/// What the nullish block does to LIR's state: the value of the register
/// is on the stack; it is kept in scratch local 1, compared twice, combined,
/// and branched on.
pub proof fn lemma_nullish_trace(
    lay: lir::Layout,
    sl: lir::St,
    x: u64,
    not_nullish: bool,
    lbl: nat,
)
    requires
        sl.stack == seq![lir::Val::I64(x)],
        sl.locals.len() == nlocals(),
    ensures
        ({
            let o1 = if not_nullish { lir::ICmp::Ne } else { lir::ICmp::Eq };
            let comb = if not_nullish { lir::IBin::And } else { lir::IBin::Or };
            let e1 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::UNDEFINED as int));
            let e2 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::NULL as int));
            let s1 = lir::St {
                stack: Seq::<lir::Val>::empty(),
                locals: sl.locals.update(1, lir::Val::I64(x)),
                mem: sl.mem,
            };
            super::run::exec(lay, super::lower::nullish_rest(not_nullish, lbl), sl) == (if lir::ibin32(comb, e1, e2) != 0 {
                lir::Outcome::Branch(lbl, s1)
            } else {
                lir::Outcome::Normal(s1)
            })
        }),
{
    let o1 = if not_nullish { lir::ICmp::Ne } else { lir::ICmp::Eq };
    let comb = if not_nullish { lir::IBin::And } else { lir::IBin::Or };
    let e1 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::UNDEFINED as int));
    let e2 = lir::bool_i32(lir::icmp(o1, 64, x as int, js::NULL as int));
    let loc2 = sl.locals.update(1, lir::Val::I64(x));
    let rest = super::lower::nullish_rest(not_nullish, lbl);
    let a1 = lir::St { stack: seq![lir::Val::I64(x)], locals: loc2, mem: sl.mem };
    let a2 = lir::St { stack: seq![lir::Val::I64(x), lir::Val::I64(js::UNDEFINED)], locals: loc2, mem: sl.mem };
    let a3 = lir::St { stack: seq![lir::Val::I32(e1)], locals: loc2, mem: sl.mem };
    let a4 = lir::St { stack: seq![lir::Val::I32(e1), lir::Val::I64(x)], locals: loc2, mem: sl.mem };
    let a5 = lir::St {
        stack: seq![lir::Val::I32(e1), lir::Val::I64(x), lir::Val::I64(js::NULL)],
        locals: loc2,
        mem: sl.mem,
    };
    let a6 = lir::St { stack: seq![lir::Val::I32(e1), lir::Val::I32(e2)], locals: loc2, mem: sl.mem };
    let cond = lir::ibin32(comb, e1, e2);
    let a7 = lir::St { stack: seq![lir::Val::I32(cond)], locals: loc2, mem: sl.mem };
    let s1 = lir::St { stack: Seq::<lir::Val>::empty(), locals: loc2, mem: sl.mem };
    assert(lir::eval(lay, rest[0], sl, 1) == lir::Outcome::Normal(a1));
    assert(a1.stack.push(lir::Val::I64(js::UNDEFINED)) =~= a2.stack);
    assert(lir::eval(lay, rest[1], a1, 1) == lir::Outcome::Normal(a2));
    assert(lir::below(a2.stack, 2) =~= Seq::<lir::Val>::empty());
    assert(lir::eval(lay, rest[2], a2, 1) == lir::Outcome::Normal(a3));
    assert(loc2[1] == lir::Val::I64(x));
    assert(a3.stack.push(lir::Val::I64(x)) =~= a4.stack);
    assert(lir::eval(lay, rest[3], a3, 1) == lir::Outcome::Normal(a4));
    assert(a4.stack.push(lir::Val::I64(js::NULL)) =~= a5.stack);
    assert(lir::eval(lay, rest[4], a4, 1) == lir::Outcome::Normal(a5));
    assert(lir::below(a5.stack, 2) =~= seq![lir::Val::I32(e1)]);
    assert(seq![lir::Val::I32(e1)].push(lir::Val::I32(e2)) =~= a6.stack);
    assert(lir::eval(lay, rest[5], a5, 1) == lir::Outcome::Normal(a6));
    assert(lir::below(a6.stack, 2) =~= Seq::<lir::Val>::empty());
    assert(Seq::<lir::Val>::empty().push(lir::Val::I32(cond)) =~= a7.stack);
    assert(lir::eval(lay, rest[6], a6, 1) == lir::Outcome::Normal(a7));
    assert(lir::below(a7.stack, 1) =~= Seq::<lir::Val>::empty());
    reveal_with_fuel(super::run::exec, 9);
}


/// A conditional jump on the register `src` being nullish (`undefined` or
/// `null`), or not.
pub proof fn lemma_jump_nullish(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    src: nat,
    not_nullish: bool,
    target: nat,
)
    requires
        pre(c, op, pc, lay, s, st, fuel),
        js::reg_ok(js::cur_code(s), src),
        super::lower::lower(c, op, pc, lbl) == super::run::chain(super::lower::load_ins(reg_off(src)) + super::lower::nullish_rest(not_nullish, lbl)),
        jump_target(op) == Some(target),
        js::fast_path(s, op),
        js::fast_step(s, op) == (if (if not_nullish {
            js::reg(s, src) != js::UNDEFINED && js::reg(s, src) != js::NULL
        } else {
            js::reg(s, src) == js::UNDEFINED || js::reg(s, src) == js::NULL
        }) {
            js::jump(s, target)
        } else {
            js::next(s)
        }),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_blocks_simple(reg_off(src), 0);
    lemma_reg_slot_ok(s, src);
    let rest = super::lower::nullish_rest(not_nullish, lbl);
    let l = super::lower::load_ins(reg_off(src));
    let ins = l + rest;
    assert(super::run::all_simple(ins)) by {
        assert forall|i: int| 0 <= i < ins.len() implies super::run::is_simple(#[trigger] ins[i]) by {
            if i < 5 {
                assert(ins[i] == l[i]);
            } else {
                assert(ins[i] == rest[i - 5]);
            }
        }
    }
    assert(ins.len() == 13);
    super::run::lemma_chain(lay, ins, st, fuel);
    super::run::lemma_exec_concat(lay, l, rest, st);
    super::frame::lemma_exec_load(lay, s, st, reg_off(src));
    let x = js::reg(s, src);
    assert(x == s.region[(s.fp + reg_off(src) / 8) as int]);
    let sl = st.with_stack(seq![lir::Val::I64(x)]);
    assert(st.stack.push(lir::Val::I64(x)) =~= seq![lir::Val::I64(x)]);
    lemma_nullish_trace(lay, sl, x, not_nullish, lbl);
    lemma_nullish_cond(x, not_nullish);
    let loc2 = st.locals.update(1, lir::Val::I64(x));
    let s1 = lir::St { stack: Seq::<lir::Val>::empty(), locals: loc2, mem: st.mem };
    assert(locals_rel(s, loc2)) by {
        assert forall|j: int| 1 <= j < loc2.len() implies #[trigger] loc2[j] is I64 by {
            if j != 1 {
                assert(loc2[j] == st.locals[j]);
            }
        }
        assert(loc2[0] == st.locals[0]);
    }
    assert(rel(lay, s, s1));
    lemma_rel_pc(lay, s, s1, target);
    lemma_rel_pc(lay, s, s1, s.pc + 1);
}

} // verus!
