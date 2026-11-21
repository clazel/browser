//! The dispatch: the refinement theorem of this slice, [`lemma_lower_refines`],
//! by cases on the op, each case one of the lemmas of [`super::proofs`] and
//! [`super::intops`].

#[allow(unused_imports)]
use super::arith::*;
#[allow(unused_imports)]
use super::contract::*;
#[allow(unused_imports)]
use super::frame::*;
#[allow(unused_imports)]
use super::intops::*;
#[allow(unused_imports)]
use super::lirmem::*;
#[allow(unused_imports)]
use super::lower::*;
#[allow(unused_imports)]
use super::proofs::*;
#[allow(unused_imports)]
use super::run::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use super::trace::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The outcome of the lowering of one lowered op from related states.
pub proof fn lemma_op_case(
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
        lowered(op),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, lower(c, op, pc, lbl), st, fuel)),
{
    lemma_state_facts(s);
    let cc = js::cur_code(s);
    assert(js::op_wf(cc, op));
    if js::op_class(op) is Handler {
        lemma_handler_op(c, op, pc, lbl, lay, s, st, fuel);
    } else {
        assert(js::op_class(op) is Core || js::op_class(op) is Guarded);
        match op {
            js::Op::Nop => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                assert(lower(c, op, pc, lbl) == lir::Instr::Nop);
                lemma_rel_pc(lay, s, st, s.pc + 1);
            },
            js::Op::Move { dst, src } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_reg_slot_ok(s, src);
                lemma_copy_op(c, op, pc, lbl, lay, s, st, fuel, dst, reg_off(src));
            },
            js::Op::LoadConst { dst, k } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_const_op(c, op, pc, lbl, lay, s, st, fuel, dst, c.consts[k as int]);
            },
            js::Op::LoadInt { dst, imm } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_const_op(c, op, pc, lbl, lay, s, st, fuel, dst, js::enc_int32(imm));
            },
            js::Op::LoadUndefined { dst } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_const_op(c, op, pc, lbl, lay, s, st, fuel, dst, js::UNDEFINED);
            },
            js::Op::LoadNull { dst } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_const_op(c, op, pc, lbl, lay, s, st, fuel, dst, js::NULL);
            },
            js::Op::LoadBool { dst, flag } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_const_op(c, op, pc, lbl, lay, s, st, fuel, dst, js::enc_bool(flag));
            },
            js::Op::LoadHole { dst } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_const_op(c, op, pc, lbl, lay, s, st, fuel, dst, js::HOLE);
            },
            js::Op::GetThis { dst } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_hdr_slot_ok(s, js::hdr_this());
                lemma_copy_op(c, op, pc, lbl, lay, s, st, fuel, dst, hdr_off(js::hdr_this()));
            },
            js::Op::GetCallee { dst } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_hdr_slot_ok(s, js::hdr_callee());
                lemma_copy_op(c, op, pc, lbl, lay, s, st, fuel, dst, hdr_off(js::hdr_callee()));
            },
            js::Op::Jump { target } => {
                lemma_jump_op(c, op, pc, lbl, lay, s, st, fuel, target);
            },
            js::Op::JumpIfUndefined { src, target } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_jump_if_is(c, op, pc, lbl, lay, s, st, fuel, src, js::UNDEFINED, true, target);
            },
            js::Op::JumpIfNotUndefined { src, target } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_jump_if_is(c, op, pc, lbl, lay, s, st, fuel, src, js::UNDEFINED, false, target);
            },
            js::Op::JumpIfNullish { src, target } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_jump_nullish(c, op, pc, lbl, lay, s, st, fuel, src, false, target);
            },
            js::Op::JumpIfNotNullish { src, target } => {
                clazel_js_vm::lemmas::lemma_core_always_fast(s, op);
                lemma_jump_nullish(c, op, pc, lbl, lay, s, st, fuel, src, true, target);
            },
            js::Op::Add { dst, a, b } => {
                assert(jump_target(op) is None);
                lemma_arith_op(c, op, pc, lbl, lay, s, st, fuel, 0, dst, a, b);
            },
            js::Op::Sub { dst, a, b } => {
                assert(jump_target(op) is None);
                lemma_arith_op(c, op, pc, lbl, lay, s, st, fuel, 1, dst, a, b);
            },
            js::Op::Mul { dst, a, b } => {
                assert(jump_target(op) is None);
                lemma_arith_op(c, op, pc, lbl, lay, s, st, fuel, 2, dst, a, b);
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// **The refinement theorem of this slice**: for every op the front end
/// lowers, its lowering satisfies the statement [`lowers`].
pub proof fn lemma_lower_refines(c: js::Code, op: js::Op, pc: nat, lbl: nat)
    requires
        lowered(op),
    ensures
        lowers(c, op, pc, lbl, lower(c, op, pc, lbl)),
{
    let code = lower(c, op, pc, lbl);
    assert forall|lay: lir::Layout, s: js::State, st: lir::St, fuel: nat|
        #![trigger lir::eval(lay, code, st, fuel), rel(lay, s, st)]
        fuel >= lower_fuel() && rel(lay, s, st) && st.stack == Seq::<lir::Val>::empty()
            && js::state_wf(s) && js::cur_code(s) == c && s.pc == pc && js::fetch(s) == op
            && handler_complete(s, op) implies outcome_refines(
        lay,
        s,
        op,
        lbl,
        lir::eval(lay, code, st, fuel),
    ) by {
        lemma_op_case(c, op, pc, lbl, lay, s, st, fuel);
    }
}


/// The host's decoding of an exit code inverts [`handler_index`]: an exit's
/// code names exactly one handler.
pub proof fn lemma_handler_index_inverse(h: js::HandlerId)
    ensures
        handler_of_index(handler_index(h)) == Some(h),
{
}

} // verus!
