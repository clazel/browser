//! The lowerings, as spec functions: for an op, the LIR instruction that
//! implements it ([`lower`]), built from a few blocks (a frame slot's
//! address, a load, a store, an exit). Which ops have one is [`lowered`];
//! the proof that each refines `step` is in [`super::proofs`].
//!
//! Every access to a frame slot is `local.get 0` (the frame base),
//! `i64.const offset`, `i64.add`, `bounds_check`, then `load` or `store`:
//! register `r` is at [`reg_off`]`(r)`, a header slot at [`hdr_off`].

#[allow(unused_imports)]
use super::run::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exit code of a failed bounds check. No handler has it, and under the
/// state relation the check never fails (the proofs show it).
pub open spec fn bounds_code() -> nat {
    1000
}

/// `i64.const n`.
pub open spec fn i64c(n: u64) -> lir::Instr {
    lir::Instr::Const(lir::Val::I64(n))
}

/// An `i64` comparison, as an instruction.
pub open spec fn cmp64(o: lir::ICmp) -> lir::Instr {
    lir::Instr::Bin(lir::BinOp::I64Cmp(o))
}

/// Push the address (index into region 0) of the slot at byte offset `off`
/// from the frame base, bounds-checked for 8 bytes.
pub open spec fn addr_ins(off: nat) -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(0),
        i64c(off as u64),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Add)),
        lir::Instr::BoundsCheck { region: 0, size: 8, code: bounds_code() },
    ]
}

/// Push the value of the slot at byte offset `off`.
pub open spec fn load_ins(off: nat) -> Seq<lir::Instr> {
    addr_ins(off).push(lir::Instr::Load { region: 0, ty: lir::Ty::I64 })
}

/// Store, in the slot at byte offset `off`, the value `val` pushes.
pub open spec fn store_ins(off: nat, val: Seq<lir::Instr>) -> Seq<lir::Instr> {
    addr_ins(off) + val + seq![lir::Instr::Store { region: 0, ty: lir::Ty::I64 }]
}

/// The exit to handler `h` from the op at `pc`: push `pc`, exit with the
/// handler's code and that one operand.
pub open spec fn exit_ins(h: js::HandlerId, pc: nat) -> Seq<lir::Instr> {
    seq![
        lir::Instr::Const(lir::Val::I32(pc as u32)),
        lir::Instr::Exit(handler_index(h), seq![lir::Ty::I32]),
    ]
}

/// The op is lowered by this crate.
pub open spec fn lowered(op: js::Op) -> bool {
    if js::op_class(op) is Handler {
        true
    } else {
        match op {
            js::Op::Nop => true,
            js::Op::Move { .. } => true,
            js::Op::LoadConst { .. } => true,
            js::Op::LoadInt { .. } => true,
            js::Op::LoadUndefined { .. } => true,
            js::Op::LoadNull { .. } => true,
            js::Op::LoadBool { .. } => true,
            js::Op::LoadHole { .. } => true,
            js::Op::GetThis { .. } => true,
            js::Op::GetCallee { .. } => true,
            js::Op::Jump { .. } => true,
            js::Op::JumpIfUndefined { .. } => true,
            js::Op::JumpIfNotUndefined { .. } => true,
            js::Op::JumpIfNullish { .. } => true,
            js::Op::JumpIfNotNullish { .. } => true,
            _ => false,
        }
    }
}

/// Store the constant `v` in register `dst`.
pub open spec fn set_const(dst: nat, v: u64) -> Seq<lir::Instr> {
    store_ins(reg_off(dst), seq![i64c(v)])
}

/// Branch to `lbl` if the register `src` holds `v` (`eq`) or does not (`!eq`).
pub open spec fn jump_if_is(src: nat, v: u64, eq: bool, lbl: nat) -> Seq<lir::Instr> {
    load_ins(reg_off(src)) + seq![
        i64c(v),
        cmp64(if eq { lir::ICmp::Eq } else { lir::ICmp::Ne }),
        lir::Instr::BrIf(lbl),
    ]
}

/// After the register's value is on the stack: keep it in scratch local 1,
/// compare it with `undefined` and with `null` (`==` and or, or `!=` and
/// and), and branch to `lbl` if the result is non-zero.
pub open spec fn nullish_rest(not_nullish: bool, lbl: nat) -> Seq<lir::Instr> {
    let o1 = if not_nullish { lir::ICmp::Ne } else { lir::ICmp::Eq };
    let comb = if not_nullish { lir::IBin::And } else { lir::IBin::Or };
    seq![
        lir::Instr::LocalTee(1),
        i64c(js::UNDEFINED),
        cmp64(o1),
        lir::Instr::LocalGet(1),
        i64c(js::NULL),
        cmp64(o1),
        lir::Instr::Bin(lir::BinOp::I32(comb)),
        lir::Instr::BrIf(lbl),
    ]
}

/// The LIR instruction that implements `op`, the op at `pc` of the function
/// whose code is `c`, with `lbl` the label of a jump's target. Meaningful
/// for the ops [`lowered`] holds of.
pub open spec fn lower(c: js::Code, op: js::Op, pc: nat, lbl: nat) -> lir::Instr {
    if js::op_class(op) is Handler {
        // Every handler op: an exit to its handler.
        chain(exit_ins(js::op_handler(op), pc))
    } else {
        match op {
            js::Op::Nop => lir::Instr::Nop,
            js::Op::Move { dst, src } => chain(store_ins(reg_off(dst), load_ins(reg_off(src)))),
            js::Op::LoadConst { dst, k } => chain(set_const(dst, c.consts[k as int])),
            js::Op::LoadInt { dst, imm } => chain(set_const(dst, js::enc_int32(imm))),
            js::Op::LoadUndefined { dst } => chain(set_const(dst, js::UNDEFINED)),
            js::Op::LoadNull { dst } => chain(set_const(dst, js::NULL)),
            js::Op::LoadBool { dst, flag } => chain(set_const(dst, js::enc_bool(flag))),
            js::Op::LoadHole { dst } => chain(set_const(dst, js::HOLE)),
            js::Op::GetThis { dst } => chain(
                store_ins(reg_off(dst), load_ins(hdr_off(js::hdr_this()))),
            ),
            js::Op::GetCallee { dst } => chain(
                store_ins(reg_off(dst), load_ins(hdr_off(js::hdr_callee()))),
            ),
            js::Op::Jump { .. } => lir::Instr::Br(lbl),
            js::Op::JumpIfUndefined { src, .. } => chain(jump_if_is(src, js::UNDEFINED, true, lbl)),
            js::Op::JumpIfNotUndefined { src, .. } => chain(
                jump_if_is(src, js::UNDEFINED, false, lbl),
            ),
            js::Op::JumpIfNullish { src, .. } => chain(
                load_ins(reg_off(src)) + nullish_rest(false, lbl),
            ),
            js::Op::JumpIfNotNullish { src, .. } => chain(
                load_ins(reg_off(src)) + nullish_rest(true, lbl),
            ),
            _ => lir::Instr::Nop,
        }
    }
}

} // verus!
