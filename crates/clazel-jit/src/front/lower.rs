//! The lowerings, as spec functions: for an op, the LIR instruction that
//! implements it ([`lower`]), built from a few blocks (a frame slot's
//! address, a load, a store, an exit). Which ops have one is [`lowered`];
//! the proof that each refines `step` is in [`super::proofs`].
//!
//! Every access to a frame slot is `local.get 0` (the frame base),
//! `i64.const offset`, `i64.add`, `bounds_check`, then `load` or `store`:
//! register `r` is at [`reg_off`]`(r)`, a header slot at [`hdr_off`].

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
            js::Op::Add { .. } => true,
            js::Op::Sub { .. } => true,
            js::Op::Mul { .. } => true,
            js::Op::Lt { .. } => true,
            js::Op::Le { .. } => true,
            js::Op::Gt { .. } => true,
            js::Op::Ge { .. } => true,
            js::Op::StrictEq { .. } => true,
            js::Op::StrictNe { .. } => true,
            js::Op::BitAnd { .. } => true,
            js::Op::BitOr { .. } => true,
            js::Op::BitXor { .. } => true,
            js::Op::Shl { .. } => true,
            js::Op::Shr { .. } => true,
            js::Op::Inc { .. } => true,
            js::Op::Dec { .. } => true,
            js::Op::Neg { .. } => true,
            js::Op::BitNot { .. } => true,
            js::Op::Not { .. } => true,
            js::Op::JumpIfTrue { .. } => true,
            js::Op::JumpIfFalse { .. } => true,
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

/// The block type of a block that takes and leaves nothing.
pub open spec fn bt0() -> lir::BlockType {
    lir::BlockType { params: seq![], results: seq![] }
}

/// Test that scratch local `x` holds an int32 value: its high 32 bits are
/// the tag and 16 zero bits. Pushes an `i32`.
pub open spec fn tag_test(x: nat) -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(x),
        i64c(32),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::ShrU)),
        i64c(super::arith::tag_hi()),
        cmp64(lir::ICmp::Eq),
    ]
}

/// Load the two operands into scratch locals 1 and 2.
pub open spec fn operands_ins(a: nat, b: nat) -> Seq<lir::Instr> {
    load_ins(reg_off(a)) + seq![lir::Instr::LocalSet(1)] + load_ins(reg_off(b))
        + seq![lir::Instr::LocalSet(2)]
}

/// Both operands are int32 values: the `and` of the two tests.
pub open spec fn guard1_ins() -> Seq<lir::Instr> {
    tag_test(1) + tag_test(2) + seq![lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And))]
}

/// Push the sign extension of the payload of scratch local `x`.
pub open spec fn sext_local(x: nat) -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(x),
        lir::Instr::Un(lir::UnOp::I32WrapI64),
        lir::Instr::Un(lir::UnOp::I64ExtendI32S),
    ]
}

/// The operation in 64 bits, into scratch local 3.
pub open spec fn compute_ins(k: nat) -> Seq<lir::Instr> {
    sext_local(1) + sext_local(2) + seq![
        lir::Instr::Bin(lir::BinOp::I64(super::arith::ibin_of(k))),
        lir::Instr::LocalSet(3),
    ]
}

/// The part of the second guard every operation has: local 3 is its own
/// sign-extended low half. Pushes an `i32`.
pub open spec fn fits_ins() -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(3),
        lir::Instr::Un(lir::UnOp::I32WrapI64),
        lir::Instr::Un(lir::UnOp::I64ExtendI32S),
        lir::Instr::LocalGet(3),
        cmp64(lir::ICmp::Eq),
    ]
}

/// A product's extra test, with the fits flag on the stack: the result is
/// not a zero from a negative operand (`+0 × -5` is `-0`, not an int32).
/// Leaves one `i32`: the fits flag and that.
pub open spec fn mul_tail_ins() -> Seq<lir::Instr> {
    seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)] + sext_local(1)
        + sext_local(2) + seq![
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
        i64c(0),
        cmp64(lir::ICmp::LtS),
    ] + seq![
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
        lir::Instr::Un(lir::UnOp::I32Eqz),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ]
}

/// The test that the result in local 3 is an int32 the semantics encodes as
/// one: it is its own sign-extended low half and, for a product, not a zero
/// from a negative operand. Pushes an `i32`.
pub open spec fn guard2_ins(k: nat) -> Seq<lir::Instr> {
    if k == 2 {
        fits_ins() + mul_tail_ins()
    } else {
        fits_ins()
    }
}

/// The value to store: the low half of local 3, tagged.
pub open spec fn tagged_ins() -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(3),
        i64c(0xFFFF_FFFF),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
        i64c(super::arith::tag_bits()),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
    ]
}

/// The lowering of small-integer add (`k` 0), subtract (1) or multiply (2)
/// of registers `a` and `b` into `dst`, with an exit to handler `h` from
/// the op at `pc` when an operand is not an int32 or the result is not.
pub open spec fn lower_arith(
    k: nat,
    dst: nat,
    a: nat,
    b: nat,
    h: js::HandlerId,
    pc: nat,
) -> lir::Instr {
    let exit = super::run::chain(exit_ins(h, pc));
    let store = super::run::chain(store_ins(reg_off(dst), tagged_ins()));
    let inner = super::run::chain((compute_ins(k) + guard2_ins(k)).push(lir::Instr::If(
        bt0(),
        Box::new(store),
        Box::new(exit),
    )));
    super::run::chain((operands_ins(a, b) + guard1_ins()).push(lir::Instr::If(
        bt0(),
        Box::new(inner),
        Box::new(exit),
    )))
}

/// The LIR instruction that implements `op`, the op at `pc` of the function
/// whose code is `c`, with `lbl` the label of a jump's target. Meaningful
/// for the ops [`lowered`] holds of.
pub open spec fn lower(c: js::Code, op: js::Op, pc: nat, lbl: nat) -> lir::Instr {
    if js::op_class(op) is Handler {
        // Every handler op: an exit to its handler.
        super::run::chain(exit_ins(js::op_handler(op), pc))
    } else {
        match op {
            js::Op::Nop => lir::Instr::Nop,
            js::Op::Move { dst, src } => super::run::chain(store_ins(reg_off(dst), load_ins(reg_off(src)))),
            js::Op::LoadConst { dst, k } => super::run::chain(set_const(dst, c.consts[k as int])),
            js::Op::LoadInt { dst, imm } => super::run::chain(set_const(dst, js::enc_int32(imm))),
            js::Op::LoadUndefined { dst } => super::run::chain(set_const(dst, js::UNDEFINED)),
            js::Op::LoadNull { dst } => super::run::chain(set_const(dst, js::NULL)),
            js::Op::LoadBool { dst, flag } => super::run::chain(set_const(dst, js::enc_bool(flag))),
            js::Op::LoadHole { dst } => super::run::chain(set_const(dst, js::HOLE)),
            js::Op::GetThis { dst } => super::run::chain(
                store_ins(reg_off(dst), load_ins(hdr_off(js::hdr_this()))),
            ),
            js::Op::GetCallee { dst } => super::run::chain(
                store_ins(reg_off(dst), load_ins(hdr_off(js::hdr_callee()))),
            ),
            js::Op::Jump { .. } => lir::Instr::Br(lbl),
            js::Op::JumpIfUndefined { src, .. } => super::run::chain(jump_if_is(src, js::UNDEFINED, true, lbl)),
            js::Op::JumpIfNotUndefined { src, .. } => super::run::chain(
                jump_if_is(src, js::UNDEFINED, false, lbl),
            ),
            js::Op::JumpIfNullish { src, .. } => super::run::chain(
                load_ins(reg_off(src)) + nullish_rest(false, lbl),
            ),
            js::Op::JumpIfNotNullish { src, .. } => super::run::chain(
                load_ins(reg_off(src)) + nullish_rest(true, lbl),
            ),
            js::Op::Add { dst, a, b } => lower_arith(0, dst, a, b, js::op_handler(op), pc),
            js::Op::Sub { dst, a, b } => lower_arith(1, dst, a, b, js::op_handler(op), pc),
            js::Op::Mul { dst, a, b } => lower_arith(2, dst, a, b, js::op_handler(op), pc),
            js::Op::Lt { dst, a, b } => super::intcmp::lower_cmp(0, dst, a, b, op, pc),
            js::Op::Le { dst, a, b } => super::intcmp::lower_cmp(1, dst, a, b, op, pc),
            js::Op::Gt { dst, a, b } => super::intcmp::lower_cmp(2, dst, a, b, op, pc),
            js::Op::Ge { dst, a, b } => super::intcmp::lower_cmp(3, dst, a, b, op, pc),
            js::Op::StrictEq { dst, a, b } => super::intcmp::lower_cmp(4, dst, a, b, op, pc),
            js::Op::StrictNe { dst, a, b } => super::intcmp::lower_cmp(5, dst, a, b, op, pc),
            js::Op::BitAnd { dst, a, b } => super::bitops::lower_bit(0, dst, a, b, op, pc),
            js::Op::BitOr { dst, a, b } => super::bitops::lower_bit(1, dst, a, b, op, pc),
            js::Op::BitXor { dst, a, b } => super::bitops::lower_bit(2, dst, a, b, op, pc),
            js::Op::Shl { dst, a, b } => super::bitops::lower_bit(3, dst, a, b, op, pc),
            js::Op::Shr { dst, a, b } => super::bitops::lower_bit(4, dst, a, b, op, pc),
            js::Op::Inc { dst, src } => super::unops::lower_unary(0, dst, src, op, pc),
            js::Op::Dec { dst, src } => super::unops::lower_unary(1, dst, src, op, pc),
            js::Op::Neg { dst, src } => super::unops::lower_unary(2, dst, src, op, pc),
            js::Op::BitNot { dst, src } => super::unops::lower_unary(3, dst, src, op, pc),
            js::Op::Not { dst, src } => super::truth::lower_not(dst, src, op, pc),
            js::Op::JumpIfTrue { cond, .. } => super::truth::lower_jump(false, cond, lbl, op, pc),
            js::Op::JumpIfFalse { cond, .. } => super::truth::lower_jump(true, cond, lbl, op, pc),
            _ => lir::Instr::Nop,
        }
    }
}

} // verus!
