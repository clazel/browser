//! The templates (jit.md J.9): for each LIR instruction of the first slice,
//! at a known stack height, a fixed list of x86-64 instructions over the
//! scratch registers `rax`, `rcx` and `rdx`, reading and writing frame slots.
//! These are spec functions: the executable emitter (`emit`) is proven equal
//! to them, and the refinement proofs (`proofs`) are about them.
//!
//! Every template has the shape *load operands from slots into scratch
//! registers, compute in registers, store the result to a slot*. The
//! operand stack's top is slot `nl + h - 1` for `nl` locals and height `h`
//! (see `spec`, modelling choice 2), so a binary operation at height `h`
//! reads slots `nl + h - 2` and `nl + h - 1` and writes the first.
//!
//! No template reads memory other than the frame, writes anything but the
//! frame and scratch registers, or touches `r15` or `rsp`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `mov r, [r15 + 264 + 8 j]`: load frame slot `j` (64 bits) into `dst`.
pub open spec fn load_slot(dst: u8, j: nat) -> x64::Instr {
    x64::Instr::MovLoad { sz: x64::Size::W64, dst: dst, mem: slot_mem(j) }
}

/// `mov [r15 + 264 + 8 j], r`: store `src` (64 bits) to frame slot `j`.
pub open spec fn store_slot(j: nat, src: u8) -> x64::Instr {
    x64::Instr::MovStore { sz: x64::Size::W64, mem: slot_mem(j), src: src }
}

/// The condition code of `setcc` for an integer comparison, read after
/// `cmp lhs, rhs` (so the flags are those of `lhs - rhs`): `e`, `ne`, `l`
/// (signed less), `b` (below: carry), `g`, `a`, `le`, `be`, `ge`, `ae`.
pub open spec fn cc_of(c: lir::ICmp) -> u8 {
    match c {
        lir::ICmp::Eq => 4,
        lir::ICmp::Ne => 5,
        lir::ICmp::LtS => 12,
        lir::ICmp::LtU => 2,
        lir::ICmp::GtS => 15,
        lir::ICmp::GtU => 7,
        lir::ICmp::LeS => 14,
        lir::ICmp::LeU => 6,
        lir::ICmp::GeS => 13,
        lir::ICmp::GeU => 3,
    }
}

/// The x86-64 two-operand operation for an integer binary operator with a
/// one-instruction register-register form (`add`, `sub`, `and`, `or`, `xor`).
pub open spec fn alu_of(o: lir::IBin) -> Option<x64::AluOp> {
    match o {
        lir::IBin::Add => Some(x64::AluOp::Add),
        lir::IBin::Sub => Some(x64::AluOp::Sub),
        lir::IBin::And => Some(x64::AluOp::And),
        lir::IBin::Or => Some(x64::AluOp::Or),
        lir::IBin::Xor => Some(x64::AluOp::Xor),
        _ => None,
    }
}

/// The x86-64 shift for an integer shift operator (`shl`, `shr`, `sar`).
pub open spec fn shift_of(o: lir::IBin) -> Option<x64::ShiftOp> {
    match o {
        lir::IBin::Shl => Some(x64::ShiftOp::Shl),
        lir::IBin::ShrU => Some(x64::ShiftOp::Shr),
        lir::IBin::ShrS => Some(x64::ShiftOp::Sar),
        _ => None,
    }
}

/// The instructions that load the slots `ls` (register, slot pairs) one after
/// the other.
pub open spec fn loads_seq(ls: Seq<(u8, nat)>) -> Seq<x64::Instr>
    decreases ls.len(),
{
    if ls.len() == 0 {
        seq![]
    } else {
        loads_seq(ls.drop_last()) + seq![load_slot(ls.last().0, ls.last().1)]
    }
}

/// A template: the loads, the register-only middle, and one store of `rax` to
/// a slot.
pub open spec fn shape(
    ls: Seq<(u8, nat)>,
    mid: Seq<x64::Instr>,
    ts: nat,
) -> Seq<x64::Instr> {
    loads_seq(ls) + mid + seq![store_slot(ts, rax())]
}

/// `ra := ra op rb` with the operands in `rax` and `rcx`: the operator's
/// instruction (`add sub and or xor imul`, or a shift by `cl`).
pub open spec fn int_op_instr(o: lir::IBin, sz: x64::Size) -> x64::Instr {
    match alu_of(o) {
        Some(alu) => x64::Instr::AluRR { alu: alu, sz: sz, dst: rax(), src: rcx() },
        None => match shift_of(o) {
            Some(sh) => x64::Instr::ShiftCl { shift: sh, sz: sz, r: rax() },
            None => x64::Instr::ImulRR { sz: sz, dst: rax(), src: rcx() },
        },
    }
}

/// `mov eax, 0; cmp rcx, rdx; setcc al`: `rax` is 0 or 1. The `mov` is
/// before the compare because it leaves the flags alone.
pub open spec fn cmp_mid(c: lir::ICmp, sz: x64::Size) -> Seq<x64::Instr> {
    seq![
        x64::Instr::MovImm32 { dst: rax(), imm_u32: 0 },
        x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: sz, dst: rcx(), src: rdx() },
        x64::Instr::Setcc { cc: cc_of(c), dst: rax() },
    ]
}

/// `mov eax, 0; test rcx, rcx; sete al`.
pub open spec fn eqz_mid(sz: x64::Size) -> Seq<x64::Instr> {
    seq![
        x64::Instr::MovImm32 { dst: rax(), imm_u32: 0 },
        x64::Instr::TestRR { sz: sz, a: rcx(), b: rcx() },
        x64::Instr::Setcc { cc: 4, dst: rax() },
    ]
}

/// `mov rcx, mask; xor/and rax, rcx`: `f64.neg` (flip the sign bit) and
/// `f64.abs` (clear it) on the bits.
pub open spec fn mask_mid(alu: x64::AluOp, mask: u64) -> Seq<x64::Instr> {
    seq![
        x64::Instr::MovImm64 { dst: rcx(), imm_u64: mask },
        x64::Instr::AluRR { alu: alu, sz: x64::Size::W64, dst: rax(), src: rcx() },
    ]
}

/// `mov ecx, 0x80000000; xor rax, rcx; sub rax, rcx`: sign-extends the low
/// 32 bits of `rax`, `(x ^ 2^31) - 2^31`.
pub open spec fn exts_mid() -> Seq<x64::Instr> {
    seq![
        x64::Instr::MovImm32 { dst: rcx(), imm_u32: 0x8000_0000 },
        x64::Instr::AluRR {
            alu: x64::AluOp::Xor,
            sz: x64::Size::W64,
            dst: rax(),
            src: rcx(),
        },
        x64::Instr::AluRR {
            alu: x64::AluOp::Sub,
            sz: x64::Size::W64,
            dst: rax(),
            src: rcx(),
        },
    ]
}

/// `mov eax, eax`: the low 32 bits, zero-extended.
pub open spec fn wrap_mid() -> Seq<x64::Instr> {
    seq![x64::Instr::MovRR { sz: x64::Size::W32, dst: rax(), src: rax() }]
}

/// `test edx, edx; cmove rax, rcx`: `rax` (the first value) stays unless the
/// condition in `rdx` is 0, when it becomes `rcx` (the second).
pub open spec fn select_mid() -> Seq<x64::Instr> {
    seq![
        x64::Instr::TestRR { sz: x64::Size::W32, a: rdx(), b: rdx() },
        x64::Instr::Cmovcc { cc: 4, sz: x64::Size::W64, dst: rax(), src: rcx() },
    ]
}

/// The template of an integer arithmetic, logic or shift instruction at
/// slots `t` (left operand and result) and `t + 1` (right operand): `mov rax,
/// [t]; mov rcx, [t+1]; op rax, rcx; mov [t], rax`.
pub open spec fn int_bin_tmpl(o: lir::IBin, sz: x64::Size, t: nat) -> Seq<x64::Instr> {
    shape(seq![(rax(), t), (rcx(), t + 1)], seq![int_op_instr(o, sz)], t)
}

/// The template of an integer comparison at slots `t` and `t + 1`: `mov rcx,
/// [t]; mov rdx, [t+1]; mov eax, 0; cmp rcx, rdx; setcc al; mov [t], rax`.
pub open spec fn int_cmp_tmpl(c: lir::ICmp, sz: x64::Size, t: nat) -> Seq<x64::Instr> {
    shape(seq![(rcx(), t), (rdx(), t + 1)], cmp_mid(c, sz), t)
}

/// The template of `eqz` at slot `t`.
pub open spec fn eqz_tmpl(sz: x64::Size, t: nat) -> Seq<x64::Instr> {
    shape(seq![(rcx(), t)], eqz_mid(sz), t)
}

/// The template of a binary instruction at stack height `h` with `nl`
/// locals. An empty list for an instruction outside the slice.
pub open spec fn bin_tmpl(b: lir::BinOp, nl: nat, h: nat) -> Seq<x64::Instr> {
    let t = (nl + h - 2) as nat;
    match b {
        lir::BinOp::I32(o) => int_bin_tmpl(o, x64::Size::W32, t),
        lir::BinOp::I64(o) => int_bin_tmpl(o, x64::Size::W64, t),
        lir::BinOp::I32Cmp(c) => int_cmp_tmpl(c, x64::Size::W32, t),
        lir::BinOp::I64Cmp(c) => int_cmp_tmpl(c, x64::Size::W64, t),
        lir::BinOp::F64(_) => seq![],
        lir::BinOp::F64Cmp(_) => seq![],
    }
}

/// The template of a unary instruction at stack height `h` with `nl` locals.
/// The conversions that change no bits of the word (`extend_i32_u`, the
/// reinterprets) are empty: an `i32` is stored zero-extended, and an `f64`
/// is its bits.
pub open spec fn un_tmpl(u: lir::UnOp, nl: nat, h: nat) -> Seq<x64::Instr> {
    let t = (nl + h - 1) as nat;
    match u {
        lir::UnOp::I32Eqz => eqz_tmpl(x64::Size::W32, t),
        lir::UnOp::I64Eqz => eqz_tmpl(x64::Size::W64, t),
        lir::UnOp::F64Neg => shape(
            seq![(rax(), t)],
            mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000),
            t,
        ),
        lir::UnOp::F64Abs => shape(
            seq![(rax(), t)],
            mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF),
            t,
        ),
        lir::UnOp::I64ExtendI32S => shape(seq![(rax(), t)], exts_mid(), t),
        lir::UnOp::I32WrapI64 => shape(seq![(rax(), t)], wrap_mid(), t),
        lir::UnOp::I64ExtendI32U => seq![],
        lir::UnOp::F64ReinterpretI64 => seq![],
        lir::UnOp::I64ReinterpretF64 => seq![],
        lir::UnOp::F64Sqrt => seq![],
        lir::UnOp::F64ConvertI32S => seq![],
        lir::UnOp::F64ConvertI32U => seq![],
        lir::UnOp::F64ConvertI64S => seq![],
        lir::UnOp::F64ConvertI64U => seq![],
    }
}

/// The load of a constant into `rax`: `mov eax, c` (zero-extending) for an
/// `i32`, `mov rax, c` for an `i64` or an `f64`'s bits.
pub open spec fn const_instr(v: lir::Val) -> x64::Instr {
    match v {
        lir::Val::I32(c) => x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
        lir::Val::I64(c) => x64::Instr::MovImm64 { dst: rax(), imm_u64: c },
        lir::Val::F64(c) => x64::Instr::MovImm64 { dst: rax(), imm_u64: c },
    }
}

/// **The template of one instruction** at stack height `h` with `nl` locals.
pub open spec fn tmpl(op: Op, nl: nat, h: nat) -> Seq<x64::Instr> {
    match op {
        Op::Nop => seq![],
        Op::Drop => seq![],
        // the new top is slot nl + h
        Op::Const(v) => shape(seq![], seq![const_instr(v)], nl + h),
        Op::LocalGet(x) => shape(seq![(rax(), x as nat)], seq![], nl + h),
        // the top is slot nl + h - 1
        Op::LocalSet(x) => shape(seq![(rax(), (nl + h - 1) as nat)], seq![], x as nat),
        Op::LocalTee(x) => shape(seq![(rax(), (nl + h - 1) as nat)], seq![], x as nat),
        // v1, v2, c at slots t, t + 1, t + 2: c == 0 picks v2 (cmove)
        Op::Select => {
            let t = (nl + h - 3) as nat;
            shape(seq![(rax(), t), (rcx(), t + 1), (rdx(), t + 2)], select_mid(), t)
        },
        Op::Bin(b) => bin_tmpl(b, nl, h),
        Op::Un(u) => un_tmpl(u, nl, h),
    }
}

/// The code of a program: the templates one after the other, each at the
/// stack height the instructions before it leave.
pub open spec fn code_of(ops: Seq<Op>, nl: nat, h: nat) -> Seq<x64::Instr>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        code_of(ops.drop_last(), nl, h) + tmpl(ops.last(), nl, height_after(ops.drop_last(), h))
    }
}

} // verus!
