//! The A64 templates (jit.md J.9): for each LIR instruction of the first
//! slice, at a known stack height, a fixed list of A64 instructions over the
//! scratch registers `x0`, `x1` and `x2`, reading and writing frame slots.
//! These are spec functions: the executable emitter (`emit`) is proven equal
//! to them, and the refinement proofs (`proofs`) are about them. They are
//! [`crate::templates`]'s templates for the A64 instruction set.
//!
//! Every template has the shape *load operands from slots into `x0`, `x1`,
//! `x2`, compute in registers, store `x0` to a slot*. A64 is a three-operand
//! machine with no memory operands, so the middles are shorter than x86-64's:
//! one instruction for each integer operator, two for a comparison (`cmp`,
//! `cset`), and a constant is a `movz` and up to three `movk`. Neither the
//! comparison nor `select` needs a flag to be set beforehand: the flags are
//! written by the instruction that precedes the one that reads them.
//!
//! No template reads memory other than the frame, writes anything but the
//! frame, `x0`, `x1`, `x2` and the flags, or touches `x28`, `x30` or `SP`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `ldr xt, [x28, #(264 + 8 j)]`: load frame slot `j` (64 bits) into `dst`.
pub open spec fn load_slot(dst: u8, j: nat) -> isa::Instr {
    isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: true,
        t: dst,
        n: abi::ctx_reg(),
        imm12: slot_imm(j),
    }
}

/// `str xt, [x28, #(264 + 8 j)]`: store `src` (64 bits) to frame slot `j`.
pub open spec fn store_slot(j: nat, src: u8) -> isa::Instr {
    isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: false,
        t: src,
        n: abi::ctx_reg(),
        imm12: slot_imm(j),
    }
}

/// The `cond` field of the `csinc` that sets a register to 1 when the
/// comparison holds and to 0 otherwise, read after `cmp lhs, rhs`. `cset
/// wd, cc` is `csinc wd, wzr, wzr, invert(cc)`, so this is the *inverse* of
/// the condition that is true when the comparison holds: `ne` (1) for `eq`,
/// `eq` (0) for `ne`, `ge` (10) for signed less, `hs` (2) for below, `le`
/// (13) for signed greater, `ls` (9) for above, `gt` (12) for signed less or
/// equal, `hi` (8) for below or equal, `lt` (11) for signed greater or equal,
/// `lo` (3) for above or equal.
pub open spec fn cset_cond(c: lir::ICmp) -> u8 {
    match c {
        lir::ICmp::Eq => 1,
        lir::ICmp::Ne => 0,
        lir::ICmp::LtS => 10,
        lir::ICmp::LtU => 2,
        lir::ICmp::GtS => 13,
        lir::ICmp::GtU => 9,
        lir::ICmp::LeS => 12,
        lir::ICmp::LeU => 8,
        lir::ICmp::GeS => 11,
        lir::ICmp::GeU => 3,
    }
}

/// The A64 logical operation for an integer binary operator with a
/// one-instruction register-register form (`and`, `orr`, `eor`).
pub open spec fn logic_of(o: lir::IBin) -> Option<isa::LogicalOpc> {
    match o {
        lir::IBin::And => Some(isa::LogicalOpc::And),
        lir::IBin::Or => Some(isa::LogicalOpc::Orr),
        lir::IBin::Xor => Some(isa::LogicalOpc::Eor),
        _ => None,
    }
}

/// The A64 shift for an integer shift operator (`lslv`, `lsrv`, `asrv`).
pub open spec fn shift_of(o: lir::IBin) -> Option<isa::ShiftType> {
    match o {
        lir::IBin::Shl => Some(isa::ShiftType::Lsl),
        lir::IBin::ShrU => Some(isa::ShiftType::Lsr),
        lir::IBin::ShrS => Some(isa::ShiftType::Asr),
        _ => None,
    }
}

/// The instructions that load the slots `ls` (register, slot pairs) one after
/// the other.
pub open spec fn loads_seq(ls: Seq<(u8, nat)>) -> Seq<isa::Instr>
    decreases ls.len(),
{
    if ls.len() == 0 {
        seq![]
    } else {
        loads_seq(ls.drop_last()) + seq![load_slot(ls.last().0, ls.last().1)]
    }
}

/// A template: the loads, the register-only middle, and one store of `x0` to
/// a slot.
pub open spec fn shape(ls: Seq<(u8, nat)>, mid: Seq<isa::Instr>, ts: nat) -> Seq<isa::Instr> {
    loads_seq(ls) + mid + seq![store_slot(ts, x0())]
}

/// `op x0, x0, x1` for the integer operator `o` at width `sf`: `add`, `sub`,
/// `and`, `orr`, `eor`, `mul` (`madd x0, x0, x1, xzr`), or a variable shift.
pub open spec fn int_op_instr(o: lir::IBin, sf: isa::Width) -> isa::Instr {
    match o {
        lir::IBin::Add => isa::Instr::AddSubShiftedReg {
            sf,
            sub_op: false,
            setflags: false,
            d: x0(),
            n: x0(),
            m: x1(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Sub => isa::Instr::AddSubShiftedReg {
            sf,
            sub_op: true,
            setflags: false,
            d: x0(),
            n: x0(),
            m: x1(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::And => isa::Instr::LogicalShiftedReg {
            sf,
            opc: isa::LogicalOpc::And,
            d: x0(),
            n: x0(),
            m: x1(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Or => isa::Instr::LogicalShiftedReg {
            sf,
            opc: isa::LogicalOpc::Orr,
            d: x0(),
            n: x0(),
            m: x1(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Xor => isa::Instr::LogicalShiftedReg {
            sf,
            opc: isa::LogicalOpc::Eor,
            d: x0(),
            n: x0(),
            m: x1(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Shl => isa::Instr::ShiftVariable {
            sf,
            shift_type: isa::ShiftType::Lsl,
            d: x0(),
            n: x0(),
            m: x1(),
        },
        lir::IBin::ShrU => isa::Instr::ShiftVariable {
            sf,
            shift_type: isa::ShiftType::Lsr,
            d: x0(),
            n: x0(),
            m: x1(),
        },
        lir::IBin::ShrS => isa::Instr::ShiftVariable {
            sf,
            shift_type: isa::ShiftType::Asr,
            d: x0(),
            n: x0(),
            m: x1(),
        },
        lir::IBin::Mul => isa::Instr::MulAddSub {
            sf,
            sub_op: false,
            d: x0(),
            n: x0(),
            m: x1(),
            a: 31,
        },
        // no template (the subset has no rotate): a placeholder, never emitted
        lir::IBin::Rotl => isa::Instr::MulAddSub {
            sf,
            sub_op: false,
            d: x0(),
            n: x0(),
            m: x1(),
            a: 31,
        },
        lir::IBin::Rotr => isa::Instr::MulAddSub {
            sf,
            sub_op: false,
            d: x0(),
            n: x0(),
            m: x1(),
            a: 31,
        },
    }
}

/// `cmp rn, rm` (`subs xzr, rn, rm`, or `wzr` at 32 bits): sets the flags of
/// `rn - rm` and writes nothing.
pub open spec fn cmp_rr(sf: isa::Width, n: u8, m: u8) -> isa::Instr {
    isa::Instr::AddSubShiftedReg {
        sf,
        sub_op: true,
        setflags: true,
        d: 31,
        n,
        m,
        shift_type: isa::ShiftType::Lsl,
        shift_amount: 0,
    }
}

/// `cmp rn, #0` (`subs xzr, rn, #0`): sets the flags of `rn - 0`.
pub open spec fn cmp_zero(sf: isa::Width, n: u8) -> isa::Instr {
    isa::Instr::AddSubImm { sf, sub_op: true, setflags: true, d: 31, n, imm12: 0, sh: false }
}

/// `cset w0, cc`, with `cond` the inverse of `cc` (see [`cset_cond`]):
/// `csinc w0, wzr, wzr, cond`, 1 if `cond` fails and 0 if it holds.
pub open spec fn cset0(cond: u8) -> isa::Instr {
    isa::Instr::CondSelect {
        sf: isa::Width::W32,
        else_inv: false,
        else_inc: true,
        d: x0(),
        n: 31,
        m: 31,
        cond,
    }
}

/// `cmp x0, x1; cset w0, cc`: `x0` is 0 or 1.
pub open spec fn cmp_mid(c: lir::ICmp, sf: isa::Width) -> Seq<isa::Instr> {
    seq![cmp_rr(sf, x0(), x1()), cset0(cset_cond(c))]
}

/// `cmp x0, #0; cset w0, eq`: `x0` is 1 if it was 0, else 0.
pub open spec fn eqz_mid(sf: isa::Width) -> Seq<isa::Instr> {
    seq![cmp_zero(sf, x0()), cset0(1)]
}

/// `movz x1, #0x8000, lsl #48; eor x0, x0, x1`: `f64.neg` (flip the sign bit)
/// on the bits.
pub open spec fn neg_mid() -> Seq<isa::Instr> {
    seq![
        isa::Instr::MoveWide {
            sf: isa::Width::W64,
            opcode: isa::MoveWideOp::Z,
            d: x1(),
            imm16: 0x8000,
            hw: 3,
        },
        isa::Instr::LogicalShiftedReg {
            sf: isa::Width::W64,
            opc: isa::LogicalOpc::Eor,
            d: x0(),
            n: x0(),
            m: x1(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
    ]
}

/// `ubfx x0, x0, #0, #63` (`ubfm x0, x0, #0, #62`): the low 63 bits, which
/// clears the sign bit: `f64.abs` on the bits.
pub open spec fn abs_mid() -> Seq<isa::Instr> {
    seq![
        isa::Instr::Bitfield { sf: isa::Width::W64, signed: false, d: x0(), n: x0(), immr: 0, imms: 62 },
    ]
}

/// `sxtw x0, w0` (`sbfm x0, x0, #0, #31`): sign-extends the low 32 bits of
/// `x0` to 64.
pub open spec fn exts_mid() -> Seq<isa::Instr> {
    seq![
        isa::Instr::Bitfield { sf: isa::Width::W64, signed: true, d: x0(), n: x0(), immr: 0, imms: 31 },
    ]
}

/// `mov w0, w0` (`orr w0, wzr, w0`): the low 32 bits, zero-extended.
pub open spec fn wrap_mid() -> Seq<isa::Instr> {
    seq![
        isa::Instr::LogicalShiftedReg {
            sf: isa::Width::W32,
            opc: isa::LogicalOpc::Orr,
            d: x0(),
            n: 31,
            m: x0(),
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
    ]
}

/// `cmp w2, #0; csel x0, x0, x1, ne`: `x0` (the first value) stays unless the
/// condition in `x2` is 0, when it becomes `x1` (the second).
pub open spec fn select_mid() -> Seq<isa::Instr> {
    seq![
        cmp_zero(isa::Width::W32, x2()),
        isa::Instr::CondSelect {
            sf: isa::Width::W64,
            else_inv: false,
            else_inc: false,
            d: x0(),
            n: x0(),
            m: x1(),
            cond: 1,
        },
    ]
}

/// The template of an integer arithmetic, logic or shift instruction at
/// slots `t` (left operand and result) and `t + 1` (right operand): `ldr x0,
/// [t]; ldr x1, [t+1]; op x0, x0, x1; str x0, [t]`.
pub open spec fn int_bin_tmpl(o: lir::IBin, sf: isa::Width, t: nat) -> Seq<isa::Instr> {
    shape(seq![(x0(), t), (x1(), t + 1)], seq![int_op_instr(o, sf)], t)
}

/// The template of an integer comparison at slots `t` and `t + 1`: `ldr x0,
/// [t]; ldr x1, [t+1]; cmp x0, x1; cset w0, cc; str x0, [t]`.
pub open spec fn int_cmp_tmpl(c: lir::ICmp, sf: isa::Width, t: nat) -> Seq<isa::Instr> {
    shape(seq![(x0(), t), (x1(), t + 1)], cmp_mid(c, sf), t)
}

/// The template of `eqz` at slot `t`.
pub open spec fn eqz_tmpl(sf: isa::Width, t: nat) -> Seq<isa::Instr> {
    shape(seq![(x0(), t)], eqz_mid(sf), t)
}

/// The template of a binary instruction at stack height `h` with `nl`
/// locals. An empty list for an instruction outside the slice.
pub open spec fn bin_tmpl(b: lir::BinOp, nl: nat, h: nat) -> Seq<isa::Instr> {
    let t = (nl + h - 2) as nat;
    match b {
        lir::BinOp::I32(o) => int_bin_tmpl(o, isa::Width::W32, t),
        lir::BinOp::I64(o) => int_bin_tmpl(o, isa::Width::W64, t),
        lir::BinOp::I32Cmp(c) => int_cmp_tmpl(c, isa::Width::W32, t),
        lir::BinOp::I64Cmp(c) => int_cmp_tmpl(c, isa::Width::W64, t),
        lir::BinOp::F64(_) => seq![],
        lir::BinOp::F64Cmp(_) => seq![],
    }
}

/// The template of a unary instruction at stack height `h` with `nl` locals.
/// The conversions that change no bits of the word (`extend_i32_u`, the
/// reinterprets) are empty: an `i32` is stored zero-extended, and an `f64`
/// is its bits.
pub open spec fn un_tmpl(u: lir::UnOp, nl: nat, h: nat) -> Seq<isa::Instr> {
    let t = (nl + h - 1) as nat;
    match u {
        lir::UnOp::I32Eqz => eqz_tmpl(isa::Width::W32, t),
        lir::UnOp::I64Eqz => eqz_tmpl(isa::Width::W64, t),
        lir::UnOp::F64Neg => shape(seq![(x0(), t)], neg_mid(), t),
        lir::UnOp::F64Abs => shape(seq![(x0(), t)], abs_mid(), t),
        lir::UnOp::I64ExtendI32S => shape(seq![(x0(), t)], exts_mid(), t),
        lir::UnOp::I32WrapI64 => shape(seq![(x0(), t)], wrap_mid(), t),
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

/// `movz x0, #imm16, lsl #(16 hw)` at width `sf`.
pub open spec fn movz0(sf: isa::Width, imm16: u16, hw: u8) -> isa::Instr {
    isa::Instr::MoveWide { sf, opcode: isa::MoveWideOp::Z, d: x0(), imm16, hw }
}

/// `movk x0, #imm16, lsl #(16 hw)` at width `sf`.
pub open spec fn movk0(sf: isa::Width, imm16: u16, hw: u8) -> isa::Instr {
    isa::Instr::MoveWide { sf, opcode: isa::MoveWideOp::K, d: x0(), imm16, hw }
}

/// The 16-bit chunk `k` (0 is the lowest) of a 64-bit word.
pub open spec fn chunk(v: u64, k: nat) -> u16 {
    if k == 0 {
        (v % 0x1_0000) as u16
    } else if k == 1 {
        ((v / 0x1_0000) % 0x1_0000) as u16
    } else if k == 2 {
        ((v / 0x1_0000_0000) % 0x1_0000) as u16
    } else {
        (v / 0x1_0000_0000_0000) as u16
    }
}

/// The load of a constant into `x0`: `movz w0, #lo; movk w0, #hi, lsl #16` for
/// an `i32`, and `movz x0, #c0; movk x0, #c1, lsl #16; movk x0, #c2, lsl #32;
/// movk x0, #c3, lsl #48` for an `i64` or an `f64`'s bits. (No chunk is
/// skipped: a `movk` of 0 is a harmless instruction, and the proof stays a
/// straight line.)
pub open spec fn const_mid(v: lir::Val) -> Seq<isa::Instr> {
    match v {
        lir::Val::I32(c) => seq![
            movz0(isa::Width::W32, chunk(c as u64, 0), 0),
            movk0(isa::Width::W32, chunk(c as u64, 1), 1),
        ],
        lir::Val::I64(c) => seq![
            movz0(isa::Width::W64, chunk(c, 0), 0),
            movk0(isa::Width::W64, chunk(c, 1), 1),
            movk0(isa::Width::W64, chunk(c, 2), 2),
            movk0(isa::Width::W64, chunk(c, 3), 3),
        ],
        lir::Val::F64(c) => seq![
            movz0(isa::Width::W64, chunk(c, 0), 0),
            movk0(isa::Width::W64, chunk(c, 1), 1),
            movk0(isa::Width::W64, chunk(c, 2), 2),
            movk0(isa::Width::W64, chunk(c, 3), 3),
        ],
    }
}

/// **The template of one instruction** at stack height `h` with `nl` locals.
pub open spec fn tmpl(op: Op, nl: nat, h: nat) -> Seq<isa::Instr> {
    match op {
        Op::Nop => seq![],
        Op::Drop => seq![],
        // the new top is slot nl + h
        Op::Const(v) => shape(seq![], const_mid(v), nl + h),
        Op::LocalGet(x) => shape(seq![(x0(), x as nat)], seq![], nl + h),
        // the top is slot nl + h - 1
        Op::LocalSet(x) => shape(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat),
        Op::LocalTee(x) => shape(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat),
        // v1, v2, c at slots t, t + 1, t + 2: c == 0 picks v2 (csel .. ne)
        Op::Select => {
            let t = (nl + h - 3) as nat;
            shape(seq![(x0(), t), (x1(), t + 1), (x2(), t + 2)], select_mid(), t)
        },
        Op::Bin(b) => bin_tmpl(b, nl, h),
        Op::Un(u) => un_tmpl(u, nl, h),
    }
}

/// The code of a program: the templates one after the other, each at the
/// stack height the instructions before it leave.
pub open spec fn code_of(ops: Seq<Op>, nl: nat, h: nat) -> Seq<isa::Instr>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        code_of(ops.drop_last(), nl, h) + tmpl(ops.last(), nl, height_after(ops.drop_last(), h))
    }
}

} // verus!
