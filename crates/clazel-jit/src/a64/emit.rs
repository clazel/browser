//! The executable A64 back end: [`A64Backend`] implements
//! [`super::api::Backend`], proven to return exactly the templates' code
//! ([`super::contract::emit_body_ensures`]) and, through `clazel-a64`'s encoder,
//! its canonical encoding ([`super::contract::emit_blob_ensures`]). It is
//! [`crate::emit`]'s counterpart: the same loop, with the A64 instructions.
//!
//! Arithmetic is checked (the workspace denies the unchecked operators), so
//! the helpers saturate where the proofs show they cannot.

use super::api::Backend;
#[allow(unused_imports)]
use super::spec::*;
use clazel_a64::encoder::encode_instr;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ----------------------------------------------------------------------------
// Checked arithmetic
// ----------------------------------------------------------------------------

fn add_u(a: usize, b: usize) -> (r: usize)
    requires
        a + b <= usize::MAX,
    ensures
        r == a + b,
{
    a.saturating_add(b)
}

fn sub_u(a: usize, b: usize) -> (r: usize)
    requires
        b <= a,
    ensures
        r == a - b,
{
    a.saturating_sub(b)
}

// ----------------------------------------------------------------------------
// Instructions
// ----------------------------------------------------------------------------

/// The operand size of a template: 32 or 64 bits.
fn wd(w32: bool) -> (r: isa::Width)
    ensures
        r == (if w32 {
            isa::Width::W32
        } else {
            isa::Width::W64
        }),
{
    if w32 {
        isa::Width::W32
    } else {
        isa::Width::W64
    }
}

fn slot_imm_exec(j: usize) -> (d: u16)
    requires
        j < 31,
    ensures
        d == slot_imm(j as nat),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
        super::steps::lemma_abi_consts();
    }
    add_u(j, 33) as u16
}

pub(crate) fn ex_load(dst: u8, j: usize) -> (i: isa::Instr)
    requires
        j < 31,
    ensures
        i == super::templates::load_slot(dst, j as nat),
{
    proof {
        super::steps::lemma_abi_consts();
    }
    isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: true,
        t: dst,
        n: 28,
        imm12: slot_imm_exec(j),
    }
}

pub(crate) fn ex_store(j: usize, src: u8) -> (i: isa::Instr)
    requires
        j < 31,
    ensures
        i == super::templates::store_slot(j as nat, src),
{
    proof {
        super::steps::lemma_abi_consts();
    }
    isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: false,
        t: src,
        n: 28,
        imm12: slot_imm_exec(j),
    }
}

fn chunk_exec(v: u64, k: usize) -> (r: u16)
    requires
        k < 4,
    ensures
        r == super::templates::chunk(v, k as nat),
{
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

fn ex_movz(w32: bool, imm16: u16, hw: u8) -> (i: isa::Instr)
    ensures
        i == super::templates::movz0(if w32 {
            isa::Width::W32
        } else {
            isa::Width::W64
        }, imm16, hw),
{
    isa::Instr::MoveWide { sf: wd(w32), opcode: isa::MoveWideOp::Z, d: 0, imm16, hw }
}

fn ex_movk(w32: bool, imm16: u16, hw: u8) -> (i: isa::Instr)
    ensures
        i == super::templates::movk0(if w32 {
            isa::Width::W32
        } else {
            isa::Width::W64
        }, imm16, hw),
{
    isa::Instr::MoveWide { sf: wd(w32), opcode: isa::MoveWideOp::K, d: 0, imm16, hw }
}

fn cset_cond_exec(c: &lir::ICmp) -> (r: u8)
    ensures
        r == super::templates::cset_cond(*c),
{
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

fn int_op_exec(o: &lir::IBin, w32: bool) -> (i: isa::Instr)
    ensures
        i == super::templates::int_op_instr(*o, if w32 {
            isa::Width::W32
        } else {
            isa::Width::W64
        }),
{
    let sf = wd(w32);
    match o {
        lir::IBin::Add => isa::Instr::AddSubShiftedReg {
            sf,
            sub_op: false,
            setflags: false,
            d: 0,
            n: 0,
            m: 1,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Sub => isa::Instr::AddSubShiftedReg {
            sf,
            sub_op: true,
            setflags: false,
            d: 0,
            n: 0,
            m: 1,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::And => isa::Instr::LogicalShiftedReg {
            sf,
            opc: isa::LogicalOpc::And,
            d: 0,
            n: 0,
            m: 1,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Or => isa::Instr::LogicalShiftedReg {
            sf,
            opc: isa::LogicalOpc::Orr,
            d: 0,
            n: 0,
            m: 1,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Xor => isa::Instr::LogicalShiftedReg {
            sf,
            opc: isa::LogicalOpc::Eor,
            d: 0,
            n: 0,
            m: 1,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
        lir::IBin::Shl => isa::Instr::ShiftVariable {
            sf,
            shift_type: isa::ShiftType::Lsl,
            d: 0,
            n: 0,
            m: 1,
        },
        lir::IBin::ShrU => isa::Instr::ShiftVariable {
            sf,
            shift_type: isa::ShiftType::Lsr,
            d: 0,
            n: 0,
            m: 1,
        },
        lir::IBin::ShrS => isa::Instr::ShiftVariable {
            sf,
            shift_type: isa::ShiftType::Asr,
            d: 0,
            n: 0,
            m: 1,
        },
        lir::IBin::Mul => isa::Instr::MulAddSub { sf, sub_op: false, d: 0, n: 0, m: 1, a: 31 },
        lir::IBin::Rotl => isa::Instr::MulAddSub { sf, sub_op: false, d: 0, n: 0, m: 1, a: 31 },
        lir::IBin::Rotr => isa::Instr::MulAddSub { sf, sub_op: false, d: 0, n: 0, m: 1, a: 31 },
    }
}

fn cmp_rr_exec(w32: bool, n: u8, m: u8) -> (i: isa::Instr)
    ensures
        i == super::templates::cmp_rr(if w32 {
            isa::Width::W32
        } else {
            isa::Width::W64
        }, n, m),
{
    isa::Instr::AddSubShiftedReg {
        sf: wd(w32),
        sub_op: true,
        setflags: true,
        d: 31,
        n,
        m,
        shift_type: isa::ShiftType::Lsl,
        shift_amount: 0,
    }
}

fn cmp_zero_exec(w32: bool, n: u8) -> (i: isa::Instr)
    ensures
        i == super::templates::cmp_zero(if w32 {
            isa::Width::W32
        } else {
            isa::Width::W64
        }, n),
{
    isa::Instr::AddSubImm {
        sf: wd(w32),
        sub_op: true,
        setflags: true,
        d: 31,
        n,
        imm12: 0,
        sh: false,
    }
}

fn cset0_exec(cond: u8) -> (i: isa::Instr)
    ensures
        i == super::templates::cset0(cond),
{
    isa::Instr::CondSelect {
        sf: isa::Width::W32,
        else_inv: false,
        else_inc: true,
        d: 0,
        n: 31,
        m: 31,
        cond,
    }
}

// ----------------------------------------------------------------------------
// Which instructions have templates
// ----------------------------------------------------------------------------

fn ibin_supported_exec(o: &lir::IBin) -> (r: bool)
    ensures
        r == crate::spec::ibin_supported(*o),
{
    !matches!(o, lir::IBin::Rotl | lir::IBin::Rotr)
}

fn bin_supported_exec(b: &lir::BinOp) -> (r: bool)
    ensures
        r == crate::spec::bin_supported(*b),
{
    match b {
        lir::BinOp::I32(o) => ibin_supported_exec(o),
        lir::BinOp::I64(o) => ibin_supported_exec(o),
        lir::BinOp::I32Cmp(_) => true,
        lir::BinOp::I64Cmp(_) => true,
        lir::BinOp::F64(_) => false,
        lir::BinOp::F64Cmp(_) => false,
    }
}

fn un_supported_exec(u: &lir::UnOp) -> (r: bool)
    ensures
        r == crate::spec::un_supported(*u),
{
    match u {
        lir::UnOp::I32Eqz => true,
        lir::UnOp::I64Eqz => true,
        lir::UnOp::F64Neg => true,
        lir::UnOp::F64Abs => true,
        lir::UnOp::F64Sqrt => false,
        lir::UnOp::I32WrapI64 => true,
        lir::UnOp::I64ExtendI32S => true,
        lir::UnOp::I64ExtendI32U => true,
        lir::UnOp::F64ConvertI32S => false,
        lir::UnOp::F64ConvertI32U => false,
        lir::UnOp::F64ConvertI64S => false,
        lir::UnOp::F64ConvertI64U => false,
        lir::UnOp::F64ReinterpretI64 => true,
        lir::UnOp::I64ReinterpretF64 => true,
    }
}

pub(crate) fn pops_exec(op: &Op) -> (r: usize)
    ensures
        r == crate::spec::pops(*op),
{
    match op {
        Op::Nop => 0,
        Op::Const(_) => 0,
        Op::LocalGet(_) => 0,
        Op::LocalSet(_) => 1,
        Op::LocalTee(_) => 1,
        Op::Drop => 1,
        Op::Select => 3,
        Op::Bin(_) => 2,
        Op::Un(_) => 1,
    }
}

pub(crate) fn pushes_exec(op: &Op) -> (r: usize)
    ensures
        r == crate::spec::pushes(*op),
{
    match op {
        Op::Nop => 0,
        Op::Const(_) => 1,
        Op::LocalGet(_) => 1,
        Op::LocalSet(_) => 0,
        Op::LocalTee(_) => 1,
        Op::Drop => 0,
        Op::Select => 1,
        Op::Bin(_) => 1,
        Op::Un(_) => 1,
    }
}

pub(crate) fn op_ok_exec(op: &Op, nl: usize, h: usize) -> (r: bool)
    ensures
        r == op_ok(*op, nl as nat, h as nat),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
    }
    if nl > 31 || h > sub_u(31, nl) {
        return false;
    }
    let p = pops_exec(op);
    let q = pushes_exec(op);
    if p > h {
        return false;
    }
    let h2 = add_u(sub_u(h, p), q);
    if h2 > sub_u(31, nl) {
        return false;
    }
    match op {
        Op::LocalGet(x) => *x < nl,
        Op::LocalSet(x) => *x < nl,
        Op::LocalTee(x) => *x < nl,
        Op::Bin(b) => bin_supported_exec(b),
        Op::Un(u) => un_supported_exec(u),
        _ => true,
    }
}

// ----------------------------------------------------------------------------
// Templates
// ----------------------------------------------------------------------------

#[verifier::rlimit(1000)]
pub(crate) fn emit_op(op: &Op, nl: usize, h: usize, out: &mut Vec<isa::Instr>)
    requires
        op_ok(*op, nl as nat, h as nat),
    ensures
        final(out)@ == old(out)@ + super::templates::tmpl(*op, nl as nat, h as nat),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
        super::steps::lemma_abi_consts();
    }
    let ghost old_out = out@;
    match op {
        Op::Nop => {
            proof {
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::Drop => {
            proof {
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::Const(v) => {
            match v {
                lir::Val::I32(c) => {
                    let c64 = *c as u64;
                    out.push(ex_movz(true, chunk_exec(c64, 0), 0));
                    out.push(ex_movk(true, chunk_exec(c64, 1), 1));
                },
                lir::Val::I64(c) => {
                    out.push(ex_movz(false, chunk_exec(*c, 0), 0));
                    out.push(ex_movk(false, chunk_exec(*c, 1), 1));
                    out.push(ex_movk(false, chunk_exec(*c, 2), 2));
                    out.push(ex_movk(false, chunk_exec(*c, 3), 3));
                },
                lir::Val::F64(c) => {
                    out.push(ex_movz(false, chunk_exec(*c, 0), 0));
                    out.push(ex_movk(false, chunk_exec(*c, 1), 1));
                    out.push(ex_movk(false, chunk_exec(*c, 2), 2));
                    out.push(ex_movk(false, chunk_exec(*c, 3), 3));
                },
            }
            out.push(ex_store(add_u(nl, h), 0));
            proof {
                super::tlemmas::lemma_shape0(super::templates::const_mid(*v), (nl + h) as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::LocalGet(x) => {
            out.push(ex_load(0, *x));
            out.push(ex_store(add_u(nl, h), 0));
            proof {
                super::tlemmas::lemma_shape1(x0(), *x as nat, seq![], (nl + h) as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::LocalSet(x) => {
            out.push(ex_load(0, sub_u(add_u(nl, h), 1)));
            out.push(ex_store(*x, 0));
            proof {
                super::tlemmas::lemma_shape1(x0(), (nl + h - 1) as nat, seq![], *x as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::LocalTee(x) => {
            out.push(ex_load(0, sub_u(add_u(nl, h), 1)));
            out.push(ex_store(*x, 0));
            proof {
                super::tlemmas::lemma_shape1(x0(), (nl + h - 1) as nat, seq![], *x as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::Select => {
            let t = sub_u(add_u(nl, h), 3);
            out.push(ex_load(0, t));
            out.push(ex_load(1, add_u(t, 1)));
            out.push(ex_load(2, add_u(t, 2)));
            out.push(cmp_zero_exec(true, 2));
            out.push(
                isa::Instr::CondSelect {
                    sf: isa::Width::W64,
                    else_inv: false,
                    else_inc: false,
                    d: 0,
                    n: 0,
                    m: 1,
                    cond: 1,
                },
            );
            out.push(ex_store(t, 0));
            proof {
                super::tlemmas::lemma_shape3(
                    x0(),
                    t as nat,
                    x1(),
                    (t + 1) as nat,
                    x2(),
                    (t + 2) as nat,
                    super::templates::select_mid(),
                    t as nat,
                );
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::Bin(b) => {
            let t = sub_u(add_u(nl, h), 2);
            match b {
                lir::BinOp::I32(o) => {
                    out.push(ex_load(0, t));
                    out.push(ex_load(1, add_u(t, 1)));
                    out.push(int_op_exec(o, true));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            x0(),
                            t as nat,
                            x1(),
                            (t + 1) as nat,
                            seq![super::templates::int_op_instr(*o, isa::Width::W32)],
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::I64(o) => {
                    out.push(ex_load(0, t));
                    out.push(ex_load(1, add_u(t, 1)));
                    out.push(int_op_exec(o, false));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            x0(),
                            t as nat,
                            x1(),
                            (t + 1) as nat,
                            seq![super::templates::int_op_instr(*o, isa::Width::W64)],
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::I32Cmp(c) => {
                    out.push(ex_load(0, t));
                    out.push(ex_load(1, add_u(t, 1)));
                    out.push(cmp_rr_exec(true, 0, 1));
                    out.push(cset0_exec(cset_cond_exec(c)));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            x0(),
                            t as nat,
                            x1(),
                            (t + 1) as nat,
                            super::templates::cmp_mid(*c, isa::Width::W32),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::I64Cmp(c) => {
                    out.push(ex_load(0, t));
                    out.push(ex_load(1, add_u(t, 1)));
                    out.push(cmp_rr_exec(false, 0, 1));
                    out.push(cset0_exec(cset_cond_exec(c)));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            x0(),
                            t as nat,
                            x1(),
                            (t + 1) as nat,
                            super::templates::cmp_mid(*c, isa::Width::W64),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::F64(_) => {
                    proof {
                        assert(false);
                    }
                },
                lir::BinOp::F64Cmp(_) => {
                    proof {
                        assert(false);
                    }
                },
            }
        },
        Op::Un(u) => {
            let t = sub_u(add_u(nl, h), 1);
            match u {
                lir::UnOp::I32Eqz => {
                    out.push(ex_load(0, t));
                    out.push(cmp_zero_exec(true, 0));
                    out.push(cset0_exec(1));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(
                            x0(),
                            t as nat,
                            super::templates::eqz_mid(isa::Width::W32),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I64Eqz => {
                    out.push(ex_load(0, t));
                    out.push(cmp_zero_exec(false, 0));
                    out.push(cset0_exec(1));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(
                            x0(),
                            t as nat,
                            super::templates::eqz_mid(isa::Width::W64),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::F64Neg => {
                    out.push(ex_load(0, t));
                    out.push(
                        isa::Instr::MoveWide {
                            sf: isa::Width::W64,
                            opcode: isa::MoveWideOp::Z,
                            d: 1,
                            imm16: 0x8000,
                            hw: 3,
                        },
                    );
                    out.push(
                        isa::Instr::LogicalShiftedReg {
                            sf: isa::Width::W64,
                            opc: isa::LogicalOpc::Eor,
                            d: 0,
                            n: 0,
                            m: 1,
                            shift_type: isa::ShiftType::Lsl,
                            shift_amount: 0,
                        },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(x0(), t as nat, super::templates::neg_mid(), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::F64Abs => {
                    out.push(ex_load(0, t));
                    out.push(
                        isa::Instr::Bitfield {
                            sf: isa::Width::W64,
                            signed: false,
                            d: 0,
                            n: 0,
                            immr: 0,
                            imms: 62,
                        },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(x0(), t as nat, super::templates::abs_mid(), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I64ExtendI32S => {
                    out.push(ex_load(0, t));
                    out.push(
                        isa::Instr::Bitfield {
                            sf: isa::Width::W64,
                            signed: true,
                            d: 0,
                            n: 0,
                            immr: 0,
                            imms: 31,
                        },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(x0(), t as nat, super::templates::exts_mid(), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I32WrapI64 => {
                    out.push(ex_load(0, t));
                    out.push(
                        isa::Instr::LogicalShiftedReg {
                            sf: isa::Width::W32,
                            opc: isa::LogicalOpc::Orr,
                            d: 0,
                            n: 31,
                            m: 0,
                            shift_type: isa::ShiftType::Lsl,
                            shift_amount: 0,
                        },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(x0(), t as nat, super::templates::wrap_mid(), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I64ExtendI32U => {
                    proof {
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::F64ReinterpretI64 => {
                    proof {
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I64ReinterpretF64 => {
                    proof {
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::F64Sqrt => {
                    proof {
                        assert(false);
                    }
                },
                lir::UnOp::F64ConvertI32S => {
                    proof {
                        assert(false);
                    }
                },
                lir::UnOp::F64ConvertI32U => {
                    proof {
                        assert(false);
                    }
                },
                lir::UnOp::F64ConvertI64S => {
                    proof {
                        assert(false);
                    }
                },
                lir::UnOp::F64ConvertI64U => {
                    proof {
                        assert(false);
                    }
                },
            }
        },
    }
}

// ----------------------------------------------------------------------------
// Programs
// ----------------------------------------------------------------------------

/// A prefix of a program that has templates has them.
pub proof fn lemma_prog_ok_take(ops: Seq<Op>, k: int, nl: nat, h0: nat)
    requires
        prog_ok(ops, nl, h0),
        0 <= k <= ops.len(),
    ensures
        prog_ok(ops.take(k), nl, h0),
    decreases ops.len(),
{
    if k == ops.len() {
        assert(ops.take(k) =~= ops);
    } else {
        let pre = ops.drop_last();
        lemma_prog_ok_take(pre, k, nl, h0);
        assert(ops.take(k) =~= pre.take(k));
    }
}

/// Each instruction of a program that has templates is well formed at the height
/// the instructions before it leave.
pub proof fn lemma_prog_ok_op(ops: Seq<Op>, k: int, nl: nat, h0: nat)
    requires
        prog_ok(ops, nl, h0),
        0 <= k < ops.len(),
    ensures
        op_ok(ops[k], nl, height_after(ops.take(k), h0)),
{
    lemma_prog_ok_take(ops, k + 1, nl, h0);
    let t = ops.take(k + 1);
    assert(t.drop_last() =~= ops.take(k));
    assert(t.last() == ops[k]);
}

fn emit_body_impl(ops: &[Op], nl: usize) -> (r: Option<Vec<isa::Instr>>)
    ensures
        super::contract::emit_body_ensures(ops@, nl, match r {
            Some(v) => Some(v@),
            None => None,
        }),
{
    if nl > 31 {
        proof {
            super::tlemmas::lemma_abi_consts_t();
            if prog_ok(ops@, nl as nat, 0) {
                lemma_prog_ok_take(ops@, 0, nl as nat, 0);
                assert(ops@.take(0) =~= Seq::<Op>::empty());
            }
        }
        return None;
    }
    let mut out: Vec<isa::Instr> = Vec::new();
    let mut h: usize = 0;
    let mut i: usize = 0;
    proof {
        assert(ops@.take(0) =~= Seq::<Op>::empty());
        super::tlemmas::lemma_abi_consts_t();
    }
    while i < ops.len()
        invariant
            i <= ops.len(),
            nl <= 31,
            prog_ok(ops@.take(i as int), nl as nat, 0),
            h as nat == height_after(ops@.take(i as int), 0),
            out@ == super::templates::code_of(ops@.take(i as int), nl as nat, 0),
        decreases ops.len() - i,
    {
        proof {
            super::tlemmas::lemma_abi_consts_t();
        }
        let op = match ops.get(i) {
            Some(op) => op,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let ok = op_ok_exec(op, nl, h);
        if !ok {
            proof {
                if prog_ok(ops@, nl as nat, 0) {
                    lemma_prog_ok_op(ops@, i as int, nl as nat, 0);
                }
            }
            return None;
        }
        emit_op(op, nl, h, &mut out);
        proof {
            let t = ops@.take(i as int + 1);
            assert(t.drop_last() =~= ops@.take(i as int));
            assert(t.last() == ops@[i as int]);
            assert(super::templates::code_of(t, nl as nat, 0) == super::templates::code_of(ops@.take(i as int), nl as nat, 0) + super::templates::tmpl(
                ops@[i as int],
                nl as nat,
                height_after(ops@.take(i as int), 0),
            ));
        }
        let p = pops_exec(op);
        let q = pushes_exec(op);
        proof {
            assert(op == &ops@[i as int]);
        }
        h = add_u(sub_u(h, p), q);
        i = add_u(i, 1);
    }
    proof {
        assert(ops@.take(ops.len() as int) =~= ops@);
        super::compose::lemma_prog_refines(ops@, nl as nat, 0);
        super::tlemmas::lemma_code_of_valid(ops@, nl as nat, 0);
    }
    Some(out)
}

pub(crate) fn emit_exit(code: &mut Vec<isa::Instr>, exit_code: u16)
    ensures
        final(code)@ == old(code)@ + exit_seq(exit_code),
{
    let ghost old_code = code@;
    code.push(
        isa::Instr::MoveWide {
            sf: isa::Width::W32,
            opcode: isa::MoveWideOp::Z,
            d: 0,
            imm16: exit_code,
            hw: 0,
        },
    );
    code.push(
        isa::Instr::LoadStoreImm {
            sf: isa::Width::W64,
            load: false,
            t: 0,
            n: 28,
            imm12: 32,
        },
    );
    code.push(isa::Instr::Ret);
    proof {
        super::steps::lemma_abi_consts();
        assert(code@ =~= old_code + exit_seq(exit_code));
    }
}

#[verifier::rlimit(500)]
fn emit_blob_impl(ops: &[Op], nl: usize, exit_code: u16) -> (r: Option<Vec<u8>>)
    ensures
        super::contract::emit_blob_ensures(ops@, nl, exit_code, match r {
            Some(v) => Some(v@),
            None => None,
        }),
{
    match emit_body_impl(ops, nl) {
        None => None,
        Some(body) => {
            let ghost body_seq = body@;
            let mut code = body;
            emit_exit(&mut code, exit_code);
            proof {
                super::tlemmas::lemma_exit_valid(exit_code);
                assert(super::contract::all_valid_instrs(body_seq));
                assert forall|k: int| 0 <= k < code@.len() implies isa::valid_instr(
                    #[trigger] code@[k],
                ) by {
                    if k < body_seq.len() {
                        assert(code@[k] == body_seq[k]);
                    } else {
                        assert(code@[k] == exit_seq(exit_code)[k - body_seq.len()]);
                    }
                }
            }
            let mut bytes: Vec<u8> = Vec::new();
            let mut k: usize = 0;
            while k < code.len()
                invariant
                    k <= code.len(),
                    bytes@.len() == 4 * k,
                    forall|j: int|
                        0 <= j < k ==> #[trigger] bytes@.subrange(4 * j, 4 * j + 4) == isa::word_bytes(
                            isa::encode(code@[j]),
                        ),
                    forall|j: int| 0 <= j < code@.len() ==> isa::valid_instr(#[trigger] code@[j]),
                decreases code.len() - k,
            {
                let ins = match code.get(k) {
                    Some(ins) => ins,
                    None => {
                        proof {
                            assert(false);
                        }
                        return None;
                    },
                };
                let w = encode_instr(ins);
                let ghost old_bytes = bytes@;
                bytes.push((w % 256) as u8);
                bytes.push(((w / 0x100) % 256) as u8);
                bytes.push(((w / 0x1_0000) % 256) as u8);
                bytes.push((w / 0x100_0000) as u8);
                proof {
                    assert(ins == &code@[k as int]);
                    assert(w as int == isa::encode(code@[k as int]));
                    assert(w as int / 0x100_0000 < 0x100);
                    let b = isa::word_bytes(isa::encode(code@[k as int]));
                    assert(bytes@ =~= old_bytes + b);
                    assert forall|j: int| 0 <= j < k + 1 implies #[trigger] bytes@.subrange(4 * j, 4 * j + 4)
                        == isa::word_bytes(isa::encode(code@[j])) by {
                        if j < k {
                            assert(bytes@.subrange(4 * j, 4 * j + 4) =~= old_bytes.subrange(4 * j, 4 * j + 4));
                        } else {
                            assert(bytes@.subrange(4 * j, 4 * j + 4) =~= b);
                        }
                    }
                }
                k = add_u(k, 1);
            }
            proof {
                assert(code@ == body_seq + exit_seq(exit_code));
                super::compose::lemma_prog_refines(ops@, nl as nat, 0);
                assert(clazel_codecheck::a64::spec::decodes_to(bytes@, code@)) by {
                    assert(bytes@.len() == 4 * code@.len());
                }
            }
            Some(bytes)
        },
    }
}

/// The LIR → A64 back end.
pub struct A64Backend;

impl Backend for A64Backend {
    fn emit_body(ops: &[Op], nl: usize) -> (r: Option<Vec<isa::Instr>>) {
        emit_body_impl(ops, nl)
    }

    fn emit_blob(ops: &[Op], nl: usize, exit_code: u16) -> (r: Option<Vec<u8>>) {
        emit_blob_impl(ops, nl, exit_code)
    }
}

} // verus!
