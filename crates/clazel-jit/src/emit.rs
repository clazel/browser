//! The executable back end: [`X64Backend`] implements [`Backend`]. It
//! pushes, for each instruction of the program, exactly the instructions of
//! its template ([`tmpl`]), at the stack height the instructions before it
//! leave, and encodes them with `clazel-x64`'s proven encoder. Each function
//! is proven equal to the spec it implements, so the refinement proofs
//! ([`crate::compose::lemma_prog_refines`]) are about the bytes it returns.

use super::api::Backend;
#[allow(unused_imports)]
use super::spec::*;
use clazel_x64::encoder::encode_exec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ----------------------------------------------------------------------------
// Checked arithmetic (the workspace denies the unchecked operators)
// ----------------------------------------------------------------------------

/// `a + b`, when it does not overflow.
fn add_u(a: usize, b: usize) -> (r: usize)
    requires
        a + b <= usize::MAX,
    ensures
        r == a + b,
{
    a.saturating_add(b)
}

/// `a - b`, when it does not underflow.
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

/// The displacement of frame slot `j` from the context register.
fn slot_disp_exec(j: usize) -> (d: i32)
    requires
        j < 31,
    ensures
        d as int == slot_disp(j as nat),
        slot_mem(j as nat).disp == d,
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
        super::steps::lemma_abi_consts();
    }
    let d = j.saturating_mul(8).saturating_add(264);
    d as i32
}

/// `mov dst, [r15 + 264 + 8 j]`.
pub(crate) fn ex_load(dst: u8, j: usize) -> (i: x64::Instr)
    requires
        j < 31,
    ensures
        i == super::templates::load_slot(dst, j as nat),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
        crate::steps::lemma_abi_consts();
    }
    x64::Instr::MovLoad {
        sz: x64::Size::W64,
        dst,
        mem: x64::Mem { base: 15, index: None, disp: slot_disp_exec(j) },
    }
}

/// `mov [r15 + 264 + 8 j], src`.
pub(crate) fn ex_store(j: usize, src: u8) -> (i: x64::Instr)
    requires
        j < 31,
    ensures
        i == super::templates::store_slot(j as nat, src),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
        crate::steps::lemma_abi_consts();
    }
    x64::Instr::MovStore {
        sz: x64::Size::W64,
        mem: x64::Mem { base: 15, index: None, disp: slot_disp_exec(j) },
        src,
    }
}

/// The instruction that loads a constant into `rax`.
fn ex_const(v: &lir::Val) -> (i: x64::Instr)
    ensures
        i == super::templates::const_instr(*v),
{
    match v {
        lir::Val::I32(c) => x64::Instr::MovImm32 { dst: 0, imm_u32: *c },
        lir::Val::I64(c) => x64::Instr::MovImm64 { dst: 0, imm_u64: *c },
        lir::Val::F64(c) => x64::Instr::MovImm64 { dst: 0, imm_u64: *c },
    }
}

/// The condition code of an integer comparison.
fn cc_exec(c: &lir::ICmp) -> (r: u8)
    ensures
        r == super::templates::cc_of(*c),
{
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

/// The instruction of an integer operator on `rax` and `rcx`.
fn int_op_exec(o: &lir::IBin, sz: x64::Size) -> (i: x64::Instr)
    ensures
        i == super::templates::int_op_instr(*o, sz),
{
    match o {
        lir::IBin::Add => x64::Instr::AluRR { alu: x64::AluOp::Add, sz, dst: 0, src: 1 },
        lir::IBin::Sub => x64::Instr::AluRR { alu: x64::AluOp::Sub, sz, dst: 0, src: 1 },
        lir::IBin::And => x64::Instr::AluRR { alu: x64::AluOp::And, sz, dst: 0, src: 1 },
        lir::IBin::Or => x64::Instr::AluRR { alu: x64::AluOp::Or, sz, dst: 0, src: 1 },
        lir::IBin::Xor => x64::Instr::AluRR { alu: x64::AluOp::Xor, sz, dst: 0, src: 1 },
        lir::IBin::Shl => x64::Instr::ShiftCl { shift: x64::ShiftOp::Shl, sz, r: 0 },
        lir::IBin::ShrU => x64::Instr::ShiftCl { shift: x64::ShiftOp::Shr, sz, r: 0 },
        lir::IBin::ShrS => x64::Instr::ShiftCl { shift: x64::ShiftOp::Sar, sz, r: 0 },
        lir::IBin::Mul => x64::Instr::ImulRR { sz, dst: 0, src: 1 },
        lir::IBin::Rotl => x64::Instr::ImulRR { sz, dst: 0, src: 1 },
        lir::IBin::Rotr => x64::Instr::ImulRR { sz, dst: 0, src: 1 },
    }
}

// ----------------------------------------------------------------------------
// Which instructions have templates
// ----------------------------------------------------------------------------

/// `ibin_supported`.
fn ibin_supported_exec(o: &lir::IBin) -> (r: bool)
    ensures
        r == ibin_supported(*o),
{
    !matches!(o, lir::IBin::Rotl | lir::IBin::Rotr)
}

/// `bin_supported`.
fn bin_supported_exec(b: &lir::BinOp) -> (r: bool)
    ensures
        r == bin_supported(*b),
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

/// `un_supported`.
fn un_supported_exec(u: &lir::UnOp) -> (r: bool)
    ensures
        r == un_supported(*u),
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

/// `pops`.
pub(crate) fn pops_exec(op: &Op) -> (r: usize)
    ensures
        r == pops(*op),
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

/// `pushes`.
pub(crate) fn pushes_exec(op: &Op) -> (r: usize)
    ensures
        r == pushes(*op),
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

/// [`op_ok`], executable.
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

/// Append the template of `op` at height `h` with `nl` locals.
#[verifier::rlimit(500)]
pub(crate) fn emit_op(op: &Op, nl: usize, h: usize, out: &mut Vec<x64::Instr>)
    requires
        op_ok(*op, nl as nat, h as nat),
    ensures
        final(out)@ == old(out)@ + super::templates::tmpl(*op, nl as nat, h as nat),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
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
            let c = ex_const(v);
            out.push(c);
            out.push(ex_store(add_u(nl, h), 0));
            proof {
                super::tlemmas::lemma_shape0(seq![super::templates::const_instr(*v)], (nl + h) as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::LocalGet(x) => {
            out.push(ex_load(0, *x));
            out.push(ex_store(add_u(nl, h), 0));
            proof {
                super::tlemmas::lemma_shape1(rax(), *x as nat, seq![], (nl + h) as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::LocalSet(x) => {
            out.push(ex_load(0, sub_u(add_u(nl, h), 1)));
            out.push(ex_store(*x, 0));
            proof {
                super::tlemmas::lemma_shape1(rax(), (nl + h - 1) as nat, seq![], *x as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::LocalTee(x) => {
            out.push(ex_load(0, sub_u(add_u(nl, h), 1)));
            out.push(ex_store(*x, 0));
            proof {
                super::tlemmas::lemma_shape1(rax(), (nl + h - 1) as nat, seq![], *x as nat);
                assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
            }
        },
        Op::Select => {
            let t = sub_u(add_u(nl, h), 3);
            out.push(ex_load(0, t));
            out.push(ex_load(1, add_u(t, 1)));
            out.push(ex_load(2, add_u(t, 2)));
            out.push(x64::Instr::TestRR { sz: x64::Size::W32, a: 2, b: 2 });
            out.push(x64::Instr::Cmovcc { cc: 4, sz: x64::Size::W64, dst: 0, src: 1 });
            out.push(ex_store(t, 0));
            proof {
                super::tlemmas::lemma_shape3(
                    rax(),
                    t as nat,
                    rcx(),
                    (t + 1) as nat,
                    rdx(),
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
                    out.push(int_op_exec(o, x64::Size::W32));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            rax(),
                            t as nat,
                            rcx(),
                            (t + 1) as nat,
                            seq![super::templates::int_op_instr(*o, x64::Size::W32)],
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::I64(o) => {
                    out.push(ex_load(0, t));
                    out.push(ex_load(1, add_u(t, 1)));
                    out.push(int_op_exec(o, x64::Size::W64));
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            rax(),
                            t as nat,
                            rcx(),
                            (t + 1) as nat,
                            seq![super::templates::int_op_instr(*o, x64::Size::W64)],
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::I32Cmp(c) => {
                    out.push(ex_load(1, t));
                    out.push(ex_load(2, add_u(t, 1)));
                    out.push(x64::Instr::MovImm32 { dst: 0, imm_u32: 0 });
                    out.push(
                        x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: x64::Size::W32, dst: 1, src: 2 },
                    );
                    out.push(x64::Instr::Setcc { cc: cc_exec(c), dst: 0 });
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            rcx(),
                            t as nat,
                            rdx(),
                            (t + 1) as nat,
                            super::templates::cmp_mid(*c, x64::Size::W32),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::BinOp::I64Cmp(c) => {
                    out.push(ex_load(1, t));
                    out.push(ex_load(2, add_u(t, 1)));
                    out.push(x64::Instr::MovImm32 { dst: 0, imm_u32: 0 });
                    out.push(
                        x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: 1, src: 2 },
                    );
                    out.push(x64::Instr::Setcc { cc: cc_exec(c), dst: 0 });
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape2(
                            rcx(),
                            t as nat,
                            rdx(),
                            (t + 1) as nat,
                            super::templates::cmp_mid(*c, x64::Size::W64),
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
                    out.push(ex_load(1, t));
                    out.push(x64::Instr::MovImm32 { dst: 0, imm_u32: 0 });
                    out.push(x64::Instr::TestRR { sz: x64::Size::W32, a: 1, b: 1 });
                    out.push(x64::Instr::Setcc { cc: 4, dst: 0 });
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(rcx(), t as nat, super::templates::eqz_mid(x64::Size::W32), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I64Eqz => {
                    out.push(ex_load(1, t));
                    out.push(x64::Instr::MovImm32 { dst: 0, imm_u32: 0 });
                    out.push(x64::Instr::TestRR { sz: x64::Size::W64, a: 1, b: 1 });
                    out.push(x64::Instr::Setcc { cc: 4, dst: 0 });
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(rcx(), t as nat, super::templates::eqz_mid(x64::Size::W64), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::F64Neg => {
                    out.push(ex_load(0, t));
                    out.push(x64::Instr::MovImm64 { dst: 1, imm_u64: 0x8000_0000_0000_0000 });
                    out.push(
                        x64::Instr::AluRR { alu: x64::AluOp::Xor, sz: x64::Size::W64, dst: 0, src: 1 },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(
                            rax(),
                            t as nat,
                            super::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::F64Abs => {
                    out.push(ex_load(0, t));
                    out.push(x64::Instr::MovImm64 { dst: 1, imm_u64: 0x7FFF_FFFF_FFFF_FFFF });
                    out.push(
                        x64::Instr::AluRR { alu: x64::AluOp::And, sz: x64::Size::W64, dst: 0, src: 1 },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(
                            rax(),
                            t as nat,
                            super::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF),
                            t as nat,
                        );
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I64ExtendI32S => {
                    out.push(ex_load(0, t));
                    out.push(x64::Instr::MovImm32 { dst: 1, imm_u32: 0x8000_0000 });
                    out.push(
                        x64::Instr::AluRR { alu: x64::AluOp::Xor, sz: x64::Size::W64, dst: 0, src: 1 },
                    );
                    out.push(
                        x64::Instr::AluRR { alu: x64::AluOp::Sub, sz: x64::Size::W64, dst: 0, src: 1 },
                    );
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(rax(), t as nat, super::templates::exts_mid(), t as nat);
                        assert(out@ =~= old_out + super::templates::tmpl(*op, nl as nat, h as nat));
                    }
                },
                lir::UnOp::I32WrapI64 => {
                    out.push(ex_load(0, t));
                    out.push(x64::Instr::MovRR { sz: x64::Size::W32, dst: 0, src: 0 });
                    out.push(ex_store(t, 0));
                    proof {
                        super::tlemmas::lemma_shape1(rax(), t as nat, super::templates::wrap_mid(), t as nat);
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

/// `prog_ok` of a prefix.
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

/// The instruction at `k` has a template at the height before it.
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

/// [`Backend::emit_body`], and the proof that the code refines.
fn emit_body_impl(ops: &[Op], nl: usize) -> (r: Option<Vec<x64::Instr>>)
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
    let mut out: Vec<x64::Instr> = Vec::new();
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

/// The exit sequence appended to `code`.
pub(crate) fn emit_exit(code: &mut Vec<x64::Instr>, exit_code: u32)
    ensures
        final(code)@ == old(code)@ + exit_seq(exit_code),
{
    let ghost old_code = code@;
    code.push(x64::Instr::MovImm32 { dst: 0, imm_u32: exit_code });
    code.push(
        x64::Instr::MovStore {
            sz: x64::Size::W64,
            mem: x64::Mem { base: 15, index: None, disp: 256 },
            src: 0,
        },
    );
    code.push(x64::Instr::Ret);
    proof {
        crate::steps::lemma_abi_consts();
        assert(code@ =~= old_code + exit_seq(exit_code));
    }
}

/// [`Backend::emit_blob`]: the code and the exit sequence, encoded.
#[verifier::rlimit(500)]
fn emit_blob_impl(ops: &[Op], nl: usize, exit_code: u32) -> (r: Option<Vec<u8>>)
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
                assert forall|k: int| 0 <= k < code@.len() implies x64::valid_instr(
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
            proof {
                assert(code@.take(0) =~= Seq::<x64::Instr>::empty());
            }
            while k < code.len()
                invariant
                    k <= code.len(),
                    bytes@ == clazel_codecheck::spec::enc_all(code@.take(k as int)),
                    forall|j: int| 0 <= j < code@.len() ==> x64::valid_instr(#[trigger] code@[j]),
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
                let e = encode_exec(ins);
                bytes.extend_from_slice(e.as_slice());
                proof {
                    let t = code@.take(k as int + 1);
                    assert(t.drop_last() =~= code@.take(k as int));
                    assert(t.last() == code@[k as int]);
                    assert(e@ =~= x64::encode(code@[k as int]));
                }
                k = add_u(k, 1);
            }
            proof {
                assert(code@.take(code@.len() as int) =~= code@);
                assert(code@ == body_seq + exit_seq(exit_code));
            }
            Some(bytes)
        },
    }
}

/// The x86-64 back end.
pub struct X64Backend;

impl Backend for X64Backend {
    fn emit_body(ops: &[Op], nl: usize) -> (r: Option<Vec<x64::Instr>>) {
        emit_body_impl(ops, nl)
    }

    fn emit_blob(ops: &[Op], nl: usize, exit_code: u32) -> (r: Option<Vec<u8>>) {
        emit_blob_impl(ops, nl, exit_code)
    }
}

} // verus!
