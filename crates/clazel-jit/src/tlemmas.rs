//! Facts about the template definitions the emitter's proof needs: a template
//! is the explicit list of instructions the emitter pushes, and every
//! instruction of the code is in the x86-64 subset.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `shape` with no loads.
pub proof fn lemma_shape0(mid: Seq<x64::Instr>, ts: nat)
    ensures
        super::templates::shape(seq![], mid, ts) == mid + seq![super::templates::store_slot(ts, rax())],
{
    assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<x64::Instr>::empty());
    assert(Seq::<x64::Instr>::empty() + mid =~= mid);
}

/// `shape` with one load.
pub proof fn lemma_shape1(r: u8, j: nat, mid: Seq<x64::Instr>, ts: nat)
    ensures
        super::templates::shape(seq![(r, j)], mid, ts) == seq![super::templates::load_slot(r, j)] + mid + seq![super::templates::store_slot(ts, rax())],
{
    let ls = seq![(r, j)];
    assert(ls.drop_last() =~= Seq::<(u8, nat)>::empty());
    assert(ls.last() == (r, j));
    assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<x64::Instr>::empty());
    assert(super::templates::loads_seq(ls) =~= seq![super::templates::load_slot(r, j)]);
}

/// `shape` with two loads.
pub proof fn lemma_shape2(r1: u8, j1: nat, r2: u8, j2: nat, mid: Seq<x64::Instr>, ts: nat)
    ensures
        super::templates::shape(seq![(r1, j1), (r2, j2)], mid, ts) == seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2)]
            + mid + seq![super::templates::store_slot(ts, rax())],
{
    let ls = seq![(r1, j1), (r2, j2)];
    assert(ls.drop_last() =~= seq![(r1, j1)]);
    assert(ls.last() == (r2, j2));
    lemma_shape1(r1, j1, seq![], 0);
    assert(super::templates::loads_seq(seq![(r1, j1)]) =~= seq![super::templates::load_slot(r1, j1)]) by {
        let l1 = seq![(r1, j1)];
        assert(l1.drop_last() =~= Seq::<(u8, nat)>::empty());
        assert(l1.last() == (r1, j1));
        assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<x64::Instr>::empty());
    }
    assert(super::templates::loads_seq(ls) =~= seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2)]);
}

/// `shape` with three loads.
pub proof fn lemma_shape3(
    r1: u8,
    j1: nat,
    r2: u8,
    j2: nat,
    r3: u8,
    j3: nat,
    mid: Seq<x64::Instr>,
    ts: nat,
)
    ensures
        super::templates::shape(seq![(r1, j1), (r2, j2), (r3, j3)], mid, ts) == seq![
            super::templates::load_slot(r1, j1),
            super::templates::load_slot(r2, j2),
            super::templates::load_slot(r3, j3),
        ] + mid + seq![super::templates::store_slot(ts, rax())],
{
    let ls = seq![(r1, j1), (r2, j2), (r3, j3)];
    assert(ls.drop_last() =~= seq![(r1, j1), (r2, j2)]);
    assert(ls.last() == (r3, j3));
    let l2 = seq![(r1, j1), (r2, j2)];
    assert(l2.drop_last() =~= seq![(r1, j1)]);
    assert(l2.last() == (r2, j2));
    let l1 = seq![(r1, j1)];
    assert(l1.drop_last() =~= Seq::<(u8, nat)>::empty());
    assert(l1.last() == (r1, j1));
    assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<x64::Instr>::empty());
    assert(super::templates::loads_seq(l1) =~= seq![super::templates::load_slot(r1, j1)]);
    assert(super::templates::loads_seq(l2) =~= seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2)]);
    assert(super::templates::loads_seq(ls) =~= seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2), super::templates::load_slot(r3, j3)]);
}

/// The slot operand of a frame slot below 31 is a valid memory operand.
pub proof fn lemma_slot_valid(j: nat)
    requires
        j < max_slots(),
    ensures
        x64::mem_ok(slot_mem(j)),
{
}

/// A load or store of an existing slot with scratch registers is in the subset.
pub proof fn lemma_ls_valid(r: u8, j: nat)
    requires
        r < 16,
        j < max_slots(),
    ensures
        x64::valid_instr(super::templates::load_slot(r, j)),
        x64::valid_instr(super::templates::store_slot(j, r)),
{
    lemma_slot_valid(j);
}

/// Every instruction of a template is in the subset.
pub proof fn lemma_tmpl_valid(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        forall|k: int| 0 <= k < super::templates::tmpl(op, nl, h).len() ==> x64::valid_instr(#[trigger] super::templates::tmpl(op, nl, h)[k]),
{
    assert(max_slots() == 31) by {
        lemma_abi_consts_t();
    }
    let code = super::templates::tmpl(op, nl, h);
    assert forall|k: int| 0 <= k < code.len() implies x64::valid_instr(#[trigger] code[k]) by {
        match op {
            Op::Nop => {},
            Op::Drop => {},
            Op::Const(v) => {
                lemma_shape0(seq![super::templates::const_instr(v)], nl + h);
                lemma_ls_valid(0, nl + h);
                assert(code =~= seq![super::templates::const_instr(v), super::templates::store_slot(nl + h, rax())]);
            },
            Op::LocalGet(x) => {
                lemma_shape1(rax(), x as nat, seq![], nl + h);
                lemma_ls_valid(0, nl + h);
                lemma_ls_valid(0, x as nat);
                assert(code =~= seq![super::templates::load_slot(rax(), x as nat), super::templates::store_slot(nl + h, rax())]);
            },
            Op::LocalSet(x) => {
                lemma_shape1(rax(), (nl + h - 1) as nat, seq![], x as nat);
                lemma_ls_valid(0, x as nat);
                lemma_ls_valid(0, (nl + h - 1) as nat);
                assert(code =~= seq![super::templates::load_slot(rax(), (nl + h - 1) as nat), super::templates::store_slot(x as nat, rax())]);
            },
            Op::LocalTee(x) => {
                lemma_shape1(rax(), (nl + h - 1) as nat, seq![], x as nat);
                lemma_ls_valid(0, x as nat);
                lemma_ls_valid(0, (nl + h - 1) as nat);
                assert(code =~= seq![super::templates::load_slot(rax(), (nl + h - 1) as nat), super::templates::store_slot(x as nat, rax())]);
            },
            Op::Select => {
                let t = (nl + h - 3) as nat;
                lemma_shape3(rax(), t, rcx(), t + 1, rdx(), t + 2, super::templates::select_mid(), t);
                lemma_ls_valid(0, t);
                lemma_ls_valid(1, t + 1);
                lemma_ls_valid(2, t + 2);
                assert(code =~= seq![
                    super::templates::load_slot(rax(), t),
                    super::templates::load_slot(rcx(), t + 1),
                    super::templates::load_slot(rdx(), t + 2),
                    super::templates::select_mid()[0],
                    super::templates::select_mid()[1],
                    super::templates::store_slot(t, rax()),
                ]);
            },
            Op::Bin(b) => {
                let t = (nl + h - 2) as nat;
                match b {
                    lir::BinOp::I32(o) => {
                        lemma_shape2(rax(), t, rcx(), t + 1, seq![super::templates::int_op_instr(o, x64::Size::W32)], t);
                        lemma_ls_valid(0, t);
                        lemma_ls_valid(1, t + 1);
                        assert(code =~= seq![
                            super::templates::load_slot(rax(), t),
                            super::templates::load_slot(rcx(), t + 1),
                            super::templates::int_op_instr(o, x64::Size::W32),
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::I64(o) => {
                        lemma_shape2(rax(), t, rcx(), t + 1, seq![super::templates::int_op_instr(o, x64::Size::W64)], t);
                        lemma_ls_valid(0, t);
                        lemma_ls_valid(1, t + 1);
                        assert(code =~= seq![
                            super::templates::load_slot(rax(), t),
                            super::templates::load_slot(rcx(), t + 1),
                            super::templates::int_op_instr(o, x64::Size::W64),
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::I32Cmp(c) => {
                        lemma_shape2(rcx(), t, rdx(), t + 1, super::templates::cmp_mid(c, x64::Size::W32), t);
                        lemma_ls_valid(1, t);
                        lemma_ls_valid(2, t + 1);
                        lemma_ls_valid(0, t);
                        assert(code =~= seq![
                            super::templates::load_slot(rcx(), t),
                            super::templates::load_slot(rdx(), t + 1),
                            super::templates::cmp_mid(c, x64::Size::W32)[0],
                            super::templates::cmp_mid(c, x64::Size::W32)[1],
                            super::templates::cmp_mid(c, x64::Size::W32)[2],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::I64Cmp(c) => {
                        lemma_shape2(rcx(), t, rdx(), t + 1, super::templates::cmp_mid(c, x64::Size::W64), t);
                        lemma_ls_valid(1, t);
                        lemma_ls_valid(2, t + 1);
                        lemma_ls_valid(0, t);
                        assert(code =~= seq![
                            super::templates::load_slot(rcx(), t),
                            super::templates::load_slot(rdx(), t + 1),
                            super::templates::cmp_mid(c, x64::Size::W64)[0],
                            super::templates::cmp_mid(c, x64::Size::W64)[1],
                            super::templates::cmp_mid(c, x64::Size::W64)[2],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::F64(_) => {
                        assert(false);
                    },
                    lir::BinOp::F64Cmp(_) => {
                        assert(false);
                    },
                }
            },
            Op::Un(u) => {
                let t = (nl + h - 1) as nat;
                lemma_ls_valid(0, t);
                lemma_ls_valid(1, t);
                match u {
                    lir::UnOp::I32Eqz => {
                        lemma_shape1(rcx(), t, super::templates::eqz_mid(x64::Size::W32), t);
                        assert(code =~= seq![
                            super::templates::load_slot(rcx(), t),
                            super::templates::eqz_mid(x64::Size::W32)[0],
                            super::templates::eqz_mid(x64::Size::W32)[1],
                            super::templates::eqz_mid(x64::Size::W32)[2],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I64Eqz => {
                        lemma_shape1(rcx(), t, super::templates::eqz_mid(x64::Size::W64), t);
                        assert(code =~= seq![
                            super::templates::load_slot(rcx(), t),
                            super::templates::eqz_mid(x64::Size::W64)[0],
                            super::templates::eqz_mid(x64::Size::W64)[1],
                            super::templates::eqz_mid(x64::Size::W64)[2],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::F64Neg => {
                        lemma_shape1(rax(), t, super::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000), t);
                        assert(code =~= seq![
                            super::templates::load_slot(rax(), t),
                            super::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000)[0],
                            super::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000)[1],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::F64Abs => {
                        lemma_shape1(rax(), t, super::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF), t);
                        assert(code =~= seq![
                            super::templates::load_slot(rax(), t),
                            super::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF)[0],
                            super::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF)[1],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I64ExtendI32S => {
                        lemma_shape1(rax(), t, super::templates::exts_mid(), t);
                        assert(code =~= seq![
                            super::templates::load_slot(rax(), t),
                            super::templates::exts_mid()[0],
                            super::templates::exts_mid()[1],
                            super::templates::exts_mid()[2],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I32WrapI64 => {
                        lemma_shape1(rax(), t, super::templates::wrap_mid(), t);
                        assert(code =~= seq![
                            super::templates::load_slot(rax(), t),
                            super::templates::wrap_mid()[0],
                            super::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I64ExtendI32U => {},
                    lir::UnOp::F64ReinterpretI64 => {},
                    lir::UnOp::I64ReinterpretF64 => {},
                    lir::UnOp::F64Sqrt => {
                        assert(false);
                    },
                    lir::UnOp::F64ConvertI32S => {
                        assert(false);
                    },
                    lir::UnOp::F64ConvertI32U => {
                        assert(false);
                    },
                    lir::UnOp::F64ConvertI64S => {
                        assert(false);
                    },
                    lir::UnOp::F64ConvertI64U => {
                        assert(false);
                    },
                }
            },
        }
    }
}

/// The ABI constants the lemmas above need.
pub proof fn lemma_abi_consts_t()
    ensures
        max_slots() == 31,
{
}

/// Every instruction of a program's code is in the subset.
pub proof fn lemma_code_of_valid(ops: Seq<Op>, nl: nat, h0: nat)
    requires
        prog_ok(ops, nl, h0),
    ensures
        super::contract::all_valid_instrs(super::templates::code_of(ops, nl, h0)),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let pre = ops.drop_last();
        let last = ops.last();
        let hl = height_after(pre, h0);
        lemma_code_of_valid(pre, nl, h0);
        lemma_tmpl_valid(last, nl, hl);
        let ca = super::templates::code_of(pre, nl, h0);
        let cb = super::templates::tmpl(last, nl, hl);
        assert(super::templates::code_of(ops, nl, h0) == ca + cb);
        assert forall|k: int| 0 <= k < (ca + cb).len() implies x64::valid_instr(
            #[trigger] (ca + cb)[k],
        ) by {
            if k < ca.len() {
                assert((ca + cb)[k] == ca[k]);
            } else {
                assert((ca + cb)[k] == cb[k - ca.len()]);
            }
        }
    }
}

/// The exit sequence is in the subset.
pub proof fn lemma_exit_valid(c: u32)
    ensures
        super::contract::all_valid_instrs(exit_seq(c)),
{
    assert forall|k: int| 0 <= k < exit_seq(c).len() implies x64::valid_instr(
        #[trigger] exit_seq(c)[k],
    ) by {
        assert(k == 0 || k == 1 || k == 2);
    }
}

} // verus!
