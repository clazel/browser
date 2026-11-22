//! The straight-line templates are single instructions the validator accepts
//! whatever it knows (jit.md item J.9, "every emitted blob is accepted",
//! x86-64): none writes the context register or the stack pointer, none
//! touches memory except the context (the frame), none is a jump, and none is
//! a `ret` or a `jcc 2`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::cfunits::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The instruction's memory access, if any, is to the context at a fixed
/// offset, and a store is to the exit area: the validator admits it whatever
/// it knows.
pub open spec fn ctx_only(i: x64::Instr) -> bool {
    match clazel_codecheck::spec::mem_access(i) {
        None => true,
        Some(a) => a.mem.base == abi::ctx_reg() && a.mem.index is None && 0 <= a.mem.disp
            && a.mem.disp + a.size <= abi::ctx_size() && (!a.store || abi::exit_code_off()
            <= a.mem.disp),
    }
}

/// **A simple instruction**: not a `ret` or a `jcc 2`, writes no reserved
/// register, and touches memory only as [`ctx_only`] says.
pub open spec fn simp(i: x64::Instr) -> bool {
    ok2(i) && !clazel_codecheck::spec::writes_reserved(i) && ctx_only(i)
}

/// A simple instruction is accepted by the validator's single-instruction
/// rule, whatever it knows.
pub proof fn lemma_simp_plain(fs: clazel_codecheck::spec::Facts, i: x64::Instr)
    requires
        simp(i),
    ensures
        clazel_codecheck::spec::plain_ok(fs, i) is Some,
{
    if clazel_codecheck::spec::mem_access(i) is Some {
        let a = clazel_codecheck::spec::mem_access(i)->Some_0;
        assert(clazel_codecheck::spec::access_ok(fs, a));
    }
}

/// An instruction that is not a jump.
pub open spec fn nojump(i: x64::Instr) -> bool {
    clazel_codecheck::spec::jump_rel(i) is None
}

/// A simple instruction that is not a jump.
pub open spec fn straight(i: x64::Instr) -> bool {
    simp(i) && nojump(i)
}

/// Every instruction of the list is [`straight`].
pub open spec fn all_straight(c: Seq<x64::Instr>) -> bool {
    forall|k: int| 0 <= k < c.len() ==> straight(#[trigger] c[k])
}

/// Straight code followed by straight code is straight.
pub proof fn lemma_straight_cat(a: Seq<x64::Instr>, b: Seq<x64::Instr>)
    requires
        all_straight(a),
        all_straight(b),
    ensures
        all_straight(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies straight(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// A load of a frame slot into a register other than the reserved ones is
/// straight.
pub proof fn lemma_load_slot_straight(r: u8, j: nat)
    requires
        r < 8,
        r != 4,
        j < 31,
    ensures
        straight(load_slot(r, j)),
        straight(store_slot(j, r)),
{
    assert(max_slots() == 31) by {
        crate::tlemmas::lemma_abi_consts_t();
    }
}

/// The loads of a template are straight.
pub proof fn lemma_loads_straight(ls: Seq<(u8, nat)>)
    requires
        forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q].0 < 8 && ls[q].0 != 4 && ls[q].1 < 31,
    ensures
        all_straight(loads_seq(ls)),
    decreases ls.len(),
{
    if ls.len() > 0 {
        let d = ls.drop_last();
        assert forall|q: int| 0 <= q < d.len() implies #[trigger] d[q].0 < 8 && d[q].0 != 4
            && d[q].1 < 31 by {
            assert(d[q] == ls[q]);
        }
        lemma_loads_straight(d);
        let l = ls.last();
        assert(l == ls[ls.len() - 1]);
        lemma_load_slot_straight(l.0, l.1);
        let one = seq![load_slot(l.0, l.1)];
        assert(all_straight(one));
        lemma_straight_cat(loads_seq(d), one);
    }
}

/// A template of the shape loads, middle, store is straight.
pub proof fn lemma_shape_straight(ls: Seq<(u8, nat)>, mid: Seq<x64::Instr>, ts: nat)
    requires
        forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q].0 < 8 && ls[q].0 != 4 && ls[q].1 < 31,
        all_straight(mid),
        ts < 31,
    ensures
        all_straight(shape(ls, mid, ts)),
{
    lemma_loads_straight(ls);
    lemma_load_slot_straight(0, ts);
    let st = seq![store_slot(ts, rax())];
    assert(all_straight(st));
    lemma_straight_cat(loads_seq(ls), mid);
    lemma_straight_cat(loads_seq(ls) + mid, st);
}

/// Every instruction of every middle the templates use is straight.
pub proof fn lemma_mids_straight(o: lir::IBin, c: lir::ICmp, sz: x64::Size, v: lir::Val)
    ensures
        all_straight(seq![int_op_instr(o, sz)]),
        all_straight(cmp_mid(c, sz)),
        all_straight(eqz_mid(sz)),
        all_straight(mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000)),
        all_straight(mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF)),
        all_straight(exts_mid()),
        all_straight(wrap_mid()),
        all_straight(select_mid()),
        all_straight(seq![const_instr(v)]),
{
    assert forall|k: int| 0 <= k < cmp_mid(c, sz).len() implies straight(
        #[trigger] cmp_mid(c, sz)[k],
    ) by {
        assert(k == 0 || k == 1 || k == 2);
        assert(cc_of(c) < 16 && cc_of(c) != 2 || cc_of(c) == 2);
    }
    assert forall|k: int| 0 <= k < eqz_mid(sz).len() implies straight(#[trigger] eqz_mid(sz)[k]) by {
        assert(k == 0 || k == 1 || k == 2);
    }
    let mx = mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000);
    assert forall|k: int| 0 <= k < mx.len() implies straight(#[trigger] mx[k]) by {
        assert(k == 0 || k == 1);
    }
    let ma = mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF);
    assert forall|k: int| 0 <= k < ma.len() implies straight(#[trigger] ma[k]) by {
        assert(k == 0 || k == 1);
    }
    assert forall|k: int| 0 <= k < exts_mid().len() implies straight(#[trigger] exts_mid()[k]) by {
        assert(k == 0 || k == 1 || k == 2);
    }
    assert forall|k: int| 0 <= k < select_mid().len() implies straight(
        #[trigger] select_mid()[k],
    ) by {
        assert(k == 0 || k == 1);
    }
}

/// **A template of a straight-line instruction is straight.**
pub proof fn lemma_tmpl_straight(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        all_straight(tmpl(op, nl, h)),
{
    assert(max_slots() == 31) by {
        crate::tlemmas::lemma_abi_consts_t();
    }
    lemma_mids_straight(lir::IBin::Add, lir::ICmp::Eq, x64::Size::W32, lir::Val::I32(0));
    match op {
        Op::Nop => {},
        Op::Drop => {},
        Op::Const(v) => {
            lemma_mids_straight(lir::IBin::Add, lir::ICmp::Eq, x64::Size::W32, v);
            lemma_shape_straight(seq![], seq![const_instr(v)], nl + h);
        },
        Op::LocalGet(x) => {
            lemma_shape_straight(seq![(rax(), x as nat)], seq![], nl + h);
        },
        Op::LocalSet(x) => {
            lemma_shape_straight(seq![(rax(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::LocalTee(x) => {
            lemma_shape_straight(seq![(rax(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::Select => {
            let t = (nl + h - 3) as nat;
            lemma_shape_straight(
                seq![(rax(), t), (rcx(), t + 1), (rdx(), t + 2)],
                select_mid(),
                t,
            );
        },
        Op::Bin(b) => {
            let t = (nl + h - 2) as nat;
            match b {
                lir::BinOp::I32(o) => {
                    lemma_mids_straight(o, lir::ICmp::Eq, x64::Size::W32, lir::Val::I32(0));
                    lemma_shape_straight(
                        seq![(rax(), t), (rcx(), t + 1)],
                        seq![int_op_instr(o, x64::Size::W32)],
                        t,
                    );
                },
                lir::BinOp::I64(o) => {
                    lemma_mids_straight(o, lir::ICmp::Eq, x64::Size::W64, lir::Val::I32(0));
                    lemma_shape_straight(
                        seq![(rax(), t), (rcx(), t + 1)],
                        seq![int_op_instr(o, x64::Size::W64)],
                        t,
                    );
                },
                lir::BinOp::I32Cmp(c) => {
                    lemma_mids_straight(lir::IBin::Add, c, x64::Size::W32, lir::Val::I32(0));
                    lemma_shape_straight(
                        seq![(rcx(), t), (rdx(), t + 1)],
                        cmp_mid(c, x64::Size::W32),
                        t,
                    );
                },
                lir::BinOp::I64Cmp(c) => {
                    lemma_mids_straight(lir::IBin::Add, c, x64::Size::W64, lir::Val::I32(0));
                    lemma_shape_straight(
                        seq![(rcx(), t), (rdx(), t + 1)],
                        cmp_mid(c, x64::Size::W64),
                        t,
                    );
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
            match u {
                lir::UnOp::I32Eqz => {
                    lemma_shape_straight(
                        seq![(rcx(), t)],
                        eqz_mid(x64::Size::W32),
                        t,
                    );
                },
                lir::UnOp::I64Eqz => {
                    lemma_shape_straight(
                        seq![(rcx(), t)],
                        eqz_mid(x64::Size::W64),
                        t,
                    );
                },
                lir::UnOp::F64Neg => {
                    lemma_shape_straight(
                        seq![(rax(), t)],
                        mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000),
                        t,
                    );
                },
                lir::UnOp::F64Abs => {
                    lemma_shape_straight(
                        seq![(rax(), t)],
                        mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF),
                        t,
                    );
                },
                lir::UnOp::I64ExtendI32S => {
                    lemma_shape_straight(seq![(rax(), t)], exts_mid(), t);
                },
                lir::UnOp::I32WrapI64 => {
                    lemma_shape_straight(seq![(rax(), t)], wrap_mid(), t);
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

} // verus!
