//! The A64 straight-line templates are single instructions the validator
//! accepts whatever it knows (jit.md item J.9, "every emitted blob is
//! accepted"): none writes the context register, the link register or `sp`,
//! none touches memory except the context (the frame), none is a branch, and
//! none is a `ret` or a `b.hs`. The counterpart of [`crate::cfsimple`].

#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::cfunits::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The instruction's memory access, if any, is to the context at a fixed
/// offset, and a store is to the exit area: the validator admits it whatever
/// it knows.
pub open spec fn ctx_only(i: isa::Instr) -> bool {
    match clazel_codecheck::a64::spec::mem_access(i) {
        None => true,
        Some(a) => a.base == abi::ctx_reg() && a.index is None && 0 <= a.off && a.off + a.size
            <= abi::ctx_size() && (!a.store || abi::exit_code_off() <= a.off),
    }
}

/// **A simple instruction**: not a `ret` or a `b.hs`, writes no reserved
/// register, and touches memory only as [`ctx_only`] says.
pub open spec fn simp(i: isa::Instr) -> bool {
    ok2(i) && !clazel_codecheck::a64::spec::writes_reserved(i) && ctx_only(i)
}

/// A simple instruction is accepted by the validator's single-instruction
/// rule, whatever it knows.
pub proof fn lemma_simp_plain(fs: clazel_codecheck::a64::spec::Facts, i: isa::Instr)
    requires
        simp(i),
    ensures
        clazel_codecheck::a64::spec::plain_ok(fs, i) is Some,
{
    if clazel_codecheck::a64::spec::mem_access(i) is Some {
        let a = clazel_codecheck::a64::spec::mem_access(i)->Some_0;
        assert(clazel_codecheck::a64::spec::access_ok(fs, a));
    }
}

/// An instruction that is not a branch.
pub open spec fn nojump(i: isa::Instr) -> bool {
    clazel_codecheck::a64::spec::jump_rel(i) is None
}

/// A simple instruction that is not a branch.
pub open spec fn straight(i: isa::Instr) -> bool {
    simp(i) && nojump(i)
}

/// Every instruction of the list is [`straight`].
pub open spec fn all_straight(c: Seq<isa::Instr>) -> bool {
    forall|k: int| 0 <= k < c.len() ==> straight(#[trigger] c[k])
}

/// Straight code followed by straight code is straight.
pub proof fn lemma_straight_cat(a: Seq<isa::Instr>, b: Seq<isa::Instr>)
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

/// A load or store of a frame slot is straight.
pub proof fn lemma_load_slot_straight(r: u8, j: nat)
    requires
        r < 8,
        j < 31,
    ensures
        straight(load_slot(r, j)),
        straight(store_slot(j, r)),
{
    assert(max_slots() == 31) by {
        super::tlemmas::lemma_abi_consts_t();
    }
}

/// The loads of a template are straight.
pub proof fn lemma_loads_straight(ls: Seq<(u8, nat)>)
    requires
        forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q].0 < 8 && ls[q].1 < 31,
    ensures
        all_straight(loads_seq(ls)),
    decreases ls.len(),
{
    if ls.len() > 0 {
        let d = ls.drop_last();
        assert forall|q: int| 0 <= q < d.len() implies #[trigger] d[q].0 < 8 && d[q].1 < 31 by {
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
pub proof fn lemma_shape_straight(ls: Seq<(u8, nat)>, mid: Seq<isa::Instr>, ts: nat)
    requires
        forall|q: int| 0 <= q < ls.len() ==> #[trigger] ls[q].0 < 8 && ls[q].1 < 31,
        all_straight(mid),
        ts < 31,
    ensures
        all_straight(shape(ls, mid, ts)),
{
    lemma_loads_straight(ls);
    lemma_load_slot_straight(0, ts);
    let st = seq![store_slot(ts, x0())];
    assert(all_straight(st));
    lemma_straight_cat(loads_seq(ls), mid);
    lemma_straight_cat(loads_seq(ls) + mid, st);
}

/// The integer operation is straight.
pub proof fn lemma_int_op_straight(o: lir::IBin, sf: isa::Width)
    ensures
        all_straight(seq![int_op_instr(o, sf)]),
{
    let c = seq![int_op_instr(o, sf)];
    assert forall|k: int| 0 <= k < c.len() implies straight(#[trigger] c[k]) by {
        assert(k == 0);
        match o {
            lir::IBin::Add => {},
            lir::IBin::Sub => {},
            lir::IBin::And => {},
            lir::IBin::Or => {},
            lir::IBin::Xor => {},
            lir::IBin::Shl => {},
            lir::IBin::ShrU => {},
            lir::IBin::ShrS => {},
            lir::IBin::Mul => {},
            lir::IBin::Rotl => {},
            lir::IBin::Rotr => {},
        }
    }
}

/// Every instruction of every constant's code is straight.
pub proof fn lemma_const_straight(v: lir::Val)
    ensures
        all_straight(const_mid(v)),
{
    let c = const_mid(v);
    assert forall|k: int| 0 <= k < c.len() implies straight(#[trigger] c[k]) by {
        match v {
            lir::Val::I32(_) => {
                assert(k == 0 || k == 1);
            },
            lir::Val::I64(_) => {
                assert(k == 0 || k == 1 || k == 2 || k == 3);
            },
            lir::Val::F64(_) => {
                assert(k == 0 || k == 1 || k == 2 || k == 3);
            },
        }
    }
}

/// Every instruction of the other middles is straight.
pub proof fn lemma_mids_straight(c: lir::ICmp, sf: isa::Width)
    ensures
        all_straight(cmp_mid(c, sf)),
        all_straight(eqz_mid(sf)),
        all_straight(neg_mid()),
        all_straight(abs_mid()),
        all_straight(exts_mid()),
        all_straight(wrap_mid()),
        all_straight(select_mid()),
{
    assert forall|k: int| 0 <= k < cmp_mid(c, sf).len() implies straight(
        #[trigger] cmp_mid(c, sf)[k],
    ) by {
        assert(k == 0 || k == 1);
    }
    assert forall|k: int| 0 <= k < eqz_mid(sf).len() implies straight(#[trigger] eqz_mid(sf)[k]) by {
        assert(k == 0 || k == 1);
    }
    assert forall|k: int| 0 <= k < neg_mid().len() implies straight(#[trigger] neg_mid()[k]) by {
        assert(k == 0 || k == 1);
    }
    assert forall|k: int| 0 <= k < abs_mid().len() implies straight(#[trigger] abs_mid()[k]) by {
        assert(k == 0);
    }
    assert forall|k: int| 0 <= k < exts_mid().len() implies straight(#[trigger] exts_mid()[k]) by {
        assert(k == 0);
    }
    assert forall|k: int| 0 <= k < wrap_mid().len() implies straight(#[trigger] wrap_mid()[k]) by {
        assert(k == 0);
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
        super::tlemmas::lemma_abi_consts_t();
    }
    lemma_mids_straight(lir::ICmp::Eq, isa::Width::W32);
    match op {
        Op::Nop => {},
        Op::Drop => {},
        Op::Const(v) => {
            lemma_const_straight(v);
            lemma_shape_straight(seq![], const_mid(v), nl + h);
        },
        Op::LocalGet(x) => {
            lemma_shape_straight(seq![(x0(), x as nat)], seq![], nl + h);
        },
        Op::LocalSet(x) => {
            lemma_shape_straight(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::LocalTee(x) => {
            lemma_shape_straight(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::Select => {
            let t = (nl + h - 3) as nat;
            lemma_shape_straight(
                seq![(x0(), t), (x1(), t + 1), (x2(), t + 2)],
                select_mid(),
                t,
            );
        },
        Op::Bin(b) => {
            let t = (nl + h - 2) as nat;
            match b {
                lir::BinOp::I32(o) => {
                    lemma_int_op_straight(o, isa::Width::W32);
                    lemma_shape_straight(
                        seq![(x0(), t), (x1(), t + 1)],
                        seq![int_op_instr(o, isa::Width::W32)],
                        t,
                    );
                },
                lir::BinOp::I64(o) => {
                    lemma_int_op_straight(o, isa::Width::W64);
                    lemma_shape_straight(
                        seq![(x0(), t), (x1(), t + 1)],
                        seq![int_op_instr(o, isa::Width::W64)],
                        t,
                    );
                },
                lir::BinOp::I32Cmp(c) => {
                    lemma_mids_straight(c, isa::Width::W32);
                    lemma_shape_straight(
                        seq![(x0(), t), (x1(), t + 1)],
                        cmp_mid(c, isa::Width::W32),
                        t,
                    );
                },
                lir::BinOp::I64Cmp(c) => {
                    lemma_mids_straight(c, isa::Width::W64);
                    lemma_shape_straight(
                        seq![(x0(), t), (x1(), t + 1)],
                        cmp_mid(c, isa::Width::W64),
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
                    lemma_mids_straight(lir::ICmp::Eq, isa::Width::W32);
                    lemma_shape_straight(seq![(x0(), t)], eqz_mid(isa::Width::W32), t);
                },
                lir::UnOp::I64Eqz => {
                    lemma_mids_straight(lir::ICmp::Eq, isa::Width::W64);
                    lemma_shape_straight(seq![(x0(), t)], eqz_mid(isa::Width::W64), t);
                },
                lir::UnOp::F64Neg => {
                    lemma_shape_straight(seq![(x0(), t)], neg_mid(), t);
                },
                lir::UnOp::F64Abs => {
                    lemma_shape_straight(seq![(x0(), t)], abs_mid(), t);
                },
                lir::UnOp::I64ExtendI32S => {
                    lemma_shape_straight(seq![(x0(), t)], exts_mid(), t);
                },
                lir::UnOp::I32WrapI64 => {
                    lemma_shape_straight(seq![(x0(), t)], wrap_mid(), t);
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
