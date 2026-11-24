//! Facts about the templates the emitter needs: a template is the loads, the
//! middle and the store written out; every instruction of every template is in
//! the A64 subset ([`isa::valid_instr`]), so the encoder accepts it. The A64
//! counterpart of [`crate::tlemmas`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `shape` with no loads.
pub proof fn lemma_shape0(mid: Seq<isa::Instr>, ts: nat)
    ensures
        super::templates::shape(seq![], mid, ts) == mid + seq![super::templates::store_slot(ts, x0())],
{
    assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<isa::Instr>::empty());
    assert(Seq::<isa::Instr>::empty() + mid =~= mid);
}

/// `shape` with one load, written out.
pub proof fn lemma_shape1(r: u8, j: nat, mid: Seq<isa::Instr>, ts: nat)
    ensures
        super::templates::shape(seq![(r, j)], mid, ts) == seq![super::templates::load_slot(r, j)] + mid + seq![super::templates::store_slot(ts, x0())],
{
    let ls = seq![(r, j)];
    assert(ls.drop_last() =~= Seq::<(u8, nat)>::empty());
    assert(ls.last() == (r, j));
    assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<isa::Instr>::empty());
    assert(super::templates::loads_seq(ls) =~= seq![super::templates::load_slot(r, j)]);
}

/// `shape` with two loads, written out.
pub proof fn lemma_shape2(r1: u8, j1: nat, r2: u8, j2: nat, mid: Seq<isa::Instr>, ts: nat)
    ensures
        super::templates::shape(seq![(r1, j1), (r2, j2)], mid, ts) == seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2)]
            + mid + seq![super::templates::store_slot(ts, x0())],
{
    let ls = seq![(r1, j1), (r2, j2)];
    assert(ls.drop_last() =~= seq![(r1, j1)]);
    assert(ls.last() == (r2, j2));
    lemma_shape1(r1, j1, seq![], 0);
    assert(super::templates::loads_seq(seq![(r1, j1)]) =~= seq![super::templates::load_slot(r1, j1)]) by {
        let l1 = seq![(r1, j1)];
        assert(l1.drop_last() =~= Seq::<(u8, nat)>::empty());
        assert(l1.last() == (r1, j1));
        assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<isa::Instr>::empty());
    }
    assert(super::templates::loads_seq(ls) =~= seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2)]);
}

/// `shape` with three loads, written out.
pub proof fn lemma_shape3(
    r1: u8,
    j1: nat,
    r2: u8,
    j2: nat,
    r3: u8,
    j3: nat,
    mid: Seq<isa::Instr>,
    ts: nat,
)
    ensures
        super::templates::shape(seq![(r1, j1), (r2, j2), (r3, j3)], mid, ts) == seq![
            super::templates::load_slot(r1, j1),
            super::templates::load_slot(r2, j2),
            super::templates::load_slot(r3, j3),
        ] + mid + seq![super::templates::store_slot(ts, x0())],
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
    assert(super::templates::loads_seq(Seq::<(u8, nat)>::empty()) == Seq::<isa::Instr>::empty());
    assert(super::templates::loads_seq(l1) =~= seq![super::templates::load_slot(r1, j1)]);
    assert(super::templates::loads_seq(l2) =~= seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2)]);
    assert(super::templates::loads_seq(ls) =~= seq![super::templates::load_slot(r1, j1), super::templates::load_slot(r2, j2), super::templates::load_slot(r3, j3)]);
}

/// `max_slots()` is 31.
pub proof fn lemma_abi_consts_t()
    ensures
        max_slots() == 31,
{
}

/// The concatenation of valid instruction lists is valid.
pub proof fn lemma_valid_concat(a: Seq<isa::Instr>, b: Seq<isa::Instr>)
    requires
        super::contract::all_valid_instrs(a),
        super::contract::all_valid_instrs(b),
    ensures
        super::contract::all_valid_instrs(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies isa::valid_instr(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// A load from or a store to a frame slot, through any register, is in the subset.
pub proof fn lemma_ls_valid(r: u8, j: nat)
    requires
        r < 32,
        j < max_slots(),
    ensures
        isa::valid_instr(super::templates::load_slot(r, j)),
        isa::valid_instr(super::templates::store_slot(j, r)),
{
    super::steps::lemma_slot_imm(j);
}

/// The loads of `ls` are valid when every register and slot is.
pub proof fn lemma_loads_valid(ls: Seq<(u8, nat)>)
    requires
        forall|k: int| 0 <= k < ls.len() ==> (#[trigger] ls[k]).0 < 32 && ls[k].1 < max_slots(),
    ensures
        super::contract::all_valid_instrs(super::templates::loads_seq(ls)),
    decreases ls.len(),
{
    if ls.len() > 0 {
        let pre = ls.drop_last();
        let last = ls.last();
        assert forall|k: int| 0 <= k < pre.len() implies (#[trigger] pre[k]).0 < 32 && pre[k].1
            < max_slots() by {
            assert(pre[k] == ls[k]);
        }
        lemma_loads_valid(pre);
        assert(last == ls[ls.len() - 1]);
        lemma_ls_valid(last.0, last.1);
        let one = seq![super::templates::load_slot(last.0, last.1)];
        assert(super::contract::all_valid_instrs(one)) by {
            assert forall|k: int| 0 <= k < one.len() implies isa::valid_instr(#[trigger] one[k]) by {
                assert(k == 0);
            }
        }
        lemma_valid_concat(super::templates::loads_seq(pre), one);
    }
}

/// A template with valid loads, a valid middle and a slot to store to is valid.
pub proof fn lemma_shape_valid(ls: Seq<(u8, nat)>, mid: Seq<isa::Instr>, ts: nat)
    requires
        forall|k: int| 0 <= k < ls.len() ==> (#[trigger] ls[k]).0 < 32 && ls[k].1 < max_slots(),
        super::contract::all_valid_instrs(mid),
        ts < max_slots(),
    ensures
        super::contract::all_valid_instrs(super::templates::shape(ls, mid, ts)),
{
    lemma_loads_valid(ls);
    lemma_ls_valid(0, ts);
    let st = seq![super::templates::store_slot(ts, x0())];
    assert(super::contract::all_valid_instrs(st)) by {
        assert forall|k: int| 0 <= k < st.len() implies isa::valid_instr(#[trigger] st[k]) by {
            assert(k == 0);
        }
    }
    lemma_valid_concat(super::templates::loads_seq(ls), mid);
    lemma_valid_concat(super::templates::loads_seq(ls) + mid, st);
}

/// The middle of an integer operator is one valid instruction.
pub proof fn lemma_int_op_valid(o: lir::IBin, sf: isa::Width)
    requires
        crate::spec::ibin_supported(o),
    ensures
        isa::valid_instr(super::templates::int_op_instr(o, sf)),
{
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
        lir::IBin::Rotl => {
            assert(false);
        },
        lir::IBin::Rotr => {
            assert(false);
        },
    }
}

/// The condition field of a `cset` is below 14.
pub proof fn lemma_cset_cond_ok(c: lir::ICmp)
    ensures
        super::templates::cset_cond(c) < 14,
{
    match c {
        lir::ICmp::Eq => {},
        lir::ICmp::Ne => {},
        lir::ICmp::LtS => {},
        lir::ICmp::LtU => {},
        lir::ICmp::GtS => {},
        lir::ICmp::GtU => {},
        lir::ICmp::LeS => {},
        lir::ICmp::LeU => {},
        lir::ICmp::GeS => {},
        lir::ICmp::GeU => {},
    }
}

/// Every middle of the first slice is a list of valid instructions.
pub proof fn lemma_mids_valid()
    ensures
        forall|c: lir::ICmp, sf: isa::Width|
            #[trigger] super::contract::all_valid_instrs(super::templates::cmp_mid(c, sf)),
        forall|sf: isa::Width| #[trigger] super::contract::all_valid_instrs(super::templates::eqz_mid(sf)),
        super::contract::all_valid_instrs(super::templates::neg_mid()),
        super::contract::all_valid_instrs(super::templates::abs_mid()),
        super::contract::all_valid_instrs(super::templates::exts_mid()),
        super::contract::all_valid_instrs(super::templates::wrap_mid()),
        super::contract::all_valid_instrs(super::templates::select_mid()),
        forall|v: lir::Val| #[trigger] super::contract::all_valid_instrs(super::templates::const_mid(v)),
{
    assert forall|c: lir::ICmp, sf: isa::Width|
        #[trigger] super::contract::all_valid_instrs(super::templates::cmp_mid(c, sf)) by {
        lemma_cset_cond_ok(c);
        let mid = super::templates::cmp_mid(c, sf);
        assert forall|k: int| 0 <= k < mid.len() implies isa::valid_instr(#[trigger] mid[k]) by {
            assert(k == 0 || k == 1);
        }
    }
    assert forall|sf: isa::Width| #[trigger] super::contract::all_valid_instrs(super::templates::eqz_mid(sf)) by {
        let mid = super::templates::eqz_mid(sf);
        assert forall|k: int| 0 <= k < mid.len() implies isa::valid_instr(#[trigger] mid[k]) by {
            assert(k == 0 || k == 1);
        }
    }
    let nm = super::templates::neg_mid();
    assert forall|k: int| 0 <= k < nm.len() implies isa::valid_instr(#[trigger] nm[k]) by {
        assert(k == 0 || k == 1);
    }
    let am = super::templates::abs_mid();
    assert forall|k: int| 0 <= k < am.len() implies isa::valid_instr(#[trigger] am[k]) by {
        assert(k == 0);
    }
    let em = super::templates::exts_mid();
    assert forall|k: int| 0 <= k < em.len() implies isa::valid_instr(#[trigger] em[k]) by {
        assert(k == 0);
    }
    let wm = super::templates::wrap_mid();
    assert forall|k: int| 0 <= k < wm.len() implies isa::valid_instr(#[trigger] wm[k]) by {
        assert(k == 0);
    }
    let sm = super::templates::select_mid();
    assert forall|k: int| 0 <= k < sm.len() implies isa::valid_instr(#[trigger] sm[k]) by {
        assert(k == 0 || k == 1);
    }
    assert forall|v: lir::Val| #[trigger] super::contract::all_valid_instrs(super::templates::const_mid(v)) by {
        let cm = super::templates::const_mid(v);
        assert forall|k: int| 0 <= k < cm.len() implies isa::valid_instr(#[trigger] cm[k]) by {
            match v {
                lir::Val::I32(c) => {
                    assert(k == 0 || k == 1);
                },
                lir::Val::I64(c) => {
                    assert(k == 0 || k == 1 || k == 2 || k == 3);
                },
                lir::Val::F64(c) => {
                    assert(k == 0 || k == 1 || k == 2 || k == 3);
                },
            }
        }
    }
}

/// **Every template is in the subset.**
pub proof fn lemma_tmpl_valid(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        super::contract::all_valid_instrs(super::templates::tmpl(op, nl, h)),
{
    lemma_abi_consts_t();
    lemma_mids_valid();
    let code = super::templates::tmpl(op, nl, h);
    match op {
        Op::Nop => {
            assert(super::contract::all_valid_instrs(code));
        },
        Op::Drop => {
            assert(super::contract::all_valid_instrs(code));
        },
        Op::Const(v) => {
            lemma_shape_valid(seq![], super::templates::const_mid(v), nl + h);
        },
        Op::LocalGet(x) => {
            lemma_shape_valid(seq![(x0(), x as nat)], seq![], nl + h);
        },
        Op::LocalSet(x) => {
            lemma_shape_valid(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::LocalTee(x) => {
            lemma_shape_valid(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::Select => {
            let t = (nl + h - 3) as nat;
            let ls = seq![(x0(), t), (x1(), t + 1), (x2(), t + 2)];
            assert forall|k: int| 0 <= k < ls.len() implies (#[trigger] ls[k]).0 < 32 && ls[k].1
                < max_slots() by {
                assert(k == 0 || k == 1 || k == 2);
            }
            lemma_shape_valid(ls, super::templates::select_mid(), t);
        },
        Op::Bin(b) => {
            let t = (nl + h - 2) as nat;
            let ls = seq![(x0(), t), (x1(), t + 1)];
            assert forall|k: int| 0 <= k < ls.len() implies (#[trigger] ls[k]).0 < 32 && ls[k].1
                < max_slots() by {
                assert(k == 0 || k == 1);
            }
            match b {
                lir::BinOp::I32(o) => {
                    lemma_int_op_valid(o, isa::Width::W32);
                    let mid = seq![super::templates::int_op_instr(o, isa::Width::W32)];
                    assert(super::contract::all_valid_instrs(mid)) by {
                        assert forall|k: int| 0 <= k < mid.len() implies isa::valid_instr(#[trigger] mid[k]) by {
                            assert(k == 0);
                        }
                    }
                    lemma_shape_valid(ls, mid, t);
                },
                lir::BinOp::I64(o) => {
                    lemma_int_op_valid(o, isa::Width::W64);
                    let mid = seq![super::templates::int_op_instr(o, isa::Width::W64)];
                    assert(super::contract::all_valid_instrs(mid)) by {
                        assert forall|k: int| 0 <= k < mid.len() implies isa::valid_instr(#[trigger] mid[k]) by {
                            assert(k == 0);
                        }
                    }
                    lemma_shape_valid(ls, mid, t);
                },
                lir::BinOp::I32Cmp(c) => {
                    lemma_shape_valid(ls, super::templates::cmp_mid(c, isa::Width::W32), t);
                },
                lir::BinOp::I64Cmp(c) => {
                    lemma_shape_valid(ls, super::templates::cmp_mid(c, isa::Width::W64), t);
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
            let ls = seq![(x0(), t)];
            assert forall|k: int| 0 <= k < ls.len() implies (#[trigger] ls[k]).0 < 32 && ls[k].1
                < max_slots() by {
                assert(k == 0);
            }
            match u {
                lir::UnOp::I32Eqz => {
                    lemma_shape_valid(ls, super::templates::eqz_mid(isa::Width::W32), t);
                },
                lir::UnOp::I64Eqz => {
                    lemma_shape_valid(ls, super::templates::eqz_mid(isa::Width::W64), t);
                },
                lir::UnOp::F64Neg => {
                    lemma_shape_valid(ls, super::templates::neg_mid(), t);
                },
                lir::UnOp::F64Abs => {
                    lemma_shape_valid(ls, super::templates::abs_mid(), t);
                },
                lir::UnOp::I64ExtendI32S => {
                    lemma_shape_valid(ls, super::templates::exts_mid(), t);
                },
                lir::UnOp::I32WrapI64 => {
                    lemma_shape_valid(ls, super::templates::wrap_mid(), t);
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

/// The code of a program is a list of valid instructions.
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
        lemma_valid_concat(
            super::templates::code_of(pre, nl, h0),
            super::templates::tmpl(last, nl, hl),
        );
    }
}

/// The exit sequence is a list of valid instructions.
pub proof fn lemma_exit_valid(c: u16)
    ensures
        super::contract::all_valid_instrs(exit_seq(c)),
{
    super::steps::lemma_abi_consts();
    assert forall|k: int| 0 <= k < exit_seq(c).len() implies isa::valid_instr(
        #[trigger] exit_seq(c)[k],
    ) by {
        assert(k == 0 || k == 1 || k == 2);
    }
}

} // verus!
