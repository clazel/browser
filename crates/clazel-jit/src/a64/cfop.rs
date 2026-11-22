//! The straight-line templates have no jumps, and run by `steps` as they do by
//! `run_seq`: the bridge from the first slice's [`refines`] to the
//! control-flow statement [`cf_refines`] for a straight-line instruction. The
//! A64 counterpart of [`crate::cfop`]; the facts about LIR's evaluation of a
//! straight-line instruction ([`crate::cfop::lemma_op_frame`]) are shared.

#[cfg(verus_only)]
use super::cfalg::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::contract::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[cfg(verus_only)]
use super::tlemmas::*;
#[cfg(verus_only)]
use crate::cfop::{lemma_op_frame, lemma_op_shape};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The two `op_ok`s agree (the x86-64 one, which [`cf_flow`] is written with,
/// and this back end's): the frames are the same.
pub proof fn lemma_op_ok_agrees(op: Op, nl: nat, h: nat)
    ensures
        crate::spec::op_ok(op, nl, h) == op_ok(op, nl, h),
{
    super::steps::lemma_frame_agrees();
}

/// The concatenation of jump-free lists is jump-free.
pub proof fn lemma_no_jumps_concat(a: Seq<isa::Instr>, b: Seq<isa::Instr>)
    requires
        no_jumps(a),
        no_jumps(b),
    ensures
        no_jumps(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies !is_jump(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// Loads of slots are jump-free.
pub proof fn lemma_loads_no_jumps(ls: Seq<(u8, nat)>)
    ensures
        no_jumps(loads_seq(ls)),
    decreases ls.len(),
{
    if ls.len() > 0 {
        lemma_loads_no_jumps(ls.drop_last());
        let one = seq![load_slot(ls.last().0, ls.last().1)];
        assert(no_jumps(one)) by {
            assert forall|k: int| 0 <= k < one.len() implies !is_jump(#[trigger] one[k]) by {
                assert(k == 0);
            }
        }
        lemma_no_jumps_concat(loads_seq(ls.drop_last()), one);
    }
}

/// A template with a jump-free middle is jump-free.
pub proof fn lemma_shape_no_jumps(ls: Seq<(u8, nat)>, mid: Seq<isa::Instr>, ts: nat)
    requires
        no_jumps(mid),
    ensures
        no_jumps(shape(ls, mid, ts)),
{
    lemma_loads_no_jumps(ls);
    let st = seq![store_slot(ts, x0())];
    assert(no_jumps(st)) by {
        assert forall|k: int| 0 <= k < st.len() implies !is_jump(#[trigger] st[k]) by {
            assert(k == 0);
        }
    }
    lemma_no_jumps_concat(loads_seq(ls), mid);
    lemma_no_jumps_concat(loads_seq(ls) + mid, st);
}

/// The middle of a supported integer operator is one jump-free instruction.
pub proof fn lemma_int_op_no_jump(o: lir::IBin, sf: isa::Width)
    requires
        crate::spec::ibin_supported(o),
    ensures
        no_jumps(seq![int_op_instr(o, sf)]),
{
    assert forall|k: int| 0 <= k < 1 implies !is_jump(#[trigger] seq![int_op_instr(o, sf)][k]) by {
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
}

/// Every middle of the first slice is jump-free.
pub proof fn lemma_mids_no_jumps()
    ensures
        forall|c: lir::ICmp, sf: isa::Width| #[trigger] no_jumps(cmp_mid(c, sf)),
        forall|sf: isa::Width| #[trigger] no_jumps(eqz_mid(sf)),
        no_jumps(neg_mid()),
        no_jumps(abs_mid()),
        no_jumps(exts_mid()),
        no_jumps(wrap_mid()),
        no_jumps(select_mid()),
        forall|v: lir::Val| #[trigger] no_jumps(const_mid(v)),
{
    assert forall|c: lir::ICmp, sf: isa::Width| #[trigger] no_jumps(cmp_mid(c, sf)) by {
        let mid = cmp_mid(c, sf);
        assert forall|k: int| 0 <= k < mid.len() implies !is_jump(#[trigger] mid[k]) by {
            assert(k == 0 || k == 1);
        }
    }
    assert forall|sf: isa::Width| #[trigger] no_jumps(eqz_mid(sf)) by {
        let mid = eqz_mid(sf);
        assert forall|k: int| 0 <= k < mid.len() implies !is_jump(#[trigger] mid[k]) by {
            assert(k == 0 || k == 1);
        }
    }
    let nm = neg_mid();
    assert forall|k: int| 0 <= k < nm.len() implies !is_jump(#[trigger] nm[k]) by {
        assert(k == 0 || k == 1);
    }
    let am = abs_mid();
    assert forall|k: int| 0 <= k < am.len() implies !is_jump(#[trigger] am[k]) by {
        assert(k == 0);
    }
    let em = exts_mid();
    assert forall|k: int| 0 <= k < em.len() implies !is_jump(#[trigger] em[k]) by {
        assert(k == 0);
    }
    let wm = wrap_mid();
    assert forall|k: int| 0 <= k < wm.len() implies !is_jump(#[trigger] wm[k]) by {
        assert(k == 0);
    }
    let sm = select_mid();
    assert forall|k: int| 0 <= k < sm.len() implies !is_jump(#[trigger] sm[k]) by {
        assert(k == 0 || k == 1);
    }
    assert forall|v: lir::Val| #[trigger] no_jumps(const_mid(v)) by {
        let cm = const_mid(v);
        assert forall|k: int| 0 <= k < cm.len() implies !is_jump(#[trigger] cm[k]) by {
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

/// No instruction of a template is a branch or `ret`.
pub proof fn lemma_tmpl_no_jumps(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        no_jumps(tmpl(op, nl, h)),
{
    lemma_mids_no_jumps();
    let code = tmpl(op, nl, h);
    match op {
        Op::Nop => {},
        Op::Drop => {},
        Op::Const(v) => {
            lemma_shape_no_jumps(seq![], const_mid(v), nl + h);
        },
        Op::LocalGet(x) => {
            lemma_shape_no_jumps(seq![(x0(), x as nat)], seq![], nl + h);
        },
        Op::LocalSet(x) => {
            lemma_shape_no_jumps(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::LocalTee(x) => {
            lemma_shape_no_jumps(seq![(x0(), (nl + h - 1) as nat)], seq![], x as nat);
        },
        Op::Select => {
            let t = (nl + h - 3) as nat;
            lemma_shape_no_jumps(
                seq![(x0(), t), (x1(), t + 1), (x2(), t + 2)],
                select_mid(),
                t,
            );
        },
        Op::Bin(b) => {
            let t = (nl + h - 2) as nat;
            let ls = seq![(x0(), t), (x1(), t + 1)];
            match b {
                lir::BinOp::I32(o) => {
                    lemma_int_op_no_jump(o, isa::Width::W32);
                    lemma_shape_no_jumps(ls, seq![int_op_instr(o, isa::Width::W32)], t);
                },
                lir::BinOp::I64(o) => {
                    lemma_int_op_no_jump(o, isa::Width::W64);
                    lemma_shape_no_jumps(ls, seq![int_op_instr(o, isa::Width::W64)], t);
                },
                lir::BinOp::I32Cmp(c) => {
                    lemma_shape_no_jumps(ls, cmp_mid(c, isa::Width::W32), t);
                },
                lir::BinOp::I64Cmp(c) => {
                    lemma_shape_no_jumps(ls, cmp_mid(c, isa::Width::W64), t);
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
            match u {
                lir::UnOp::I32Eqz => {
                    lemma_shape_no_jumps(ls, eqz_mid(isa::Width::W32), t);
                },
                lir::UnOp::I64Eqz => {
                    lemma_shape_no_jumps(ls, eqz_mid(isa::Width::W64), t);
                },
                lir::UnOp::F64Neg => {
                    lemma_shape_no_jumps(ls, neg_mid(), t);
                },
                lir::UnOp::F64Abs => {
                    lemma_shape_no_jumps(ls, abs_mid(), t);
                },
                lir::UnOp::I64ExtendI32S => {
                    lemma_shape_no_jumps(ls, exts_mid(), t);
                },
                lir::UnOp::I32WrapI64 => {
                    lemma_shape_no_jumps(ls, wrap_mid(), t);
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

/// `preserved` (nothing outside the exit area changed) is [`preserved_r`].
pub proof fn lemma_preserved_to_r(lay: lir::Layout, m: isa::State, m2: isa::State)
    requires
        preserved(m, m2),
    ensures
        preserved_r(lay, m, m2),
{
    assert(ctx_of(m2) == ctx_of(m)) by {
        super::steps::lemma_abi_consts();
    }
}

/// **A straight-line instruction's template refines it, in the control-flow
/// statement.** The first slice's [`refines`] (for the template, as one block
/// of code) becomes [`cf_refines`] for any labels: the base under the stack is
/// untouched (the frame lemma), and a run by [`run_seq`] of jump-free code is
/// a run by [`steps`].
#[verifier::rlimit(400)]
pub proof fn lemma_op_cf(op: Op, nl: nat, h: nat, offs: Seq<int>)
    requires
        op_ok(op, nl, h),
    ensures
        cf_refines(op@, nl, h, offs, tmpl(op, nl, h)),
{
    let code = tmpl(op, nl, h);
    super::proofs::lemma_op_refines(op, nl, h);
    lemma_tmpl_no_jumps(op, nl, h);
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, m, lir::eval(lay, op@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            code,
        ) implies cf_post(lay, base, nl, offs, code, m, lir::eval(lay, op@, a, fuel)) by {
        lemma_op_shape(op, lay, a, fuel);
        match lir::eval(lay, op@, a, fuel) {
            lir::Outcome::Normal(a2) => {
                lemma_rel_base_unfold(lay, base, a, m, nl);
                let ac = a.with_stack(base + a.stack);
                lemma_op_frame(op, lay, a, a2, base, fuel);
                let a2c = a2.with_stack(base + a2.stack);
                super::proofs::lemma_use_refines(op@, nl, h, code, lay, ac, m, fuel);
                assert(ac.stack.len() == h);
                assert(m.pc as int + code_len(code) < isa::p2(64));
                let m2 = run_seq(m, code).unwrap();
                assert(rel(lay, a2c, m2, nl) && m2.pc as int == m.pc as int + code_len(code)
                    && preserved(m, m2));
                assert(Seq::<isa::Instr>::empty() + code + Seq::<isa::Instr>::empty() =~= code);
                assert(code_len(Seq::<isa::Instr>::empty()) == 0);
                lemma_run_seq_steps(Seq::empty(), code, Seq::empty(), m.pc as int, m, m2);
                assert(reaches(code, m.pc as int, m, m2));
                lemma_preserved_to_r(lay, m, m2);
                lemma_table_pres(lay, m, m2);
                reveal(rel_base);
                assert(rel_base(lay, base, a2, m2, nl));
            },
            _ => {},
        }
    }
}

} // verus!
