//! The straight-line templates have no jumps, and run by `steps` as they do
//! by `run_seq`: the bridge from the first slice's [`refines`] to the
//! control-flow statement [`cf_refines`] for a straight-line instruction.

use crate::cfcontract::*;
use crate::cfspec::*;
use crate::cfsteps::*;
use crate::spec::*;
use crate::tlemmas::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// No instruction of a template is a jump or `ret`.
pub proof fn lemma_tmpl_no_jumps(op: Op, nl: nat, h: nat)
    requires
        op_ok(op, nl, h),
    ensures
        no_jumps(crate::templates::tmpl(op, nl, h)),
{
    assert(max_slots() == 31) by {
        lemma_abi_consts_t();
    }
    let code = crate::templates::tmpl(op, nl, h);
    assert forall|k: int| 0 <= k < code.len() implies !(#[trigger] code[k] is Jcc || code[k] is Jmp
        || code[k] is Ret) by {
        match op {
            Op::Nop => {},
            Op::Drop => {},
            Op::Const(v) => {
                lemma_shape0(seq![crate::templates::const_instr(v)], nl + h);
                lemma_ls_valid(0, nl + h);
                assert(code =~= seq![crate::templates::const_instr(v), crate::templates::store_slot(nl + h, rax())]);
            },
            Op::LocalGet(x) => {
                lemma_shape1(rax(), x as nat, seq![], nl + h);
                lemma_ls_valid(0, nl + h);
                lemma_ls_valid(0, x as nat);
                assert(code =~= seq![crate::templates::load_slot(rax(), x as nat), crate::templates::store_slot(nl + h, rax())]);
            },
            Op::LocalSet(x) => {
                lemma_shape1(rax(), (nl + h - 1) as nat, seq![], x as nat);
                lemma_ls_valid(0, x as nat);
                lemma_ls_valid(0, (nl + h - 1) as nat);
                assert(code =~= seq![crate::templates::load_slot(rax(), (nl + h - 1) as nat), crate::templates::store_slot(x as nat, rax())]);
            },
            Op::LocalTee(x) => {
                lemma_shape1(rax(), (nl + h - 1) as nat, seq![], x as nat);
                lemma_ls_valid(0, x as nat);
                lemma_ls_valid(0, (nl + h - 1) as nat);
                assert(code =~= seq![crate::templates::load_slot(rax(), (nl + h - 1) as nat), crate::templates::store_slot(x as nat, rax())]);
            },
            Op::Select => {
                let t = (nl + h - 3) as nat;
                lemma_shape3(rax(), t, rcx(), t + 1, rdx(), t + 2, crate::templates::select_mid(), t);
                lemma_ls_valid(0, t);
                lemma_ls_valid(1, t + 1);
                lemma_ls_valid(2, t + 2);
                assert(code =~= seq![
                    crate::templates::load_slot(rax(), t),
                    crate::templates::load_slot(rcx(), t + 1),
                    crate::templates::load_slot(rdx(), t + 2),
                    crate::templates::select_mid()[0],
                    crate::templates::select_mid()[1],
                    crate::templates::store_slot(t, rax()),
                ]);
            },
            Op::Bin(b) => {
                let t = (nl + h - 2) as nat;
                match b {
                    lir::BinOp::I32(o) => {
                        lemma_shape2(rax(), t, rcx(), t + 1, seq![crate::templates::int_op_instr(o, x64::Size::W32)], t);
                        lemma_ls_valid(0, t);
                        lemma_ls_valid(1, t + 1);
                        assert(code =~= seq![
                            crate::templates::load_slot(rax(), t),
                            crate::templates::load_slot(rcx(), t + 1),
                            crate::templates::int_op_instr(o, x64::Size::W32),
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::I64(o) => {
                        lemma_shape2(rax(), t, rcx(), t + 1, seq![crate::templates::int_op_instr(o, x64::Size::W64)], t);
                        lemma_ls_valid(0, t);
                        lemma_ls_valid(1, t + 1);
                        assert(code =~= seq![
                            crate::templates::load_slot(rax(), t),
                            crate::templates::load_slot(rcx(), t + 1),
                            crate::templates::int_op_instr(o, x64::Size::W64),
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::I32Cmp(c) => {
                        lemma_shape2(rcx(), t, rdx(), t + 1, crate::templates::cmp_mid(c, x64::Size::W32), t);
                        lemma_ls_valid(1, t);
                        lemma_ls_valid(2, t + 1);
                        lemma_ls_valid(0, t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rcx(), t),
                            crate::templates::load_slot(rdx(), t + 1),
                            crate::templates::cmp_mid(c, x64::Size::W32)[0],
                            crate::templates::cmp_mid(c, x64::Size::W32)[1],
                            crate::templates::cmp_mid(c, x64::Size::W32)[2],
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::BinOp::I64Cmp(c) => {
                        lemma_shape2(rcx(), t, rdx(), t + 1, crate::templates::cmp_mid(c, x64::Size::W64), t);
                        lemma_ls_valid(1, t);
                        lemma_ls_valid(2, t + 1);
                        lemma_ls_valid(0, t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rcx(), t),
                            crate::templates::load_slot(rdx(), t + 1),
                            crate::templates::cmp_mid(c, x64::Size::W64)[0],
                            crate::templates::cmp_mid(c, x64::Size::W64)[1],
                            crate::templates::cmp_mid(c, x64::Size::W64)[2],
                            crate::templates::store_slot(t, rax()),
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
                        lemma_shape1(rcx(), t, crate::templates::eqz_mid(x64::Size::W32), t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rcx(), t),
                            crate::templates::eqz_mid(x64::Size::W32)[0],
                            crate::templates::eqz_mid(x64::Size::W32)[1],
                            crate::templates::eqz_mid(x64::Size::W32)[2],
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I64Eqz => {
                        lemma_shape1(rcx(), t, crate::templates::eqz_mid(x64::Size::W64), t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rcx(), t),
                            crate::templates::eqz_mid(x64::Size::W64)[0],
                            crate::templates::eqz_mid(x64::Size::W64)[1],
                            crate::templates::eqz_mid(x64::Size::W64)[2],
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::F64Neg => {
                        lemma_shape1(rax(), t, crate::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000), t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rax(), t),
                            crate::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000)[0],
                            crate::templates::mask_mid(x64::AluOp::Xor, 0x8000_0000_0000_0000)[1],
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::F64Abs => {
                        lemma_shape1(rax(), t, crate::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF), t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rax(), t),
                            crate::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF)[0],
                            crate::templates::mask_mid(x64::AluOp::And, 0x7FFF_FFFF_FFFF_FFFF)[1],
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I64ExtendI32S => {
                        lemma_shape1(rax(), t, crate::templates::exts_mid(), t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rax(), t),
                            crate::templates::exts_mid()[0],
                            crate::templates::exts_mid()[1],
                            crate::templates::exts_mid()[2],
                            crate::templates::store_slot(t, rax()),
                        ]);
                    },
                    lir::UnOp::I32WrapI64 => {
                        lemma_shape1(rax(), t, crate::templates::wrap_mid(), t);
                        assert(code =~= seq![
                            crate::templates::load_slot(rax(), t),
                            crate::templates::wrap_mid()[0],
                            crate::templates::store_slot(t, rax()),
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



/// Taking `k` values off the top of a stack with a base under it.
pub proof fn lemma_below_cat(base: Seq<lir::Val>, s: Seq<lir::Val>, k: nat)
    requires
        k <= s.len(),
    ensures
        lir::below(base + s, k) =~= base + lir::below(s, k),
{
}

/// **A straight-line instruction's evaluation does not look below its
/// operands.** If it falls through from `a`, then from the same state with
/// a base under the stack it falls through to the same state with the same
/// base under the stack.
pub proof fn lemma_op_frame(
    op: Op,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    base: Seq<lir::Val>,
    fuel: nat,
)
    requires
        lir::eval(lay, op@, a, fuel) == lir::Outcome::Normal(a2),
    ensures
        lir::eval(lay, op@, a.with_stack(base + a.stack), fuel) == lir::Outcome::Normal(
            a2.with_stack(base + a2.stack),
        ),
{
    assert(fuel > 0);
    let ac = a.with_stack(base + a.stack);
    let n = a.stack.len();
    let nc = ac.stack.len();
    assert(nc == base.len() + n);
    match op {
        Op::Nop => {},
        Op::Const(v) => {
            assert((base + a.stack).push(v) =~= base + a.stack.push(v));
        },
        Op::LocalGet(x) => {
            assert((base + a.stack).push(a.locals[x as int]) =~= base + a.stack.push(
                a.locals[x as int],
            ));
        },
        Op::LocalSet(x) => {
            assert(n >= 1);
            assert((base + a.stack)[nc - 1] == a.stack[n - 1]);
            assert((base + a.stack).drop_last() =~= base + a.stack.drop_last());
        },
        Op::LocalTee(x) => {
            assert(n >= 1);
            assert((base + a.stack)[nc - 1] == a.stack[n - 1]);
        },
        Op::Drop => {
            assert(n >= 1);
            assert((base + a.stack).drop_last() =~= base + a.stack.drop_last());
        },
        Op::Select => {
            assert(n >= 3);
            assert((base + a.stack)[nc - 1] == a.stack[n - 1]);
            assert((base + a.stack)[nc - 2] == a.stack[n - 2]);
            assert((base + a.stack)[nc - 3] == a.stack[n - 3]);
            lemma_below_cat(base, a.stack, 3);
            match a.stack[n - 1] {
                lir::Val::I32(c) => {
                    let v = if c != 0 {
                        a.stack[n - 3]
                    } else {
                        a.stack[n - 2]
                    };
                    assert(lir::below(base + a.stack, 3).push(v) =~= base + lir::below(
                        a.stack,
                        3,
                    ).push(v));
                },
                _ => {
                    assert(false);
                },
            }
        },
        Op::Bin(b) => {
            assert(n >= 2);
            assert((base + a.stack)[nc - 1] == a.stack[n - 1]);
            assert((base + a.stack)[nc - 2] == a.stack[n - 2]);
            lemma_below_cat(base, a.stack, 2);
            match lir::bin_eval(b, a.stack[n - 2], a.stack[n - 1]) {
                Some(v) => {
                    assert(lir::below(base + a.stack, 2).push(v) =~= base + lir::below(
                        a.stack,
                        2,
                    ).push(v));
                },
                None => {
                    assert(false);
                },
            }
        },
        Op::Un(u) => {
            assert(n >= 1);
            assert((base + a.stack)[nc - 1] == a.stack[n - 1]);
            lemma_below_cat(base, a.stack, 1);
            match lir::un_eval(u, a.stack[n - 1]) {
                Some(v) => {
                    assert(lir::below(base + a.stack, 1).push(v) =~= base + lir::below(
                        a.stack,
                        1,
                    ).push(v));
                },
                None => {
                    assert(false);
                },
            }
        },
    }
}

/// A straight-line instruction's evaluation is a fall-through, stuck, or out
/// of fuel: never a branch or an exit.
pub proof fn lemma_op_shape(op: Op, lay: lir::Layout, a: lir::St, fuel: nat)
    ensures
        !(lir::eval(lay, op@, a, fuel) is Branch),
        !(lir::eval(lay, op@, a, fuel) is Exit),
{
    if fuel > 0 {
        match op {
            Op::Select => {
                let n = a.stack.len();
                if n >= 3 {
                    match a.stack[n - 1] {
                        lir::Val::I32(c) => {},
                        _ => {},
                    }
                }
            },
            Op::Bin(b) => {
                let n = a.stack.len();
                if n >= 2 {
                    match lir::bin_eval(b, a.stack[n - 2], a.stack[n - 1]) {
                        Some(v) => {},
                        None => {},
                    }
                }
            },
            Op::Un(u) => {
                let n = a.stack.len();
                if n >= 1 {
                    match lir::un_eval(u, a.stack[n - 1]) {
                        Some(v) => {},
                        None => {},
                    }
                }
            },
            _ => {},
        }
    }
}

/// `preserved` (nothing outside the exit area changed) is [`preserved_r`].
pub proof fn lemma_preserved_to_r(lay: lir::Layout, m: x64::State, m2: x64::State)
    requires
        preserved(m, m2),
    ensures
        preserved_r(lay, m, m2),
{
    assert(ctx_of(m2) == ctx_of(m)) by {
        crate::steps::lemma_abi_consts();
    }
}

/// **A straight-line instruction's template refines it, in the
/// control-flow statement.** The first slice's [`refines`] (for the template,
/// as one block of code) becomes [`cf_refines`] for any labels: the base
/// under the stack is untouched (the frame lemma), and a run by
/// [`run_seq`] of jump-free code is a run by [`steps`].
#[verifier::rlimit(400)]
pub proof fn lemma_op_cf(op: Op, nl: nat, h: nat, offs: Seq<int>)
    requires
        op_ok(op, nl, h),
    ensures
        cf_refines(op@, nl, h, offs, crate::templates::tmpl(op, nl, h)),
{
    let code = crate::templates::tmpl(op, nl, h);
    crate::proofs::lemma_op_refines(op, nl, h);
    lemma_tmpl_no_jumps(op, nl, h);
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, op@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, code) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        cu,
        m,
        lir::eval(lay, op@, a, fuel),
    ) by {
        lemma_op_shape(op, lay, a, fuel);
        match lir::eval(lay, op@, a, fuel) {
            lir::Outcome::Normal(a2) => {
                crate::cfalg::lemma_rel_base_unfold(lay, base, a, m, nl);
                let ac = a.with_stack(base + a.stack);
                lemma_op_frame(op, lay, a, a2, base, fuel);
                let a2c = a2.with_stack(base + a2.stack);
                crate::proofs::lemma_use_refines(op@, nl, h, code, lay, cu, ac, m, fuel);
                assert(ac.stack.len() == h);
                assert(x64::canonical(m.rip + code_len(code)));
                let m2 = run_seq(cu, m, code).unwrap();
                assert(rel(lay, a2c, m2, nl) && m2.rip == m.rip + code_len(code) && preserved(
                    m,
                    m2,
                ));
                assert(Seq::<x64::Instr>::empty() + code + Seq::<x64::Instr>::empty() =~= code);
                assert(code_len(Seq::<x64::Instr>::empty()) == 0);
                lemma_run_seq_steps(cu, Seq::empty(), code, Seq::empty(), m.rip, m, m2);
                assert(reaches(cu, code, m.rip, m, m2));
                lemma_preserved_to_r(lay, m, m2);
                crate::cfalg::lemma_table_pres(lay, m, m2);
                reveal(rel_base);
                assert(rel_base(lay, base, a2, m2, nl));
            },
            _ => {},
        }
    }
}

} // verus!
