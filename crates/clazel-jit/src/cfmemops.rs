//! **`load` and `store` refine their LIR instructions**
//! ([`crate::cfcontract::cf_refines`]), from the pieces: the operands, the
//! bounds check ([`crate::cfcheckrun`]), the access ([`crate::cfmemacc`]) and
//! the shape of the run ([`crate::cfmemflow`]). When the check fails LIR is
//! `Stuck` and nothing is claimed.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfcheck::*;
#[cfg(verus_only)]
use crate::cfcheckrun::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cfmem::*;
#[cfg(verus_only)]
use crate::cfmemacc::*;
#[cfg(verus_only)]
use crate::cfmemflow::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfmemsteps::*;
#[cfg(verus_only)]
use crate::cfop::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `ty_size` of the LIR type is the access size.
pub proof fn lemma_ty_size(ty: MTy)
    ensures
        lir::ty_size(ty.lir_ty()) == ty.size(),
        ty.size() >= 4,
{
}

/// **`t.load`.**
#[verifier::rlimit(1500)]
pub proof fn lemma_load_cf(region: usize, ty: MTy, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        region < 16,
    ensures
        cf_refines(
            MemOp::Load { region, ty }@,
            nl,
            h,
            offs,
            mem_code(MemOp::Load { region, ty }, nl, h),
        ),
{
    let mo = MemOp::Load { region, ty };
    let k = region as nat;
    let sz = ty.size();
    lemma_ty_size(ty);
    lemma_mem_parts_len(mo, nl, h);
    let pre = mem_pre(mo, nl, h);
    let cs = mem_check(mo, nl, h);
    let tail = mem_tail(mo, nl, h);
    let stub = exit_seq(trap_code());
    let r1 = mem_r1(mo, nl, h);
    let r2 = mem_r2(mo, nl, h);
    let whole = mem_code(mo, nl, h);
    assert(whole == flow_code(pre, cs, tail, stub));
    lemma_stub_start(pre, cs, tail, stub);
    let tl = code_len(tail);
    assert(code_len(pre) == 16 && code_len(cs) == 47 && code_len(stub) == 14);
    assert(tl == 15 || tl == 16);
    assert(code_len(whole) == 82 + tl);
    let j = (nl + h - 1) as nat;
    let i1 = load_slot(rcx(), j);
    let i2 = x64::Instr::MovLoad { sz: x64::Size::W64, dst: rsi(), mem: base_mem(k) };
    assert(pre =~= seq![i1, i2]);
    assert(no_jumps(pre)) by {
        assert forall|q: int| 0 <= q < pre.len() implies !(#[trigger] pre[q] is Jcc || pre[q]
            is Jmp || pre[q] is Ret) by {
            assert(q == 0 || q == 1);
        }
    }
    assert(no_jumps(tail)) by {
        let t1 = x64::Instr::MovLoad { sz: mty_sz(ty), dst: rax(), mem: ix_mem() };
        assert(tail =~= seq![t1, store_slot(j, rax())]);
        assert forall|q: int| 0 <= q < tail.len() implies !(#[trigger] tail[q] is Jcc || tail[q]
            is Jmp || tail[q] is Ret) by {
            assert(q == 0 || q == 1);
        }
    }
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, whole, cu, m, lir::eval(lay, mo@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, whole) implies cf_post(
        lay,
        base,
        nl,
        offs,
        whole,
        cu,
        m,
        lir::eval(lay, mo@, a, fuel),
    ) by {
        let n0 = a.stack.len();
        if fuel > 0 && n0 >= 1 && k < lay.len() {
            match a.stack[(n0 - 1) as int] {
                lir::Val::I64(ix) => {
                    let bound = lay[k as int].bound;
                    if ix as nat + sz <= bound {
                        lemma_rel_base_unfold(lay, base, a, m, nl);
                        let ac = a.with_stack(base + a.stack);
                        assert(ac.stack[(h - 1) as int] == lir::Val::I64(ix));
                        super::steps::lemma_abi_consts();
                        let big = code_len(whole);
                        assert(x64::canonical(m.rip + big));
                        super::runseq::lemma_canonical_between(m.rip, m.rip + 8, m.rip + big);
                        super::runseq::lemma_canonical_between(m.rip, m.rip + 16, m.rip + big);
                        // the operands
                        super::rel::lemma_load_rel(cu, lay, ac, m, 1, j, nl);
                        let m1 = x64::step(cu, m, i1).unwrap();
                        assert(m1.rgf[1] as int == ix as int);
                        assert(table_ok(lay, m1)) by {
                            assert(ctx_of(m1) == ctx_of(m));
                        }
                        assert(x64::wf(m1) && ctx_ok(m1));
                        lemma_table_words(lay, m1, k);
                        let base_w = lay[k as int].base;
                        assert(x64::nbytes(x64::Size::W64) == 8);
                        assert(x64::eff_addr(m1, base_mem(k)) == x64::eff_addr(m1, base_mem(k)));
                        lemma_step_movload(cu, m1, x64::Size::W64, 6, base_mem(k), base_w as int);
                        let m2 = x64::step(cu, m1, i2).unwrap();
                        lemma_mem_instr_lens(j, k);
                        super::memlemmas::lemma_p2_consts();
                        assert(m2.rgf == m1.rgf.update(6, base_w as u64)) by {
                            vstd::arithmetic::div_mod::lemma_small_mod(
                                base_w,
                                0x1_0000_0000_0000_0000nat,
                            );
                        }
                        assert(m2.mem == m.mem && m2.xmm == m1.xmm && m2.rip == m.rip + 16);
                        let f = super::runseq::stepper(cu);
                        super::runseq::lemma_gen2(f, m, i1, i2, m1, m2);
                        super::runseq::lemma_run_seq_is_gen(cu, m, pre);
                        assert(run_seq(cu, m, pre) == Some(m2));
                        super::rel::lemma_rel_regs(lay, ac, m1, m2, nl);
                        assert(table_ok(lay, m2)) by {
                            assert(ctx_of(m2) == ctx_of(m));
                        }
                        assert(m2.rgf[1] as int == ix as int && m2.rgf[6] as int == base_w as int);
                        // the check
                        assert(r1 == 36 + tl && r2 == 22 + tl);
                        super::runseq::lemma_canonical_between(m.rip, m2.rip + 47, m.rip + big);
                        super::runseq::lemma_canonical_between(
                            m.rip,
                            m2.rip + 16 + r1,
                            m.rip + big,
                        );
                        super::runseq::lemma_canonical_between(
                            m.rip,
                            m2.rip + 30 + r2,
                            m.rip + big,
                        );
                        lemma_check_run(cu, lay, m2, k, sz, r1, r2);
                        let mb = choose|q: x64::State|
                            reaches(cu, cs, m2.rip, m2, q) && q.rip == m2.rip + 47 && keeps(m2, q)
                                && q.rgf[1] == m2.rgf[1];
                        super::rel::lemma_rel_regs(lay, ac, m2, mb, nl);
                        assert(mb.rgf[6] as int == base_w as int);
                        // the access
                        super::runseq::lemma_canonical_between(m.rip, mb.rip + 16, m.rip + big);
                        lemma_load_access(cu, lay, ac, m, mb, nl, h, k, ty, ix);
                        let m4 = run_seq(cu, mb, tail).unwrap();
                        lemma_flow_pass(cu, pre, cs, tail, stub, m, m2, mb, m4);
                        let me = x64::State { rip: m.rip + big, ..m4 };
                        // LIR's result
                        let a2 = a.with_stack(
                            lir::below(a.stack, 1).push(
                                lir::val_of_bits(
                                    ty.lir_ty(),
                                    lir::read_le(
                                        a.mem,
                                        lay[k as int].base + lir::masked(bound, ix as nat),
                                        sz,
                                    ),
                                ),
                            ),
                        );
                        assert(lir::eval(lay, mo@, a, fuel) == lir::Outcome::Normal(a2));
                        let a2c = a2.with_stack(base + a2.stack);
                        let res = load_result(lay, ac, k, ty, ix);
                        assert(ac.mem == a.mem);
                        assert(a2c.stack =~= res.stack) by {
                            lemma_below_cat(base, a.stack, 1);
                            let v = lir::val_of_bits(
                                ty.lir_ty(),
                                lir::read_le(
                                    a.mem,
                                    lay[k as int].base + lir::masked(bound, ix as nat),
                                    sz,
                                ),
                            );
                            assert((base + lir::below(a.stack, 1)).push(v) =~= base
                                + lir::below(a.stack, 1).push(v));
                        }
                        assert(a2c == res);
                        assert(me.mem == m4.mem && me.rgf == m4.rgf);
                        super::rel::lemma_rel_regs(lay, res, m4, me, nl);
                        assert(preserved(m, me));
                        lemma_preserved_to_r(lay, m, me);
                        lemma_table_pres(lay, m, me);
                        reveal(rel_base);
                        assert(rel_base(lay, base, a2, me, nl));
                    }
                },
                _ => {},
            }
        }
    }
}

/// **`t.store`.**
#[verifier::rlimit(1500)]
pub proof fn lemma_store_cf(region: usize, ty: MTy, nl: nat, h: nat, offs: Seq<int>)
    requires
        2 <= h,
        nl + h <= max_slots(),
        region < 16,
    ensures
        cf_refines(
            MemOp::Store { region, ty }@,
            nl,
            h,
            offs,
            mem_code(MemOp::Store { region, ty }, nl, h),
        ),
{
    let mo = MemOp::Store { region, ty };
    let k = region as nat;
    let sz = ty.size();
    lemma_ty_size(ty);
    lemma_mem_parts_len(mo, nl, h);
    let pre = mem_pre(mo, nl, h);
    let cs = mem_check(mo, nl, h);
    let tail = mem_tail(mo, nl, h);
    let stub = exit_seq(trap_code());
    let r1 = mem_r1(mo, nl, h);
    let r2 = mem_r2(mo, nl, h);
    let whole = mem_code(mo, nl, h);
    assert(whole == flow_code(pre, cs, tail, stub));
    lemma_stub_start(pre, cs, tail, stub);
    let tl = code_len(tail);
    assert(code_len(pre) == 24 && code_len(cs) == 47 && code_len(stub) == 14);
    assert(tl == 7 || tl == 8);
    assert(code_len(whole) == 90 + tl);
    let j = (nl + h - 1) as nat;
    let j2 = (nl + h - 2) as nat;
    let i1 = load_slot(rdi(), j);
    let i2 = load_slot(rcx(), j2);
    let i3 = x64::Instr::MovLoad { sz: x64::Size::W64, dst: rsi(), mem: base_mem(k) };
    assert(pre =~= seq![i1, i2, i3]);
    assert(no_jumps(pre)) by {
        assert forall|q: int| 0 <= q < pre.len() implies !(#[trigger] pre[q] is Jcc || pre[q]
            is Jmp || pre[q] is Ret) by {
            assert(q == 0 || q == 1 || q == 2);
        }
    }
    assert(no_jumps(tail)) by {
        let t1 = x64::Instr::MovStore { sz: mty_sz(ty), mem: ix_mem(), src: rdi() };
        assert(tail =~= seq![t1]);
        assert forall|q: int| 0 <= q < tail.len() implies !(#[trigger] tail[q] is Jcc || tail[q]
            is Jmp || tail[q] is Ret) by {
            assert(q == 0);
        }
    }
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, whole, cu, m, lir::eval(lay, mo@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, whole) implies cf_post(
        lay,
        base,
        nl,
        offs,
        whole,
        cu,
        m,
        lir::eval(lay, mo@, a, fuel),
    ) by {
        let n0 = a.stack.len();
        if fuel > 0 && n0 >= 2 && k < lay.len() && lir::val_has_base_ty(
            a.stack[(n0 - 1) as int],
            ty.lir_ty(),
        ) {
            match a.stack[(n0 - 2) as int] {
                lir::Val::I64(ix) => {
                    let bound = lay[k as int].bound;
                    let v = a.stack[(n0 - 1) as int];
                    if ix as nat + sz <= bound {
                        lemma_rel_base_unfold(lay, base, a, m, nl);
                        let ac = a.with_stack(base + a.stack);
                        assert(ac.stack[(h - 1) as int] == v);
                        assert(ac.stack[(h - 2) as int] == lir::Val::I64(ix));
                        super::steps::lemma_abi_consts();
                        let big = code_len(whole);
                        assert(x64::canonical(m.rip + big));
                        super::runseq::lemma_canonical_between(m.rip, m.rip + 8, m.rip + big);
                        super::runseq::lemma_canonical_between(m.rip, m.rip + 16, m.rip + big);
                        super::runseq::lemma_canonical_between(m.rip, m.rip + 24, m.rip + big);
                        // the operands
                        super::rel::lemma_load_rel(cu, lay, ac, m, 7, j, nl);
                        let m1 = x64::step(cu, m, i1).unwrap();
                        assert(m1.rgf[7] as nat == lir::val_bits(v));
                        super::rel::lemma_load_rel(cu, lay, ac, m1, 1, j2, nl);
                        let m2 = x64::step(cu, m1, i2).unwrap();
                        assert(m2.rgf[1] as int == ix as int);
                        assert(m2.rgf[7] == m1.rgf[7]);
                        assert(table_ok(lay, m2)) by {
                            assert(ctx_of(m2) == ctx_of(m));
                        }
                        assert(x64::wf(m2) && ctx_ok(m2));
                        lemma_table_words(lay, m2, k);
                        let base_w = lay[k as int].base;
                        assert(x64::nbytes(x64::Size::W64) == 8);
                        lemma_step_movload(cu, m2, x64::Size::W64, 6, base_mem(k), base_w as int);
                        let m3 = x64::step(cu, m2, i3).unwrap();
                        lemma_mem_instr_lens(j, k);
                        super::memlemmas::lemma_p2_consts();
                        assert(m3.rgf == m2.rgf.update(6, base_w as u64)) by {
                            vstd::arithmetic::div_mod::lemma_small_mod(
                                base_w,
                                0x1_0000_0000_0000_0000nat,
                            );
                        }
                        assert(m3.mem == m.mem && m3.xmm == m2.xmm && m3.rip == m.rip + 24);
                        let f = super::runseq::stepper(cu);
                        super::runseq::lemma_gen3(f, m, i1, i2, i3, m1, m2, m3);
                        super::runseq::lemma_run_seq_is_gen(cu, m, pre);
                        assert(run_seq(cu, m, pre) == Some(m3));
                        super::rel::lemma_rel_regs(lay, ac, m2, m3, nl);
                        assert(table_ok(lay, m3)) by {
                            assert(ctx_of(m3) == ctx_of(m));
                        }
                        assert(m3.rgf[1] as int == ix as int && m3.rgf[6] as int == base_w as int);
                        assert(m3.rgf[7] as nat == lir::val_bits(v));
                        // the check
                        assert(r1 == 36 + tl && r2 == 22 + tl);
                        super::runseq::lemma_canonical_between(m.rip, m3.rip + 47, m.rip + big);
                        super::runseq::lemma_canonical_between(
                            m.rip,
                            m3.rip + 16 + r1,
                            m.rip + big,
                        );
                        super::runseq::lemma_canonical_between(
                            m.rip,
                            m3.rip + 30 + r2,
                            m.rip + big,
                        );
                        lemma_check_run(cu, lay, m3, k, sz, r1, r2);
                        let mb = choose|q: x64::State|
                            reaches(cu, cs, m3.rip, m3, q) && q.rip == m3.rip + 47 && keeps(m3, q)
                                && q.rgf[1] == m3.rgf[1];
                        super::rel::lemma_rel_regs(lay, ac, m3, mb, nl);
                        assert(mb.rgf[6] as int == base_w as int && mb.rgf[7] == m3.rgf[7]);
                        // the access
                        super::runseq::lemma_canonical_between(m.rip, mb.rip + 8, m.rip + big);
                        lemma_store_access(cu, lay, ac, m, mb, nl, h, k, ty, ix, v);
                        let m4 = run_seq(cu, mb, tail).unwrap();
                        lemma_flow_pass(cu, pre, cs, tail, stub, m, m3, mb, m4);
                        let me = x64::State { rip: m.rip + big, ..m4 };
                        // LIR's result
                        let a2 = a.with_stack(lir::below(a.stack, 2)).with_mem(
                            lir::write_le(
                                a.mem,
                                lay[k as int].base + lir::masked(bound, ix as nat),
                                lir::val_bits(v),
                                sz,
                            ),
                        );
                        assert(lir::eval(lay, mo@, a, fuel) == lir::Outcome::Normal(a2));
                        let a2c = a2.with_stack(base + a2.stack);
                        let res = store_result(lay, ac, k, ty, ix, v);
                        assert(ac.mem == a.mem);
                        assert(a2c.stack =~= res.stack) by {
                            lemma_below_cat(base, a.stack, 2);
                        }
                        assert(a2c == res);
                        assert(me.mem == m4.mem && me.rgf == m4.rgf);
                        super::rel::lemma_rel_regs(lay, res, m4, me, nl);
                        assert(preserved_r(lay, m, me));
                        lemma_table_pres(lay, m, me);
                        reveal(rel_base);
                        assert(rel_base(lay, base, a2, me, nl));
                    }
                },
                _ => {},
            }
        }
    }
}

} // verus!
