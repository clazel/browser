//! **`bounds_check`, `load` and `store` refine their LIR instructions**, in
//! the control-flow statement ([`cf_refines`]): the code is
//! [`crate::cftemplates::mem_code`], with the validator's bounds-check
//! sequence. [`crate::cfcheckrun`] runs the check, [`crate::cfmemflow`] the
//! shape around it, [`crate::cfmemrel`] relates memory (`mem_rel`).

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
use crate::cfexit::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfmemflow::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfmemrel::*;
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

/// `preserved_mem` (only the exit area changed) is `preserved_mem_r`.
pub proof fn lemma_pm_to_pmr(lay: lir::Layout, m: x64::State, m2: x64::State)
    requires
        preserved_mem(m, m2),
    ensures
        preserved_mem_r(lay, m, m2),
{
}

/// **The state a run of register-only code and a `jmp` leaves**, related to
/// the same LIR state, with everything preserved: `m2` has the memory and
/// context register of `m`.
pub proof fn lemma_regs_only(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m2: x64::State,
    nl: nat,
)
    requires
        rel_base(lay, base, a, m, nl),
        m2.mem == m.mem,
        m2.rgf.len() == 16,
        m2.xmm.len() == 16,
        m2.rgf[15] == m.rgf[15],
        m2.rgf[4] == m.rgf[4],
        x64::canonical(m2.rip),
        m.rgf.len() == 16,
    ensures
        rel_base(lay, base, a, m2, nl),
        preserved_r(lay, m, m2),
{
    lemma_rel_base_same(lay, base, a, m, m2, nl);
    lemma_preserved_same(lay, m, m2);
}

/// **`bounds_check`.**
#[verifier::rlimit(1000)]
pub proof fn lemma_bc_cf(region: usize, size: usize, code: u32, nl: nat, h: nat, offs: Seq<int>)
    requires
        1 <= h,
        nl + h <= max_slots(),
        region < 16,
        1 <= size <= 8,
    ensures
        cf_refines(
            MemOp::BoundsCheck { region, size, code }@,
            nl,
            h,
            offs,
            mem_code(MemOp::BoundsCheck { region, size, code }, nl, h),
        ),
{
    let mo = MemOp::BoundsCheck { region, size, code };
    let k = region as nat;
    let n = size as nat;
    lemma_mem_parts_len(mo, nl, h);
    let pre = mem_pre(mo, nl, h);
    let cs = mem_check(mo, nl, h);
    let tail = mem_tail(mo, nl, h);
    let stub = exit_seq(code);
    let r1 = mem_r1(mo, nl, h);
    let r2 = mem_r2(mo, nl, h);
    let whole = mem_code(mo, nl, h);
    assert(whole == flow_code(pre, cs, tail, stub));
    lemma_stub_start(pre, cs, tail, stub);
    assert(code_len(pre) == 8 && code_len(tail) == 0 && code_len(cs) == 47 && code_len(stub) == 14);
    assert(code_len(whole) == 74);
    assert(r1 == 36 && r2 == 22);
    assert(no_jumps(pre) && no_jumps(tail)) by {
        assert forall|j: int| 0 <= j < pre.len() implies !(#[trigger] pre[j] is Jcc || pre[j] is Jmp
            || pre[j] is Ret) by {
            assert(j == 0);
        }
        assert(tail.len() == 0);
    }
    let i1 = load_slot(rcx(), (nl + h - 1) as nat);
    assert(pre =~= seq![i1]);
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
                    lemma_rel_base_unfold(lay, base, a, m, nl);
                    let ac = a.with_stack(base + a.stack);
                    let j = (nl + h - 1) as nat;
                    assert(ac.stack[(h - 1) as int] == lir::Val::I64(ix));
                    assert(x64::canonical(m.rip + 74));
                    super::runseq::lemma_canonical_between(m.rip, m.rip + 8, m.rip + 74);
                    super::steps::lemma_abi_consts();
                    // the operand
                    super::rel::lemma_load_rel(cu, lay, ac, m, 1, j, nl);
                    let m1 = x64::step(cu, m, i1).unwrap();
                    assert(m1.rgf[1] as int == ix as int);
                    assert(run_seq(cu, m, pre) == Some(m1)) by {
                        super::runseq::lemma_run_seq_one(cu, m, i1);
                    }
                    assert(m1.rgf.len() == 16 && m1.xmm.len() == 16);
                    assert(table_ok(lay, m1)) by {
                        assert(ctx_of(m1) == ctx_of(m));
                    }
                    lemma_plain_reaches(cu, pre, m, m1);
                    assert(m1.rip == m.rip + 8);
                    // the check
                    super::runseq::lemma_canonical_between(m.rip, m1.rip + 47, m.rip + 74);
                    super::runseq::lemma_canonical_between(m.rip, m1.rip + 16 + r1, m.rip + 74);
                    super::runseq::lemma_canonical_between(m.rip, m1.rip + 30 + r2, m.rip + 74);
                    lemma_check_run(cu, lay, m1, k, n, r1, r2);
                    let bound = lay[k as int].bound;
                    assert(lir::eval(lay, mo@, a, fuel) == if ix as nat + n <= bound {
                        lir::Outcome::Normal(a)
                    } else {
                        lir::Outcome::Exit(
                            code as nat,
                            seq![],
                            a.with_stack(lir::below(a.stack, 1)),
                        )
                    });
                    if ix as nat + n <= bound {
                        let mb = choose|m2: x64::State|
                            reaches(cu, cs, m1.rip, m1, m2) && m2.rip == m1.rip + 47 && keeps(
                                m1,
                                m2,
                            ) && m2.rgf[1] == m1.rgf[1];
                        assert(run_seq(cu, mb, tail) == Some(mb));
                        lemma_flow_pass(cu, pre, cs, tail, stub, m, m1, mb, mb);
                        let me = x64::State { rip: m.rip + 74, ..mb };
                        assert(reaches(cu, whole, m.rip, m, me));
                        assert(me.mem == m.mem && me.rgf == mb.rgf);
                        lemma_regs_only(lay, base, a, m, me, nl);
                        assert(reaches(cu, whole, m.rip, m, me));
                    } else {
                        let ms = choose|m2: x64::State|
                            reaches(cu, cs, m1.rip, m1, m2) && (m2.rip == m1.rip + 16 + r1
                                || m2.rip == m1.rip + 30 + r2) && keeps(m1, m2) && m2.rgf[1]
                                == m1.rgf[1];
                        assert(ms.rip == m.rip + 60);
                        lemma_flow_fail(cu, pre, cs, tail, stub, m, m1, ms);
                        assert(ms.rgf[4] == m.rgf[4] && ms.rgf[15] == m.rgf[15]);
                        lemma_regs_only(lay, base, a, m, ms, nl);
                        lemma_rel_base_unfold(lay, base, a, ms, nl);
                        lemma_stack_pres(lay, m, ms);
                        assert(stack_ok_r(lay, ms));
                        assert(x64::canonical(ms.rip + code_len(exit_seq(code))));
                        lemma_exit_reach(code, nl, lay, cu, ac, ms);
                        let m2 = choose|m2: x64::State|
                            reaches(cu, exit_seq(code), ms.rip, ms, m2) && exit_done(
                                ms,
                                m2,
                                code as nat,
                            ) && rel(lay, ac, m2, nl) && preserved_mem(ms, m2);
                        let head = pre + cs + tail + seq![jmp_i(code_len(stub) as int)];
                        assert(whole =~= head + stub + Seq::<x64::Instr>::empty());
                        super::runseq::lemma_code_len_append(head, stub);
                        assert(code_len(head) == 60);
                        lemma_embed_mid(cu, head, stub, Seq::empty(), m.rip, ms, m2);
                        lemma_reaches_trans(cu, whole, m.rip, m, ms, m2);
                        // the outcome
                        let s = a.with_stack(lir::below(a.stack, 1));
                        lemma_pm_to_pmr(lay, ms, m2);
                        lemma_pmr_trans(lay, m, ms, m2);
                        lemma_table_pres(lay, m, m2);
                        assert((base + a.stack).take((base + s.stack).len() as int) =~= base
                            + s.stack);
                        lemma_rel_prefix(lay, a, base + a.stack, base + s.stack, m2, nl);
                        assert(s.with_stack(base + s.stack) == a.with_stack(base + s.stack));
                        reveal(rel_base);
                        assert(base + Seq::<lir::Val>::empty() =~= base);
                        assert(rel_base(lay, base + Seq::<lir::Val>::empty(), s, m2, nl));
                        assert(exit_done(m, m2, code as nat));
                        let vals = Seq::<lir::Val>::empty();
                        assert(ops_in_frame(
                            m2.mem,
                            ctx_of(m),
                            nl,
                            (base + Seq::<lir::Val>::empty()).len() + s.stack.len(),
                            vals,
                        ));
                        assert(exit_rel(lay, base, s, m2, nl, ctx_of(m), vals));
                    }
                },
                _ => {},
            }
        }
    }
}

} // verus!
