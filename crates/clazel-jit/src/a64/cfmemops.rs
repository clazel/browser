//! **The memory instructions refine LIR** (A64): `bounds_check`, `load` and
//! `store`. Each template ([`mem_code`]) is the operands into registers, the
//! validator's own bounds-check sequence ([`crate::a64::cfchk`]), the access,
//! a `b` over the stub, and the stub (an exit sequence) both of the check's
//! exits go to. The A64 counterpart of [`crate::cfmemops`].

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfalg::*;
#[cfg(verus_only)]
use super::cfchk::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cfexit::*;
#[cfg(verus_only)]
use super::cfleaf::*;
#[cfg(verus_only)]
use super::cfmemrel::*;
#[cfg(verus_only)]
use super::cfmemsteps::*;
#[cfg(verus_only)]
use super::cfop::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::templates::*;
#[cfg(verus_only)]
use crate::cfmemacc::{load_result, lemma_access_in_regions, store_result};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Indexing a five-part concatenation.
pub proof fn lemma_cat5_idx(
    pre: Seq<isa::Instr>,
    chk: Seq<isa::Instr>,
    tail: Seq<isa::Instr>,
    bb: isa::Instr,
    stub: Seq<isa::Instr>,
)
    ensures
        ({
            let w = pre + chk + tail + seq![bb] + stub;
            &&& w.len() == pre.len() + chk.len() + tail.len() + 1 + stub.len()
            &&& forall|i: int| 0 <= i < pre.len() ==> #[trigger] w[i] == pre[i]
            &&& forall|j: int| 0 <= j < chk.len() ==> #[trigger] w[pre.len() + j] == chk[j]
            &&& forall|i: int|
                0 <= i < tail.len() ==> #[trigger] w[pre.len() + chk.len() + i] == tail[i]
            &&& w[(pre.len() + chk.len() + tail.len()) as int] == bb
            &&& forall|i: int|
                0 <= i < stub.len() ==> #[trigger] w[pre.len() + chk.len() + tail.len() + 1 + i]
                    == stub[i]
        }),
{
    let w = pre + chk + tail + seq![bb] + stub;
    assert(w.len() == pre.len() + chk.len() + tail.len() + 1 + stub.len());
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] w[i] == pre[i] by {}
    assert forall|j: int| 0 <= j < chk.len() implies #[trigger] w[pre.len() + j] == chk[j] by {}
    assert forall|i: int| 0 <= i < tail.len() implies #[trigger] w[pre.len() + chk.len() + i]
        == tail[i] by {}
    assert forall|i: int| 0 <= i < stub.len() implies #[trigger] w[pre.len() + chk.len()
        + tail.len() + 1 + i] == stub[i] by {}
}

/// The start of the check in a memory instruction's code.
pub open spec fn mem_st(m: MemOp, nl: nat, h: nat) -> int {
    mem_pre(m, nl, h).len() as int
}

/// The word of the stub (and the target of both exits of the check).
pub open spec fn mem_sx(m: MemOp, nl: nat, h: nat) -> int {
    mem_st(m, nl, h) + 7 + mem_tail(m, nl, h).len() + 1
}

/// **The shape of a memory instruction's code**: where the pieces are.
pub proof fn lemma_mem_shape(m: MemOp, nl: nat, h: nat)
    ensures
        ({
            let code = mem_code(m, nl, h);
            let st = mem_st(m, nl, h);
            let sx = mem_sx(m, nl, h);
            let tl = mem_tail(m, nl, h).len() as int;
            &&& code.len() == sx + 3
            &&& forall|j: int|
                0 <= j < 7 ==> #[trigger] chk_at(code, st, sx, mem_region(m), mem_n(m), j)
            &&& forall|i: int| 0 <= i < st ==> #[trigger] code[i] == mem_pre(m, nl, h)[i]
            &&& forall|i: int| 0 <= i < tl ==> #[trigger] code[st + 7 + i] == mem_tail(m, nl, h)[i]
            &&& code[sx - 1] == b_i(16)
            &&& forall|i: int|
                0 <= i < 3 ==> #[trigger] code[sx + i] == exit_seq(mem_exit_code(m))[i]
        }),
{
    let pre = mem_pre(m, nl, h);
    let chk = mem_check(m, nl, h);
    let tail = mem_tail(m, nl, h);
    let stub = exit_seq(mem_exit_code(m));
    let bb = b_i(code_len(stub) as int + 4);
    assert(chk.len() == 7);
    assert(stub.len() == 3);
    assert(code_len(stub) == 12);
    lemma_cat5_idx(pre, chk, tail, bb, stub);
    let code = mem_code(m, nl, h);
    assert(code == pre + chk + tail + seq![bb] + stub);
    let st = mem_st(m, nl, h);
    let sx = mem_sx(m, nl, h);
    assert forall|j: int| 0 <= j < 7 implies #[trigger] chk_at(
        code,
        st,
        sx,
        mem_region(m),
        mem_n(m),
        j,
    ) by {
        assert(code[st + j] == chk[j]);
        assert(sx - (st + 2) == mem_r1(m, nl, h));
        assert(sx - (st + 4) == mem_r2(m, nl, h));
        assert(chk[j] == clazel_codecheck::a64::spec::check_instr(
            j,
            mem_chk(mem_region(m), mem_n(m), mem_r1(m, nl, h), mem_r2(m, nl, h)),
        ));
    }
}

/// The relation survives a run that changes registers other than `x28`, `x30`
/// and `SP`, and keeps the memory: it, the region table and `preserved_r` all
/// carry over.
pub open spec fn fr5(s: isa::State, s2: isa::State) -> bool {
    s2.r.len() == 31 && s.r.len() == 31 && s2.vreg == s.vreg && s2.mem == s.mem && s2.sp == s.sp
        && forall|k: int| 5 <= k < 31 ==> #[trigger] s2.r[k] == s.r[k]
}

/// [`chk_frame`] is [`fr5`].
pub proof fn lemma_chk_fr5(s: isa::State, s2: isa::State)
    requires
        chk_frame(s, s2),
    ensures
        fr5(s, s2),
{
}

/// [`fr5`] is transitive.
pub proof fn lemma_fr5_trans(s: isa::State, s1: isa::State, s2: isa::State)
    requires
        fr5(s, s1),
        fr5(s1, s2),
    ensures
        fr5(s, s2),
{
}

/// A [`fr5`] step keeps the relation, the region table and [`preserved_r`].
pub proof fn lemma_fr5_keep(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m2: isa::State,
    nl: nat,
)
    requires
        rel_base(lay, base, a, m, nl),
        fr5(m, m2),
    ensures
        rel_base(lay, base, a, m2, nl),
        preserved_r(lay, m, m2),
{
    super::steps::lemma_abi_consts();
    lemma_rel_base_unfold(lay, base, a, m, nl);
    assert(m2.vreg.len() == 32);
    lemma_rel_base_same(lay, base, a, m, m2, nl);
    lemma_preserved_same(lay, m, m2);
}

/// Words 0 to 8 of a bounds check are the slot load, the check, and the `b`;
/// the stub is the exit sequence.
#[verifier::rlimit(1000)]
pub proof fn lemma_bc_cf(region: usize, size: usize, code: u32, nl: nat, h: nat, offs: Seq<int>)
    requires
        nl + h <= max_slots(),
        1 <= h,
        region < 16,
        1 <= size <= 8,
        code < 0x1_0000,
    ensures
        cf_refines(
            Node::Mem(MemOp::BoundsCheck { region, size, code })@,
            nl,
            h,
            offs,
            mem_code(MemOp::BoundsCheck { region, size, code }, nl, h),
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::BoundsCheck { region, size, code };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    let c16 = code as u16;
    assert(mem_st(mo, nl, h) == 1 && mem_sx(mo, nl, h) == 9);
    assert(cd.len() == 12);
    assert(mem_exit_code(mo) == c16);
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, cd, m, lir::eval(lay, Node::Mem(mo)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            cd,
        ) implies cf_post(
        lay,
        base,
        nl,
        offs,
        cd,
        m,
        lir::eval(lay, Node::Mem(mo)@, a, fuel),
    ) by {
        let n = a.stack.len();
        if fuel > 0 && n >= 1 && (region as nat) < lay.len() {
            match a.stack[(n - 1) as int] {
                lir::Val::I64(ix) => {
                    lemma_rel_base_unfold(lay, base, a, m, nl);
                    let ac = a.with_stack(base + a.stack);
                    let j = (nl + h - 1) as nat;
                    let b0 = m.pc as int;
                    assert(ac.stack[(h - 1) as int] == lir::Val::I64(ix));
                    assert(slot_val(ac, nl, j) == lir::Val::I64(ix));
                    assert(j < nl + ac.stack.len());
                    assert(b0 + 48 < 0x1_0000_0000_0000_0000);
                    // word 0: ldr x1, [slot]
                    super::rel::lemma_load_rel(lay, ac, m, 1, j, nl);
                    let m1 = isa::step(m, load_slot(1, j)).unwrap();
                    assert(cd[0] == load_slot(1, j));
                    lemma_reach_step(cd, b0, m, 0, m1);
                    assert(m1.r[1] as nat == ix as nat);
                    // the bound
                    let k = region as nat;
                    let bound = lay[k as int].bound;
                    assert(table_ok(lay, m));
                    assert(isa::mem_read(m.mem, ctx_of(m) + abi::bound_off(k as int), 8) == Some(
                        bound as int,
                    ));
                    lemma_read_mem_range(m.mem, ctx_of(m) + abi::bound_off(k as int), 8, bound as int);
                    assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000nat);
                    let bnd = bound as u64;
                    assert(ctx_of(m1) == ctx_of(m));
                    assert(m1.mem == m.mem);
                    lemma_check_run(cd, b0, 1, 9, k, size as nat, m1, ix, bnd);
                    if ix as int + size as int > bound as int {
                        let m3 = choose|m3: isa::State|
                            reaches(cd, b0, m1, m3) && m3.pc as int == b0 + 4 * 9 && chk_frame(
                                m1,
                                m3,
                            );
                        lemma_reaches_trans(cd, b0, m, m1, m3);
                        assert(m3.r.len() == 31 && m3.vreg == m1.vreg && m3.mem == m.mem);
                        assert(m3.r[28] == m.r[28] && m3.r[30] == m.r[30]);
                        super::rel::lemma_rel_regs(lay, ac, m1, m3, nl);
                        let s = a.with_stack(lir::below(a.stack, 1));
                        assert((base + a.stack).take((base + s.stack).len() as int) =~= base
                            + s.stack);
                        lemma_rel_prefix(lay, a, base + a.stack, base + s.stack, m3, nl);
                        assert(s.with_stack(base + s.stack) == a.with_stack(base + s.stack));
                        let acs = a.with_stack(base + s.stack);
                        assert(m3.pc as int + code_len(exit_seq(c16)) < isa::p2(64));
                        lemma_exit_reach(c16, nl, lay, acs, m3);
                        let m4 = choose|m4: isa::State|
                            reaches(exit_seq(c16), m3.pc as int, m3, m4) && exit_done(
                                m3,
                                m4,
                                c16 as nat,
                            ) && rel(lay, acs, m4, nl) && preserved(m3, m4);
                        let pre9 = cd.take(9);
                        assert(cd =~= pre9 + exit_seq(c16) + Seq::<isa::Instr>::empty()) by {
                            assert forall|i: int| 0 <= i < 3 implies cd[9 + i] == exit_seq(c16)[i]
                                by {}
                        }
                        assert(code_len(pre9) == 36);
                        lemma_reaches_embed(
                            pre9,
                            exit_seq(c16),
                            Seq::empty(),
                            m3.pc as int,
                            m3,
                            m4,
                        );
                        assert(m3.pc as int - 36 == b0);
                        lemma_reaches_trans(cd, b0, m, m3, m4);
                        // the outcome
                        assert(lir::eval(lay, Node::Mem(mo)@, a, fuel) == lir::Outcome::Exit(
                            code as nat,
                            seq![],
                            s,
                        ));
                        lemma_pr_trans_mem(lay, m, m3, m4);
                        assert(ctx_of(m3) == ctx_of(m));
                        assert(exit_done(m, m4, code as nat));
                        lemma_table_pres(lay, m3, m4);
                        reveal(rel_base);
                        assert(rel_base(lay, base + Seq::<lir::Val>::empty(), s, m4, nl)) by {
                            assert(base + Seq::<lir::Val>::empty() =~= base);
                        }
                        assert(ops_in_frame(m4.mem, ctx_of(m), nl, (base + Seq::<lir::Val>::empty()).len()
                            + s.stack.len(), seq![]));
                        assert(exit_rel(lay, base, s, m4, nl, ctx_of(m), seq![]));
                    } else {
                        let m3 = choose|m3: isa::State|
                            reaches(cd, b0, m1, m3) && m3.pc as int == b0 + 4 * 8 && chk_frame(m1, m3)
                                && m3.r[1] == ix;
                        lemma_reaches_trans(cd, b0, m, m1, m3);
                        assert(cd[8] == b_i(16));
                        lemma_step_b(m3, 16);
                        let m5 = isa::State { pc: (m3.pc as int + 16) as u64, ..m3 };
                        lemma_reach_step(cd, b0, m3, 8, m5);
                        lemma_reaches_trans(cd, b0, m, m3, m5);
                        assert(m5.pc as int == b0 + 48);
                        assert(m5.r[28] == m.r[28] && m5.r[30] == m.r[30] && m5.r.len() == 31);
                        assert(fr5(m, m5));
                        lemma_fr5_keep(lay, base, a, m, m5, nl);
                        assert(lir::eval(lay, Node::Mem(mo)@, a, fuel) == lir::Outcome::Normal(a));
                    }
                },
                _ => {},
            }
        }
    }
}

/// [`preserved`] twice in the weaker, memory form.
pub proof fn lemma_pr_trans_mem(lay: lir::Layout, m: isa::State, m3: isa::State, m4: isa::State)
    requires
        m.r.len() == 31,
        m3.r.len() == 31,
        m3.mem == m.mem,
        m3.r[28] == m.r[28],
        preserved(m3, m4),
    ensures
        preserved_mem_r(lay, m, m4),
{
    super::steps::lemma_abi_consts();
    assert(ctx_of(m3) == ctx_of(m));
}


/// **The region access facts**: with the index `ix` within the bound, every byte
/// the access touches is a region byte, mapped, and below `2^56`; the effective
/// address is `base + ix`.
pub proof fn lemma_acc_facts(
    lay: lir::Layout,
    lm: lir::Mem,
    ms: isa::State,
    k: nat,
    ix: u64,
    sz: nat,
)
    requires
        isa::wf(ms),
        lir::layout_wf(lay),
        mem_rel(lay, lm, ms.mem),
        k < lay.len(),
        1 <= sz,
        ix as nat + sz <= lay[k as int].bound,
    ensures
        lay[k as int].base + ix as nat + sz < 0x1_0000_0000_0000_0000,
        forall|i: nat| i < sz ==> in_regions(lay, #[trigger] (lay[k as int].base + ix as nat + i)),
        forall|i: int|
            0 <= i < sz ==> ms.mem.dom().contains(
                #[trigger] ((lay[k as int].base + ix as nat) as int + i),
            ),
{
    super::memlemmas::lemma_p2_consts();
    lemma_access_in_regions(lay, k, ix as nat, sz);
    let a_ = lay[k as int].base + ix as nat;
    assert forall|i: int| 0 <= i < sz implies ms.mem.dom().contains(#[trigger] (a_ as int + i)) by {
        assert(in_regions(lay, a_ + i as nat));
    }
    assert(ms.mem.dom().contains(a_ as int + (sz - 1) as int));
}

/// **The loads before a `load`'s check**: the index into `x1` and the region's
/// base into `x3`.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_load_prefix(
    lay: lir::Layout,
    ac: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    ty: MTy,
    region: usize,
    ix: u64,
)
    requires
        nl + h <= max_slots(),
        1 <= h,
        region < 16,
        (region as nat) < lay.len(),
        rel(lay, ac, m, nl),
        table_ok(lay, m),
        ac.stack.len() == h,
        ac.stack[(h - 1) as int] == lir::Val::I64(ix),
        m.pc as int + 60 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let cd = mem_code(MemOp::Load { region, ty }, nl, h);
            exists|m2: isa::State|
                #![trigger reaches(cd, m.pc as int, m, m2)]
                reaches(cd, m.pc as int, m, m2) && m2.pc as int == m.pc as int + 8 && fr5(m, m2)
                    && m2.r[1] == ix && m2.r[3] == lay[region as int].base as u64 && isa::wf(m2)
                    && ctx_ok(m2) && rel(lay, ac, m2, nl)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::Load { region, ty };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    assert(mem_st(mo, nl, h) == 2);
    let j = (nl + h - 1) as nat;
    let k = region as nat;
    let b0 = m.pc as int;
    let base_r = lay[k as int].base;
    assert(slot_val(ac, nl, j) == lir::Val::I64(ix));
    assert(j < nl + ac.stack.len());
    super::rel::lemma_load_rel(lay, ac, m, 1, j, nl);
    let m1 = isa::step(m, load_slot(1, j)).unwrap();
    assert(cd[0] == load_slot(1, j));
    lemma_reach_step(cd, b0, m, 0, m1);
    assert(ctx_of(m1) == ctx_of(m) && m1.mem == m.mem);
    assert(isa::mem_read(m.mem, ctx_of(m) + abi::base_off(k as int), 8) == Some(base_r as int));
    lemma_read_mem_range(m.mem, ctx_of(m) + abi::base_off(k as int), 8, base_r as int);
    assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000nat);
    assert(cd[1] == base_ld(k));
    assert((abi::base_off(k as int) / 8) as u16 as int * 8 == abi::base_off(k as int));
    assert(isa::wf(m1) && ctx_ok(m1));
    lemma_step_ctx_ld(m1, 3, (abi::base_off(k as int) / 8) as u16, base_r);
    let m2 = isa::step(m1, base_ld(k)).unwrap();
    lemma_reach_step(cd, b0, m1, 1, m2);
    lemma_reaches_trans(cd, b0, m, m1, m2);
    assert(m2.r[1] == ix && m2.r[3] == base_r as u64 && m2.pc as int == b0 + 8);
    assert(isa::wf(m2) && ctx_ok(m2));
    assert(fr5(m, m2));
    super::rel::lemma_rel_regs(lay, ac, m, m2, nl);
}

/// **The access of a `load` and what follows**: from the state after the check
/// (at the `ldr x0, [x3, x1]`), the access, the store of the result to the slot,
/// and the `b` over the stub reach the end of the code, related to LIR's
/// result.
#[verifier::spinoff_prover]
#[verifier::rlimit(1500)]
pub proof fn lemma_load_finish(
    lay: lir::Layout,
    ac: lir::St,
    m: isa::State,
    m3: isa::State,
    nl: nat,
    h: nat,
    ty: MTy,
    region: usize,
    ix: u64,
)
    requires
        nl + h <= max_slots(),
        1 <= h,
        region < 16,
        (region as nat) < lay.len(),
        rel(lay, ac, m, nl),
        ac.stack.len() == h,
        ac.stack[(h - 1) as int] == lir::Val::I64(ix),
        ix as nat + ty.size() <= lay[region as int].bound,
        m.pc as int + 60 < 0x1_0000_0000_0000_0000,
        m3.pc as int == m.pc as int + 36,
        fr5(m, m3),
        m3.r[1] == ix,
        m3.r[3] == lay[region as int].base as u64,
        isa::wf(m3),
    ensures
        ({
            let cd = mem_code(MemOp::Load { region, ty }, nl, h);
            exists|m6: isa::State|
                #![trigger reaches(cd, m.pc as int, m3, m6)]
                reaches(cd, m.pc as int, m3, m6) && m6.pc as int == m.pc as int + 60 && rel(
                    lay,
                    load_result(lay, ac, region as nat, ty, ix),
                    m6,
                    nl,
                ) && preserved_r(lay, m, m6)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::Load { region, ty };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    let sf = mty_sf(ty);
    let sz = ty.size();
    let j = (nl + h - 1) as nat;
    let k = region as nat;
    let b0 = m.pc as int;
    let r = lay[k as int];
    let bound = r.bound;
    assert(mem_tail(mo, nl, h).len() == 2);
    assert(m3.mem == m.mem && m3.r.len() == 31);
    lemma_acc_facts(lay, ac.mem, m3, k, ix, sz);
    let a_ = r.base + ix as nat;
    assert(m3.r[3] as int + m3.r[1] as int == a_ as int);
    assert(mem_rel(lay, ac.mem, m3.mem));
    lemma_read_rel(lay, ac.mem, m3.mem, a_, sz);
    let vv = lir::read_le(ac.mem, a_, sz);
    crate::cfmemrel::lemma_read_le_range(ac.mem, a_, sz);
    assert(cd[9] == isa::Instr::LoadStoreReg { sf, load: true, t: 0, n: 3, m: 1, s: false });
    assert(sf_bytes(sf) == sz);
    lemma_step_ld_reg(m3, sf, 0, 3, 1, vv);
    let m4 = isa::step(m3, cd[9]).unwrap();
    lemma_reach_step(cd, b0, m3, 9, m4);
    let res = load_result(lay, ac, k, ty, ix);
    let val = lir::val_of_bits(ty.lir_ty(), vv);
    assert(lir::masked(bound, ix as nat) == ix as nat);
    assert(vv < vstd::arithmetic::power2::pow2(8 * sz));
    assert(lir::val_bits(val) == vv) by {
        match ty {
            MTy::I32 => {
                assert(vstd::arithmetic::power2::pow2(32) == 0x1_0000_0000nat);
                assert((vv as u32) as nat == vv);
            },
            MTy::I64 => {
                assert((vv as u64) as nat == vv);
            },
            MTy::F64 => {
                assert((vv as u64) as nat == vv);
            },
        }
    }
    assert(res.stack =~= lir::below(ac.stack, 1).push(val));
    assert(res.stack.len() == h);
    assert(slot_val(res, nl, j) == val);
    assert(crate::rel::slots_agree_except(ac, res, nl, j)) by {
        assert forall|jj: nat|
            #![trigger lir::val_bits(slot_val(res, nl, jj))]
            jj < nl + res.stack.len() && jj != j implies jj < nl + ac.stack.len()
            && lir::val_bits(slot_val(res, nl, jj)) == lir::val_bits(slot_val(ac, nl, jj)) by {
            if jj >= nl {
                assert(res.stack[(jj - nl) as int] == ac.stack[(jj - nl) as int]);
            }
        }
    }
    assert(m4.r.len() == 31 && m4.vreg == m3.vreg && m4.mem == m.mem);
    assert(m4.r[28] == m.r[28] && m4.r[30] == m.r[30] && m4.sp == m.sp);
    super::rel::lemma_rel_regs(lay, ac, m, m4, nl);
    assert(m4.r[0] as nat == lir::val_bits(slot_val(res, nl, j)));
    assert(cd[10] == store_slot(j, 0));
    assert(m4.pc as int == b0 + 40);
    super::rel::lemma_store_finish(lay, ac, res, m, m4, nl, j, 0, vv);
    let m5 = isa::step(m4, store_slot(j, 0)).unwrap();
    lemma_reach_step(cd, b0, m4, 10, m5);
    assert(cd[11] == b_i(16));
    lemma_step_b(m5, 16);
    let m6 = isa::State { pc: (m5.pc as int + 16) as u64, ..m5 };
    lemma_reach_step(cd, b0, m5, 11, m6);
    lemma_reaches_trans(cd, b0, m3, m4, m5);
    lemma_reaches_trans(cd, b0, m3, m5, m6);
    assert(m6.pc as int == b0 + 60);
    super::rel::lemma_rel_regs(lay, res, m5, m6, nl);
    lemma_preserved_to_r(lay, m, m5);
    lemma_preserved_same(lay, m5, m6);
    lemma_pr_trans(lay, m, m5, m6);
}

/// **`t.load k`**: the template refines it.
#[verifier::rlimit(1000)]
pub proof fn lemma_load_cf(region: usize, ty: MTy, nl: nat, h: nat, offs: Seq<int>)
    requires
        nl + h <= max_slots(),
        1 <= h,
        region < 16,
    ensures
        cf_refines(
            Node::Mem(MemOp::Load { region, ty })@,
            nl,
            h,
            offs,
            mem_code(MemOp::Load { region, ty }, nl, h),
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::Load { region, ty };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    assert(mem_st(mo, nl, h) == 2 && mem_sx(mo, nl, h) == 12);
    assert(cd.len() == 15);
    let sz = ty.size();
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, cd, m, lir::eval(lay, Node::Mem(mo)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            cd,
        ) implies cf_post(
        lay,
        base,
        nl,
        offs,
        cd,
        m,
        lir::eval(lay, Node::Mem(mo)@, a, fuel),
    ) by {
        let n = a.stack.len();
        if fuel > 0 && n >= 1 && (region as nat) < lay.len() {
            match a.stack[(n - 1) as int] {
                lir::Val::I64(ix) => {
                    lemma_rel_base_unfold(lay, base, a, m, nl);
                    let ac = a.with_stack(base + a.stack);
                    let k = region as nat;
                    let b0 = m.pc as int;
                    let r = lay[k as int];
                    let bound = r.bound;
                    assert(ac.stack[(h - 1) as int] == lir::Val::I64(ix));
                    assert(b0 + 60 < 0x1_0000_0000_0000_0000);
                    if ix as nat + sz <= bound {
                        lemma_load_prefix(lay, ac, m, nl, h, ty, region, ix);
                        let m2 = choose|m2: isa::State|
                            reaches(cd, b0, m, m2) && m2.pc as int == b0 + 8 && fr5(m, m2)
                                && m2.r[1] == ix && m2.r[3] == r.base as u64 && isa::wf(m2)
                                && ctx_ok(m2) && rel(lay, ac, m2, nl);
                        lemma_read_mem_range(
                            m.mem,
                            ctx_of(m) + abi::bound_off(k as int),
                            8,
                            bound as int,
                        );
                        assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000nat);
                        assert(ctx_of(m2) == ctx_of(m) && m2.mem == m.mem);
                        lemma_check_run(cd, b0, 2, 12, k, sz, m2, ix, bound as u64);
                        let m3 = choose|m3: isa::State|
                            reaches(cd, b0, m2, m3) && m3.pc as int == b0 + 4 * 9 && chk_frame(
                                m2,
                                m3,
                            ) && m3.r[1] == ix;
                        lemma_reaches_trans(cd, b0, m, m2, m3);
                        lemma_chk_fr5(m2, m3);
                        lemma_fr5_trans(m, m2, m3);
                        assert(m3.r[3] == m2.r[3]);
                        assert(isa::wf(m3));
                        lemma_load_finish(lay, ac, m, m3, nl, h, ty, region, ix);
                        let m6 = choose|m6: isa::State|
                            reaches(cd, b0, m3, m6) && m6.pc as int == b0 + 60 && rel(
                                lay,
                                load_result(lay, ac, k, ty, ix),
                                m6,
                                nl,
                            ) && preserved_r(lay, m, m6);
                        lemma_reaches_trans(cd, b0, m, m3, m6);
                        lemma_table_pres(lay, m, m6);
                        let val = lir::val_of_bits(
                            ty.lir_ty(),
                            lir::read_le(ac.mem, r.base + ix as nat, sz),
                        );
                        let a2 = a.with_stack(lir::below(a.stack, 1).push(val));
                        assert(lir::masked(bound, ix as nat) == ix as nat);
                        assert(lir::eval(lay, Node::Mem(mo)@, a, fuel) == lir::Outcome::Normal(a2));
                        assert((base + lir::below(a.stack, 1).push(val)) =~= lir::below(
                            base + a.stack,
                            1,
                        ).push(val));
                        assert(a2.with_stack(base + a2.stack) == load_result(lay, ac, k, ty, ix));
                        reveal(rel_base);
                        assert(rel_base(lay, base, a2, m6, nl));
                    }
                },
                _ => {},
            }
        }
    }
}

/// **The loads before a `store`'s check**: the value into `x4`, the index into
/// `x1`, the region's base into `x3`.
#[verifier::spinoff_prover]
#[verifier::rlimit(800)]
pub proof fn lemma_store_prefix(
    lay: lir::Layout,
    ac: lir::St,
    m: isa::State,
    nl: nat,
    h: nat,
    ty: MTy,
    region: usize,
    ix: u64,
    v: lir::Val,
)
    requires
        nl + h <= max_slots(),
        2 <= h,
        region < 16,
        (region as nat) < lay.len(),
        rel(lay, ac, m, nl),
        table_ok(lay, m),
        ac.stack.len() == h,
        ac.stack[(h - 1) as int] == v,
        ac.stack[(h - 2) as int] == lir::Val::I64(ix),
        m.pc as int + 60 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let cd = mem_code(MemOp::Store { region, ty }, nl, h);
            exists|m2: isa::State|
                #![trigger reaches(cd, m.pc as int, m, m2)]
                reaches(cd, m.pc as int, m, m2) && m2.pc as int == m.pc as int + 12 && fr5(m, m2)
                    && m2.r[1] == ix && m2.r[3] == lay[region as int].base as u64 && m2.r[4] as nat
                    == lir::val_bits(v) && isa::wf(m2) && ctx_ok(m2)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::Store { region, ty };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    assert(mem_st(mo, nl, h) == 3);
    let jv = (nl + h - 1) as nat;
    let ji = (nl + h - 2) as nat;
    let k = region as nat;
    let b0 = m.pc as int;
    let base_r = lay[k as int].base;
    assert(slot_val(ac, nl, jv) == v);
    assert(slot_val(ac, nl, ji) == lir::Val::I64(ix));
    super::rel::lemma_load_rel(lay, ac, m, 4, jv, nl);
    let m1 = isa::step(m, load_slot(4, jv)).unwrap();
    assert(cd[0] == load_slot(4, jv));
    lemma_reach_step(cd, b0, m, 0, m1);
    super::rel::lemma_load_rel(lay, ac, m1, 1, ji, nl);
    let m2 = isa::step(m1, load_slot(1, ji)).unwrap();
    assert(cd[1] == load_slot(1, ji));
    lemma_reach_step(cd, b0, m1, 1, m2);
    lemma_reaches_trans(cd, b0, m, m1, m2);
    assert(ctx_of(m2) == ctx_of(m) && m2.mem == m.mem);
    assert(isa::mem_read(m.mem, ctx_of(m) + abi::base_off(k as int), 8) == Some(base_r as int));
    lemma_read_mem_range(m.mem, ctx_of(m) + abi::base_off(k as int), 8, base_r as int);
    assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000nat);
    assert(cd[2] == base_ld(k));
    assert((abi::base_off(k as int) / 8) as u16 as int * 8 == abi::base_off(k as int));
    assert(isa::wf(m2) && ctx_ok(m2));
    lemma_step_ctx_ld(m2, 3, (abi::base_off(k as int) / 8) as u16, base_r);
    let m2b = isa::step(m2, base_ld(k)).unwrap();
    lemma_reach_step(cd, b0, m2, 2, m2b);
    lemma_reaches_trans(cd, b0, m, m2, m2b);
    assert(m2b.r[1] == ix && m2b.r[3] == base_r as u64 && m2b.pc as int == b0 + 12);
    assert(m2b.r[4] as nat == lir::val_bits(v));
    assert(isa::wf(m2b) && ctx_ok(m2b));
    assert(fr5(m, m2b));
}

/// **The access of a `store` and what follows**: the store through `[x3, x1]`
/// and the `b` over the stub reach the end of the code, related to LIR's
/// result; only region bytes changed.
#[verifier::spinoff_prover]
#[verifier::rlimit(2000)]
pub proof fn lemma_store_finish_ls(
    lay: lir::Layout,
    ac: lir::St,
    m: isa::State,
    m3: isa::State,
    nl: nat,
    h: nat,
    ty: MTy,
    region: usize,
    ix: u64,
    v: lir::Val,
)
    requires
        nl + h <= max_slots(),
        2 <= h,
        region < 16,
        (region as nat) < lay.len(),
        rel(lay, ac, m, nl),
        ac.stack.len() == h,
        ac.stack[(h - 1) as int] == v,
        ac.stack[(h - 2) as int] == lir::Val::I64(ix),
        lir::val_has_base_ty(v, ty.lir_ty()),
        ix as nat + ty.size() <= lay[region as int].bound,
        m.pc as int + 60 < 0x1_0000_0000_0000_0000,
        m3.pc as int == m.pc as int + 40,
        fr5(m, m3),
        m3.r[1] == ix,
        m3.r[3] == lay[region as int].base as u64,
        m3.r[4] as nat == lir::val_bits(v),
        isa::wf(m3),
    ensures
        ({
            let cd = mem_code(MemOp::Store { region, ty }, nl, h);
            exists|m5: isa::State|
                #![trigger reaches(cd, m.pc as int, m3, m5)]
                reaches(cd, m.pc as int, m3, m5) && m5.pc as int == m.pc as int + 60 && rel(
                    lay,
                    store_result(lay, ac, region as nat, ty, ix, v),
                    m5,
                    nl,
                ) && preserved_r(lay, m, m5)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::Store { region, ty };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    let sf = mty_sf(ty);
    let sz = ty.size();
    let k = region as nat;
    let b0 = m.pc as int;
    let r = lay[k as int];
    let bound = r.bound;
    assert(mem_tail(mo, nl, h).len() == 1);
    assert(m3.mem == m.mem && m3.r.len() == 31);
    lemma_acc_facts(lay, ac.mem, m3, k, ix, sz);
    let a_ = r.base + ix as nat;
    assert(m3.r[3] as int + m3.r[1] as int == a_ as int);
    assert(cd[10] == isa::Instr::LoadStoreReg { sf, load: false, t: 4, n: 3, m: 1, s: false });
    assert(sf_bytes(sf) == sz);
    lemma_step_st_reg(m3, sf, 4, 3, 1);
    let vb = lir::val_bits(v);
    let w = isa::trunc(isa::datasize(sf), m3.r[4] as int);
    assert(vb < vstd::arithmetic::power2::pow2(8 * sz)) by {
        match v {
            lir::Val::I32(x) => {
                assert(ty is I32);
                assert(vstd::arithmetic::power2::pow2(32) == 0x1_0000_0000nat);
            },
            lir::Val::I64(x) => {
                assert(!(ty is I32));
            },
            lir::Val::F64(x) => {
                assert(!(ty is I32));
            },
        }
    }
    assert(w == vb as int) by {
        assert(isa::p2(isa::datasize(sf)) == vstd::arithmetic::power2::pow2(8 * sz) as int);
        vstd::arithmetic::div_mod::lemma_small_mod(vb, isa::p2(isa::datasize(sf)) as nat);
    }
    let mem2 = isa::mem_set(m3.mem, a_ as int, sz, w).unwrap();
    let m4 = isa::step(m3, cd[10]).unwrap();
    assert(m4 == isa::State { mem: mem2, pc: (m3.pc + 4) as u64, ..m3 });
    lemma_reach_step(cd, b0, m3, 10, m4);
    super::memlemmas::lemma_mem_set_frame(m3.mem, a_ as int, sz, w, mem2);
    lemma_write_rel(lay, ac.mem, m3.mem, mem2, a_, sz, vb);
    let res = store_result(lay, ac, k, ty, ix, v);
    assert(lir::masked(bound, ix as nat) == ix as nat);
    let ctxb = ctx_of(m);
    assert(ctx_of(m4) == ctxb);
    assert forall|b: int| a_ as int <= b < a_ as int + sz implies !in_exit_area(ctxb, b)
        && in_regions_i(lay, b) by {
        assert(in_regions(lay, a_ + (b - a_ as int) as nat));
    }
    assert(preserved_mem_r(lay, m, m4)) by {
        assert(m4.r.len() == 31 && m4.r[28] == m.r[28]);
        assert forall|b: int|
            #[trigger] m.mem.dom().contains(b) && !in_exit_area(ctxb, b) && !in_regions_i(
                lay,
                b,
            ) implies m4.mem[b] == m.mem[b] by {
            assert(!(a_ as int <= b && b < a_ as int + sz));
        }
    }
    assert(rel(lay, res, m4, nl)) by {
        assert(isa::wf(m4)) by {
            assert(m4.mem.dom() =~= m3.mem.dom());
        }
        assert(ctx_ok(m4));
        assert(exit_area_mapped(m4.mem, ctxb));
        assert(res.locals.len() == nl);
        assert(res.stack.len() == h - 2);
        assert(res.mem == lir::write_le(ac.mem, a_, vb, sz));
        assert forall|jj: nat| jj < nl + res.stack.len() implies #[trigger] slot_holds(
            m4.mem,
            ctxb,
            jj,
            lir::val_bits(slot_val(res, nl, jj)),
        ) by {
            assert(slot_val(res, nl, jj) == slot_val(ac, nl, jj)) by {
                if jj >= nl {
                    assert(res.stack[(jj - nl) as int] == ac.stack[(jj - nl) as int]);
                }
            }
            assert(slot_holds(m.mem, ctxb, jj, lir::val_bits(slot_val(ac, nl, jj))));
            let sa = ctxb + slot_disp(jj);
            assert(jj < max_slots());
            super::steps::lemma_slot_addr(m, jj);
            assert forall|i: int| 0 <= i < 8 implies (m3.mem.dom().contains(#[trigger] (sa + i))
                == m4.mem.dom().contains(sa + i)) && (m3.mem.dom().contains(sa + i)
                ==> m3.mem[sa + i] == m4.mem[sa + i]) by {
                super::rel::lemma_slot_in_exit_area(ctxb, jj, sa + i);
                assert(!(a_ as int <= sa + i && sa + i < a_ as int + sz));
            }
            super::memlemmas::lemma_mem_read_congr(m3.mem, m4.mem, sa, 8);
        }
    }
    assert(m4.pc as int == b0 + 44);
    assert(cd[11] == b_i(16));
    lemma_step_b(m4, 16);
    let m5 = isa::State { pc: (m4.pc as int + 16) as u64, ..m4 };
    lemma_reach_step(cd, b0, m4, 11, m5);
    lemma_reaches_trans(cd, b0, m3, m4, m5);
    assert(m5.pc as int == b0 + 60);
    assert(m5.r == m4.r && m5.mem == m4.mem && m5.vreg == m4.vreg);
    super::rel::lemma_rel_regs(lay, res, m4, m5, nl);
    assert(preserved_mem_r(lay, m, m5));
    assert(m5.r[30] == m.r[30] && m5.sp == m.sp);
}

/// **`t.store k`**: the template refines it.
#[verifier::rlimit(1000)]
pub proof fn lemma_store_cf(region: usize, ty: MTy, nl: nat, h: nat, offs: Seq<int>)
    requires
        nl + h <= max_slots(),
        2 <= h,
        region < 16,
    ensures
        cf_refines(
            Node::Mem(MemOp::Store { region, ty })@,
            nl,
            h,
            offs,
            mem_code(MemOp::Store { region, ty }, nl, h),
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let mo = MemOp::Store { region, ty };
    let cd = mem_code(mo, nl, h);
    lemma_mem_shape(mo, nl, h);
    assert(mem_st(mo, nl, h) == 3 && mem_sx(mo, nl, h) == 12);
    assert(cd.len() == 15);
    let sz = ty.size();
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, cd, m, lir::eval(lay, Node::Mem(mo)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            cd,
        ) implies cf_post(
        lay,
        base,
        nl,
        offs,
        cd,
        m,
        lir::eval(lay, Node::Mem(mo)@, a, fuel),
    ) by {
        let n = a.stack.len();
        if fuel > 0 && n >= 2 && (region as nat) < lay.len() && lir::val_has_base_ty(
            a.stack[(n - 1) as int],
            ty.lir_ty(),
        ) {
            match a.stack[(n - 2) as int] {
                lir::Val::I64(ix) => {
                    lemma_rel_base_unfold(lay, base, a, m, nl);
                    let ac = a.with_stack(base + a.stack);
                    let k = region as nat;
                    let b0 = m.pc as int;
                    let r = lay[k as int];
                    let bound = r.bound;
                    let v = a.stack[(n - 1) as int];
                    assert(ac.stack[(h - 1) as int] == v);
                    assert(ac.stack[(h - 2) as int] == lir::Val::I64(ix));
                    assert(b0 + 60 < 0x1_0000_0000_0000_0000);
                    if ix as nat + sz <= bound {
                        lemma_store_prefix(lay, ac, m, nl, h, ty, region, ix, v);
                        let m2 = choose|m2: isa::State|
                            reaches(cd, b0, m, m2) && m2.pc as int == b0 + 12 && fr5(m, m2)
                                && m2.r[1] == ix && m2.r[3] == r.base as u64 && m2.r[4] as nat
                                == lir::val_bits(v) && isa::wf(m2) && ctx_ok(m2);
                        lemma_read_mem_range(
                            m.mem,
                            ctx_of(m) + abi::bound_off(k as int),
                            8,
                            bound as int,
                        );
                        assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000nat);
                        assert(ctx_of(m2) == ctx_of(m) && m2.mem == m.mem);
                        lemma_check_run(cd, b0, 3, 12, k, sz, m2, ix, bound as u64);
                        let m3 = choose|m3: isa::State|
                            reaches(cd, b0, m2, m3) && m3.pc as int == b0 + 4 * 10 && chk_frame(
                                m2,
                                m3,
                            ) && m3.r[1] == ix;
                        lemma_reaches_trans(cd, b0, m, m2, m3);
                        lemma_chk_fr5(m2, m3);
                        lemma_fr5_trans(m, m2, m3);
                        assert(m3.r[3] == m2.r[3] && m3.r[4] == m2.r[4]);
                        assert(isa::wf(m3));
                        lemma_store_finish_ls(lay, ac, m, m3, nl, h, ty, region, ix, v);
                        let m5 = choose|m5: isa::State|
                            reaches(cd, b0, m3, m5) && m5.pc as int == b0 + 60 && rel(
                                lay,
                                store_result(lay, ac, k, ty, ix, v),
                                m5,
                                nl,
                            ) && preserved_r(lay, m, m5);
                        lemma_reaches_trans(cd, b0, m, m3, m5);
                        lemma_table_pres(lay, m, m5);
                        let a_ = r.base + ix as nat;
                        let a2 = a.with_stack(lir::below(a.stack, 2));
                        let a2m = a2.with_mem(lir::write_le(a.mem, a_, lir::val_bits(v), sz));
                        assert(lir::masked(bound, ix as nat) == ix as nat);
                        assert(lir::eval(lay, Node::Mem(mo)@, a, fuel) == lir::Outcome::Normal(a2m));
                        assert((base + lir::below(a.stack, 2)) =~= lir::below(base + a.stack, 2));
                        assert(a2m.with_stack(base + a2m.stack) == store_result(
                            lay,
                            ac,
                            k,
                            ty,
                            ix,
                            v,
                        ));
                        reveal(rel_base);
                        assert(rel_base(lay, base, a2m, m5, nl));
                    }
                },
                _ => {},
            }
        }
    }
}

} // verus!
