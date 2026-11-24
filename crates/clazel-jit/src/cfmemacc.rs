//! The access of a `load` and of a `store`, after the check passed: the
//! machine state with `rsi` the region's base and `rcx` the index runs the
//! access (and a load's store to the slot) to a state related to LIR's result,
//! using `mem_rel` ([`crate::cfmemrel`]).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfmemrel::*;
#[cfg(verus_only)]
use crate::cfmemsteps::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// LIR's state after `t.load k` from the state `ac` whose top is the index
/// `ix`.
pub open spec fn load_result(lay: lir::Layout, ac: lir::St, k: nat, ty: MTy, ix: u64) -> lir::St {
    let r = lay[k as int];
    let a_ = r.base + lir::masked(r.bound, ix as nat);
    ac.with_stack(
        lir::below(ac.stack, 1).push(
            lir::val_of_bits(ty.lir_ty(), lir::read_le(ac.mem, a_, ty.size())),
        ),
    )
}

/// LIR's state after `t.store k` from the state `ac` whose top is the value
/// `v` and next the index `ix`.
pub open spec fn store_result(
    lay: lir::Layout,
    ac: lir::St,
    k: nat,
    ty: MTy,
    ix: u64,
    v: lir::Val,
) -> lir::St {
    let r = lay[k as int];
    let a_ = r.base + lir::masked(r.bound, ix as nat);
    ac.with_stack(lir::below(ac.stack, 2)).with_mem(
        lir::write_le(ac.mem, a_, lir::val_bits(v), ty.size()),
    )
}

/// Region bytes the access touches are in the region: `base + ix + i` for
/// `i < sz` when `ix + sz <= bound`.
pub proof fn lemma_access_in_regions(lay: lir::Layout, k: nat, ix: nat, sz: nat)
    requires
        k < lay.len(),
        ix + sz <= lay[k as int].bound,
    ensures
        forall|i: nat| i < sz ==> in_regions(lay, #[trigger] (lay[k as int].base + ix + i)),
{
    assert forall|i: nat| i < sz implies in_regions(lay, #[trigger] (lay[k as int].base + ix + i)) by {
        let r = k as int;
        assert(0 <= r < lay.len() && lay[r].base <= lay[r].base + ix + i && lay[r].base + ix + i
            < lay[r].base + lay[r].bound);
    }
}

/// **The access address is a machine address**: with the region byte mapped
/// (`mem_rel`) and the state well formed, `base + ix` is below `2^47`, and the
/// effective address `[rsi + rcx]` is it.
pub proof fn lemma_access_ea(
    lay: lir::Layout,
    lm: lir::Mem,
    m: x64::State,
    k: nat,
    ix: nat,
    sz: nat,
)
    requires
        x64::wf(m),
        mem_rel(lay, lm, m.mem),
        k < lay.len(),
        1 <= sz,
        ix + sz <= lay[k as int].bound,
        m.rgf.len() == 16,
        m.rgf[6] as int == lay[k as int].base as int,
        m.rgf[1] as int == ix as int,
    ensures
        x64::eff_addr(m, ix_mem()) == (lay[k as int].base + ix) as int,
        0 <= (lay[k as int].base + ix) as int,
        lay[k as int].base < 0x1_0000_0000_0000_0000,
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let r = k as int;
    let b = lay[r].base;
    assert(in_regions(lay, b + ix)) by {
        assert(0 <= r < lay.len() && lay[r].base <= b + ix && b + ix < lay[r].base + lay[r].bound);
    }
    assert(m.mem.dom().contains((b + ix) as int));
    assert(x64::canonical((b + ix) as int));
    assert(b + ix < 0x8000_0000_0000);
    let x = (b + ix) as int;
    assert(x64::p2(0) == 1);
    assert(x64::eff_addr(m, ix_mem()) == x64::logext(64, m.rgf[6] as int + m.rgf[1] as int * x64::p2(
        0,
    ) + 0));
    assert(x64::loghead(64, x) == x);
    assert(x64::logext(64, x) == x);
    assert(b < 0x1_0000_0000_0000_0000);
}

/// **A load's access and its store to the slot.** From a state `mb` with `rsi`
/// the region's base and `rcx` the index, related to `ac`, whose top is the
/// index and within the bound, the two instructions of [`mem_tail`] run to a
/// state related to [`load_result`], with only the exit area changed.
pub proof fn lemma_load_access(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    ac: lir::St,
    m: x64::State,
    mb: x64::State,
    nl: nat,
    h: nat,
    k: nat,
    ty: MTy,
    ix: u64,
)
    requires
        rel(lay, ac, m, nl),
        rel(lay, ac, mb, nl),
        mb.mem == m.mem,
        mb.rgf.len() == 16,
        m.rgf.len() == 16,
        mb.rgf[4] == m.rgf[4],
        mb.rgf[15] == m.rgf[15],
        mb.rgf[6] as int == lay[k as int].base as int,
        mb.rgf[1] as int == ix as int,
        k < lay.len(),
        ac.stack.len() == h,
        1 <= h,
        nl + h <= max_slots(),
        ix as nat + ty.size() <= lay[k as int].bound,
        x64::canonical(mb.rip + 16),
    ensures
        run_seq(cu, mb, mem_tail(MemOp::Load { region: k as usize, ty }, nl, h)) is Some,
        ({
            let m4 = run_seq(cu, mb, mem_tail(MemOp::Load { region: k as usize, ty }, nl, h)).unwrap();
            &&& rel(lay, load_result(lay, ac, k, ty, ix), m4, nl)
            &&& preserved(m, m4)
            &&& m4.rip == mb.rip + 15 + (if ty is I32 {
                0nat
            } else {
                1nat
            })
        }),
{
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let sz = ty.size();
    let mo = MemOp::Load { region: k as usize, ty };
    let j = (nl + h - 1) as nat;
    let r = lay[k as int];
    let szz = mty_sz(ty);
    lemma_mem_instr_lens(j, k);
    let t1 = x64::Instr::MovLoad { sz: szz, dst: rax(), mem: ix_mem() };
    let t2 = store_slot(j, rax());
    assert(mem_tail(mo, nl, h) =~= seq![t1, t2]);
    super::runseq::lemma_len2(t1, t2);
    assert(x64::nbytes(szz) == sz);
    lemma_access_ea(lay, ac.mem, mb, k, ix as nat, sz);
    lemma_access_in_regions(lay, k, ix as nat, sz);
    assert(mem_rel(lay, ac.mem, mb.mem));
    lemma_read_rel(lay, ac.mem, mb.mem, r.base + ix as nat, sz);
    let v = lir::read_le(ac.mem, r.base + ix as nat, sz);
    lemma_read_le_range(ac.mem, r.base + ix as nat, sz);
    assert(vstd::arithmetic::power2::pow2(8 * sz) == if ty is I32 {
        0x1_0000_0000nat
    } else {
        0x1_0000_0000_0000_0000nat
    });
    // the access
    assert(x64::canonical(mb.rip + x64::instr_len(t1))) by {
        assert(x64::canonical(mb.rip));
        super::runseq::lemma_canonical_between(mb.rip, mb.rip + x64::instr_len(t1), mb.rip + 16);
    }
    assert(x64::wf(mb));
    lemma_step_movload(cu, mb, szz, rax(), ix_mem(), v as int);
    let m3 = x64::step(cu, mb, t1).unwrap();
    assert(m3.rgf == mb.rgf.update(0, v as u64)) by {
        vstd::arithmetic::div_mod::lemma_small_mod(v, 0x1_0000_0000_0000_0000nat);
        if ty is I32 {
            vstd::arithmetic::div_mod::lemma_small_mod(v, 0x1_0000_0000nat);
        }
    }
    assert(m3.mem == mb.mem && m3.xmm == mb.xmm);
    assert(m3.rip == mb.rip + x64::instr_len(t1));
    super::rel::lemma_rel_regs(lay, ac, mb, m3, nl);
    // the new LIR state
    let res = load_result(lay, ac, k, ty, ix);
    let val = lir::val_of_bits(ty.lir_ty(), v);
    assert(lir::masked(r.bound, ix as nat) == ix as nat);
    assert(lir::val_bits(val) == v) by {
        match ty {
            MTy::I32 => {
                assert((v as u32) as nat == v);
            },
            MTy::I64 => {
                assert((v as u64) as nat == v);
            },
            MTy::F64 => {
                assert((v as u64) as nat == v);
            },
        }
    }
    assert(res.stack =~= lir::below(ac.stack, 1).push(val));
    assert(res.stack.len() == h);
    assert(res.stack[(h - 1) as int] == val);
    assert(slot_val(res, nl, j) == val);
    assert(super::rel::slots_agree_except(ac, res, nl, j)) by {
        assert forall|jj: nat|
            #![trigger lir::val_bits(slot_val(res, nl, jj))]
            jj < nl + res.stack.len() && jj != j implies jj < nl + ac.stack.len() && lir::val_bits(
            slot_val(res, nl, jj),
        ) == lir::val_bits(slot_val(ac, nl, jj)) by {
            if jj >= nl {
                assert(res.stack[(jj - nl) as int] == ac.stack[(jj - nl) as int]);
            }
        }
    }
    assert(m3.rgf[0] as nat == lir::val_bits(slot_val(res, nl, j)));
    assert(x64::canonical(m3.rip + x64::instr_len(t2))) by {
        super::runseq::lemma_canonical_between(mb.rip, m3.rip + x64::instr_len(t2), mb.rip + 16);
    }
    super::rel::lemma_store_finish(cu, lay, ac, res, m, m3, nl, j, rax(), v);
    let m4 = x64::step(cu, m3, t2).unwrap();
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen2(f, mb, t1, t2, m3, m4);
    super::runseq::lemma_run_seq_is_gen(cu, mb, seq![t1, t2]);
}

/// **A store's access.** From a state `mb` with `rsi` the region's base, `rcx`
/// the index and `rdi` the value's bits, related to `ac` (value on top, index
/// below), the access runs to a state related to [`store_result`]; only
/// region bytes changed.
pub proof fn lemma_store_access(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    ac: lir::St,
    m: x64::State,
    mb: x64::State,
    nl: nat,
    h: nat,
    k: nat,
    ty: MTy,
    ix: u64,
    v: lir::Val,
)
    requires
        rel(lay, ac, m, nl),
        rel(lay, ac, mb, nl),
        mb.mem == m.mem,
        mb.rgf.len() == 16,
        m.rgf.len() == 16,
        mb.rgf[4] == m.rgf[4],
        mb.rgf[15] == m.rgf[15],
        mb.rgf[6] as int == lay[k as int].base as int,
        mb.rgf[1] as int == ix as int,
        mb.rgf[7] as nat == lir::val_bits(v),
        lir::val_has_base_ty(v, ty.lir_ty()),
        k < lay.len(),
        ac.stack.len() == h,
        2 <= h,
        nl + h <= max_slots(),
        ix as nat + ty.size() <= lay[k as int].bound,
        x64::canonical(mb.rip + 8),
    ensures
        run_seq(cu, mb, mem_tail(MemOp::Store { region: k as usize, ty }, nl, h)) is Some,
        ({
            let m4 = run_seq(cu, mb, mem_tail(MemOp::Store { region: k as usize, ty }, nl, h)).unwrap();
            &&& rel(lay, store_result(lay, ac, k, ty, ix, v), m4, nl)
            &&& preserved_mem_r(lay, m, m4)
            &&& m4.rgf[4] == m.rgf[4]
            &&& m4.rip == mb.rip + 7 + (if ty is I32 {
                0nat
            } else {
                1nat
            })
        }),
{
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let sz = ty.size();
    let mo = MemOp::Store { region: k as usize, ty };
    let r = lay[k as int];
    let szz = mty_sz(ty);
    lemma_mem_instr_lens(0, k);
    let t1 = x64::Instr::MovStore { sz: szz, mem: ix_mem(), src: rdi() };
    assert(mem_tail(mo, nl, h) =~= seq![t1]);
    super::runseq::lemma_len1(t1);
    assert(x64::nbytes(szz) == sz);
    assert(x64::wf(mb));
    lemma_access_ea(lay, ac.mem, mb, k, ix as nat, sz);
    lemma_access_in_regions(lay, k, ix as nat, sz);
    let a_ = r.base + ix as nat;
    let vb = lir::val_bits(v);
    assert(vb < vstd::arithmetic::power2::pow2(8 * sz)) by {
        match v {
            lir::Val::I32(x) => {
                assert(ty is I32);
            },
            lir::Val::I64(x) => {
                assert(!(ty is I32));
            },
            lir::Val::F64(x) => {
                assert(!(ty is I32));
            },
        }
        assert(vstd::arithmetic::power2::pow2(32) == 0x1_0000_0000nat);
    }
    assert(x64::rgfi_size(mb, szz, rdi()) == vb as int) by {
        assert(vb < 0x1_0000_0000_0000_0000);
        vstd::arithmetic::div_mod::lemma_small_mod(vb, 0x1_0000_0000_0000_0000nat);
        if ty is I32 {
            vstd::arithmetic::div_mod::lemma_small_mod(vb, 0x1_0000_0000nat);
        }
    }
    // the bytes are mapped
    assert forall|i: int| 0 <= i < sz implies mb.mem.dom().contains(#[trigger] (a_ as int + i)) by {
        assert(in_regions(lay, a_ + i as nat));
    }
    super::memlemmas::lemma_write_mem_some(mb.mem, a_ as int, sz, vb as int);
    let mem2 = x64::write_mem(mb.mem, a_ as int, sz, vb as int).unwrap();
    assert(x64::canonical(mb.rip + x64::instr_len(t1)));
    lemma_step_movstore(cu, mb, szz, ix_mem(), rdi(), mem2);
    let m4 = x64::step(cu, mb, t1).unwrap();
    assert(m4 == x64::State { mem: mem2, rip: mb.rip + x64::instr_len(t1), ..mb });
    super::memlemmas::lemma_write_mem_frame(mb.mem, a_ as int, sz, vb as int, mem2);
    lemma_write_rel(lay, ac.mem, mb.mem, mem2, a_, sz, vb);
    let res = store_result(lay, ac, k, ty, ix, v);
    assert(lir::masked(r.bound, ix as nat) == ix as nat);
    let ctxb = ctx_of(m);
    assert(ctx_of(m4) == ctxb);
    // written bytes are region bytes, so outside the exit area
    assert forall|b: int| a_ as int <= b < a_ as int + sz implies !in_exit_area(
        ctxb,
        b,
    ) && in_regions_i(lay, b) by {
        assert(in_regions(lay, (b as nat)));
        assert(in_regions(lay, a_ + (b - a_ as int) as nat));
    }
    // preserved
    assert(preserved_mem_r(lay, m, m4)) by {
        assert forall|b: int|
            #[trigger] m.mem.dom().contains(b) && !in_exit_area(ctxb, b) && !in_regions_i(
                lay,
                b,
            ) implies m4.mem[b] == m.mem[b] by {
            assert(!(a_ as int <= b && b < a_ as int + sz));
        }
    }
    // the relation
    assert(rel(lay, res, m4, nl)) by {
        assert(x64::wf(m4)) by {
            assert(m4.mem.dom() =~= mb.mem.dom());
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
            assert forall|i: int| 0 <= i < 8 implies (m.mem.dom().contains(#[trigger] (sa + i))
                == m4.mem.dom().contains(sa + i)) && (m.mem.dom().contains(sa + i) ==> m.mem[sa + i]
                == m4.mem[sa + i]) by {
                assert(in_exit_area(ctxb, sa + i)) by {
                    super::rel::lemma_slot_in_exit_area(ctxb, jj, sa + i);
                }
                assert(!(a_ as int <= sa + i && sa + i < a_ as int + sz));
            }
            super::memlemmas::lemma_read_mem_congr(m.mem, m4.mem, sa, 8);
        }
    }
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen1(f, mb, t1, m4);
    super::runseq::lemma_run_seq_is_gen(cu, mb, seq![t1]);
}

} // verus!
