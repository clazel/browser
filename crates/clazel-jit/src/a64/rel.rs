//! Facts about the state relation [`rel`]: it survives a change of scratch
//! registers, flags and `pc`; a load from a slot leaves it intact and puts the
//! slot's word in a register; and a store of the result word to slot `ts`
//! takes the relation to the next LIR state. The A64 counterpart of
//! [`crate::rel`]. The slot-agreement predicates are those of
//! [`crate::rel`] (they speak of LIR states only; [`super::steps::lemma_frame_agrees`]
//! shows the two frames have the same number of slots).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A register the templates may use: a general register that is neither the
/// context register nor the link register (and not the zero register).
pub open spec fn scratch(r: u8) -> bool {
    r < 31 && r != abi::ctx_reg() && r != abi::link_reg()
}

/// A state with the same memory and context register, and registers and vector
/// registers of the right size, is related to what `m` is.
pub proof fn lemma_rel_regs(lay: lir::Layout, a: lir::St, m: isa::State, m3: isa::State, nl: nat)
    requires
        rel(lay, a, m, nl),
        m3.mem == m.mem,
        m3.r.len() == 31,
        m3.vreg.len() == 32,
        m3.r[abi::ctx_reg() as int] == m.r[abi::ctx_reg() as int],
    ensures
        rel(lay, a, m3, nl),
{
    super::steps::lemma_abi_consts();
    assert(ctx_of(m3) == ctx_of(m));
    assert(isa::wf(m3));
    assert(ctx_ok(m3));
}

/// A load from slot `j` into a scratch register `r` puts the slot's word there
/// and keeps the relation.
pub proof fn lemma_load_rel(lay: lir::Layout, a: lir::St, m: isa::State, r: u8, j: nat, nl: nat)
    requires
        rel(lay, a, m, nl),
        scratch(r),
        j < nl + a.stack.len(),
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, super::templates::load_slot(r, j)) is Some,
        ({
            let m1 = isa::step(m, super::templates::load_slot(r, j)).unwrap();
            &&& m1 == isa::State {
                r: m.r.update(r as int, lir::val_bits(slot_val(a, nl, j)) as u64),
                pc: (m.pc + 4) as u64,
                ..m
            }
            &&& rel(lay, a, m1, nl)
            &&& m1.r[r as int] as nat == lir::val_bits(slot_val(a, nl, j))
        }),
{
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    let v = lir::val_bits(slot_val(a, nl, j));
    assert(slot_holds(m.mem, ctx_of(m), j, v));
    assert(v < 0x1_0000_0000_0000_0000) by {
        match slot_val(a, nl, j) {
            lir::Val::I32(x) => {},
            lir::Val::I64(x) => {},
            lir::Val::F64(x) => {},
        }
    }
    assert(j < max_slots());
    super::steps::lemma_step_load_slot(m, r, j, v);
    let m1 = isa::step(m, super::templates::load_slot(r, j)).unwrap();
    assert(m1.r.len() == 31);
    lemma_rel_regs(lay, a, m, m1, nl);
    assert(m1.r[r as int] == v as u64);
}

/// `slots_agree` in this module's terms: the frame of `a2` is what the frame of
/// `a` holds.
pub proof fn lemma_rel_agree(lay: lir::Layout, a: lir::St, a2: lir::St, m: isa::State, nl: nat)
    requires
        rel(lay, a, m, nl),
        crate::rel::slots_agree(a, a2, nl),
    ensures
        rel(lay, a2, m, nl),
{
    super::steps::lemma_frame_agrees();
    assert forall|j: nat| j < nl + a2.stack.len() implies #[trigger] slot_holds(
        m.mem,
        ctx_of(m),
        j,
        lir::val_bits(slot_val(a2, nl, j)),
    ) by {
        assert(lir::val_bits(slot_val(a2, nl, j)) >= 0);
        assert(j < nl + a.stack.len());
        assert(slot_holds(m.mem, ctx_of(m), j, lir::val_bits(slot_val(a, nl, j))));
    }
}

/// The 8 bytes of a slot are in the exit area.
pub proof fn lemma_slot_in_exit_area(ctxb: int, j: nat, b: int)
    requires
        j < max_slots(),
        ctxb + slot_disp(j) <= b < ctxb + slot_disp(j) + 8,
    ensures
        in_exit_area(ctxb, b),
{
    super::steps::lemma_abi_consts();
}

/// Two different slots do not overlap.
pub proof fn lemma_slots_disjoint(ctxb: int, j: nat, ts: nat, b: int)
    requires
        j != ts,
        ctxb + slot_disp(j) <= b < ctxb + slot_disp(j) + 8,
    ensures
        b < ctxb + slot_disp(ts) || ctxb + slot_disp(ts) + 8 <= b,
{
    super::steps::lemma_abi_consts();
}

/// **The store finishes the template.** With the result word `w` in register
/// `rd`, storing it to slot `ts` takes the machine to a state related to the
/// next LIR state `a2`, `pc` four further, and nothing outside the exit area
/// changed since `m0` (the state the template started from).
#[verifier::rlimit(500)]
pub proof fn lemma_store_finish(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m0: isa::State,
    m3: isa::State,
    nl: nat,
    ts: nat,
    rd: u8,
    w: nat,
)
    requires
        rel(lay, a, m3, nl),
        rel(lay, a, m0, nl),
        m3.mem == m0.mem,
        m3.sp == m0.sp,
        m3.r[abi::link_reg() as int] == m0.r[abi::link_reg() as int],
        m3.r[abi::ctx_reg() as int] == m0.r[abi::ctx_reg() as int],
        crate::rel::slots_agree_except(a, a2, nl, ts),
        w == lir::val_bits(slot_val(a2, nl, ts)),
        ts < max_slots(),
        rd < 31,
        m3.r[rd as int] as nat == w,
        m3.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m3, super::templates::store_slot(ts, rd)) is Some,
        ({
            let m4 = isa::step(m3, super::templates::store_slot(ts, rd)).unwrap();
            &&& rel(lay, a2, m4, nl)
            &&& m4.pc as int == m3.pc as int + 4
            &&& preserved(m0, m4)
        }),
{
    super::steps::lemma_abi_consts();
    super::steps::lemma_frame_agrees();
    let ctxb = ctx_of(m3);
    assert(ctx_of(m0) == ctxb);
    super::steps::lemma_step_store_slot(m3, rd, ts);
    let m4 = isa::step(m3, super::templates::store_slot(ts, rd)).unwrap();
    assert(m4.r == m3.r && m4.vreg == m3.vreg && m4.sp == m3.sp);
    assert(isa::wf(m4)) by {
        assert(m4.mem.dom() =~= m3.mem.dom());
    }
    assert(ctx_of(m4) == ctxb);
    assert(ctx_ok(m4));
    assert(exit_area_mapped(m4.mem, ctxb));
    // every slot of a2
    assert forall|j: nat| j < nl + a2.stack.len() implies #[trigger] slot_holds(
        m4.mem,
        ctxb,
        j,
        lir::val_bits(slot_val(a2, nl, j)),
    ) by {
        assert(lir::val_bits(slot_val(a2, nl, j)) >= 0);
        if j == ts {
            assert(m3.r[rd as int] as int == w as int);
        } else {
            assert(j < nl + a.stack.len());
            assert(slot_holds(m3.mem, ctxb, j, lir::val_bits(slot_val(a, nl, j))));
            assert(j < max_slots());
            super::steps::lemma_slot_addr(m3, j);
            assert forall|i: int| 0 <= i < 8 implies (m3.mem.dom().contains(
                #[trigger] (ctxb + slot_disp(j) + i),
            ) == m4.mem.dom().contains(ctxb + slot_disp(j) + i)) && (m3.mem.dom().contains(
                ctxb + slot_disp(j) + i,
            ) ==> m3.mem[ctxb + slot_disp(j) + i] == m4.mem[ctxb + slot_disp(j) + i]) by {
                lemma_slots_disjoint(ctxb, j, ts, ctxb + slot_disp(j) + i);
                assert(m4.mem.dom().contains(ctxb + slot_disp(j) + i) == m3.mem.dom().contains(
                    ctxb + slot_disp(j) + i,
                ));
            }
            super::memlemmas::lemma_mem_read_congr(m3.mem, m4.mem, ctxb + slot_disp(j), 8);
        }
    }
    // memory outside the exit area is untouched
    assert forall|b: int| #[trigger] m0.mem.dom().contains(b) && !in_exit_area(ctxb, b) implies m4.mem[b]
        == m0.mem[b] by {
        if b < ctxb + slot_disp(ts) || ctxb + slot_disp(ts) + 8 <= b {
        } else {
            lemma_slot_in_exit_area(ctxb, ts, b);
        }
    }
    assert(mem_rel(lay, a2.mem, m4.mem)) by {
        assert forall|b: nat| #[trigger] in_regions(lay, b) implies m4.mem.dom().contains(b as int)
            && m4.mem[b as int] == lir::byte_at(a2.mem, b) by {
            assert(!in_exit_area(ctxb, b as int));
            assert(m3.mem.dom().contains(b as int) && m3.mem[b as int] == lir::byte_at(a.mem, b));
            assert(m0.mem.dom().contains(b as int));
        }
    }
    assert(preserved_mem(m0, m4));
}

} // verus!
