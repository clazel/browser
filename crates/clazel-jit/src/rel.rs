//! Lemmas about the state relation [`rel`]: it survives a change that only
//! touches scratch registers, a load into a scratch register, and a store to
//! one frame slot (when the LIR state changes at that slot only).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A register a template may write: not the context register, not `rsp`.
pub open spec fn scratch(r: u8) -> bool {
    r < 16 && r != abi::ctx_reg() && r != abi::sp_reg()
}

/// `rel` does not mention registers other than `r15`, nor the flags, `rip`
/// (beyond being canonical) or the XMM registers: a state with the same
/// memory and context register is related to what `m` was.
pub proof fn lemma_rel_regs(
    lay: lir::Layout,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
    nl: nat,
)
    requires
        rel(lay, a, m, nl),
        m3.mem == m.mem,
        m3.rgf.len() == 16,
        m3.xmm.len() == 16,
        m3.rgf[abi::ctx_reg() as int] == m.rgf[abi::ctx_reg() as int],
        x64::canonical(m3.rip),
    ensures
        rel(lay, a, m3, nl),
{
    super::steps::lemma_abi_consts();
    assert(ctx_of(m3) == ctx_of(m));
    assert(x64::wf(m3));
    assert(ctx_ok(m3));
}

/// `mov r, [slot j]` for a scratch register `r`: loads the slot's word, and the
/// state stays related to the same LIR state.
pub proof fn lemma_load_rel(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    a: lir::St,
    m: x64::State,
    r: u8,
    j: nat,
    nl: nat,
)
    requires
        rel(lay, a, m, nl),
        scratch(r),
        j < nl + a.stack.len(),
        x64::canonical(m.rip + x64::instr_len(super::templates::load_slot(r, j))),
    ensures
        x64::step(cu, m, super::templates::load_slot(r, j)) is Some,
        ({
            let m1 = x64::step(cu, m, super::templates::load_slot(r, j)).unwrap();
            &&& m1 == x64::State {
                rgf: m.rgf.update(r as int, lir::val_bits(slot_val(a, nl, j)) as u64),
                rip: m.rip + x64::instr_len(super::templates::load_slot(r, j)),
                ..m
            }
            &&& rel(lay, a, m1, nl)
            &&& m1.rgf[r as int] as nat == lir::val_bits(slot_val(a, nl, j))
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
    super::steps::lemma_step_load_slot(cu, m, r, j, v);
    let m1 = x64::step(cu, m, super::templates::load_slot(r, j)).unwrap();
    assert(m1.rgf.len() == 16);
    lemma_rel_regs(lay, a, m, m1, nl);
    assert(m1.rgf[r as int] == v as u64);
}

/// The LIR state `a2` has the slots of `a` except at `ts`: same locals count,
/// same memory, a frame that fits, and every other slot holds the same word.
pub open spec fn slots_agree_except(a: lir::St, a2: lir::St, nl: nat, ts: nat) -> bool {
    a2.locals.len() == nl && nl + a2.stack.len() <= max_slots() && a2.mem == a.mem && ts < nl
        + a2.stack.len() && forall|j: nat|
        #![trigger lir::val_bits(slot_val(a2, nl, j))]
        j < nl + a2.stack.len() && j != ts ==> j < nl + a.stack.len() && lir::val_bits(
            slot_val(a2, nl, j),
        ) == lir::val_bits(slot_val(a, nl, j))
}

/// As [`slots_agree_except`], with no exception: the slots of `a2` are all
/// slots of `a`, with the same words.
pub open spec fn slots_agree(a: lir::St, a2: lir::St, nl: nat) -> bool {
    a2.locals.len() == nl && nl + a2.stack.len() <= max_slots() && a2.mem == a.mem && forall|
        j: nat,
    |
        #![trigger lir::val_bits(slot_val(a2, nl, j))]
        j < nl + a2.stack.len() ==> j < nl + a.stack.len() && lir::val_bits(slot_val(a2, nl, j))
            == lir::val_bits(slot_val(a, nl, j))
}

/// If the slots of `a2` are slots of `a` with the same words, `a2` is related
/// to whatever `a` was.
pub proof fn lemma_rel_agree(lay: lir::Layout, a: lir::St, a2: lir::St, m: x64::State, nl: nat)
    requires
        rel(lay, a, m, nl),
        slots_agree(a, a2, nl),
    ensures
        rel(lay, a2, m, nl),
{
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

/// The exit area is within the context.
pub proof fn lemma_slot_in_exit_area(ctxb: int, j: nat, b: int)
    requires
        j < max_slots(),
        ctxb + slot_disp(j) <= b < ctxb + slot_disp(j) + 8,
    ensures
        in_exit_area(ctxb, b),
{
    super::steps::lemma_abi_consts();
}

/// `mov [slot ts], rd` finishes a template: from a state `m3` related to the
/// LIR state `a` (the template's registers computed, memory untouched since
/// `m0`, where the template began), with `rd` holding the word `w` that `a2`
/// keeps in slot `ts`, the store leaves a state related to `a2`, and `m0`
/// and the result differ in the exit area only ([`preserved`]).
pub proof fn lemma_store_finish(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m0: x64::State,
    m3: x64::State,
    nl: nat,
    ts: nat,
    rd: u8,
    w: nat,
)
    requires
        rel(lay, a, m3, nl),
        rel(lay, a, m0, nl),
        m3.mem == m0.mem,
        m3.rgf[abi::sp_reg() as int] == m0.rgf[abi::sp_reg() as int],
        m3.rgf[abi::ctx_reg() as int] == m0.rgf[abi::ctx_reg() as int],
        slots_agree_except(a, a2, nl, ts),
        w == lir::val_bits(slot_val(a2, nl, ts)),
        ts < max_slots(),
        rd < 16,
        m3.rgf[rd as int] as nat == w,
        x64::canonical(m3.rip + x64::instr_len(super::templates::store_slot(ts, rd))),
    ensures
        x64::step(cu, m3, super::templates::store_slot(ts, rd)) is Some,
        ({
            let m4 = x64::step(cu, m3, super::templates::store_slot(ts, rd)).unwrap();
            &&& rel(lay, a2, m4, nl)
            &&& m4.rip == m3.rip + x64::instr_len(super::templates::store_slot(ts, rd))
            &&& preserved(m0, m4)
        }),
{
    super::steps::lemma_abi_consts();
    let ctxb = ctx_of(m3);
    assert(ctx_of(m0) == ctxb);
    super::steps::lemma_step_store_slot(cu, m3, rd, ts);
    let m4 = x64::step(cu, m3, super::templates::store_slot(ts, rd)).unwrap();
    assert(m4.rgf == m3.rgf && m4.xmm == m3.xmm);
    assert(x64::wf(m4)) by {
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
        } else {
            assert(j < nl + a.stack.len());
            assert(slot_holds(m3.mem, ctxb, j, lir::val_bits(slot_val(a, nl, j))));
            assert(j < max_slots());
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
