//! What one `x64::step` does, for each instruction form the templates use:
//! a load from or store to a frame slot, an immediate move, a register move,
//! and the arithmetic, logic, shift, multiply, compare, test, set and
//! conditional-move forms. Each lemma computes the state `step` returns, in
//! terms of the state it is given, so a template's proof is a chain of them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The ABI constants the lemmas need, evaluated.
pub proof fn lemma_abi_consts()
    ensures
        abi::ctx_reg() == 15,
        abi::sp_reg() == 4,
        abi::exit_code_off() == 256,
        abi::ctx_size() == 512,
        frame_off() == 264,
        max_slots() == 31,
{
}

/// The address of frame slot `j`, formed by the effective-address rule from the
/// context register, is the context plus the slot's displacement, with no
/// wrap-around.
pub proof fn lemma_slot_ea(m: x64::State, j: nat)
    requires
        ctx_ok(m),
        j < max_slots(),
    ensures
        x64::eff_addr(m, slot_mem(j)) == ctx_of(m) + slot_disp(j),
        (slot_disp(j) as i32) as int == slot_disp(j),
        0 <= slot_disp(j) < 512,
{
    super::memlemmas::lemma_p2_consts();
    lemma_abi_consts();
    let d = slot_disp(j);
    assert(d == 264 + 8 * j);
    assert((d as i32) as int == d);
    let x = ctx_of(m) + d;
    assert(0 <= x && x < 0x8000_0000_0000 + 512);
    assert(x64::loghead(64, x) == x);
    assert(x64::logext(64, x) == x);
    assert(x64::eff_addr(m, slot_mem(j)) == x64::logext(64, ctx_of(m) + 0 + d));
}

/// `mov dst, [slot j]` puts the slot's word in `dst` and advances `rip`.
pub proof fn lemma_step_load_slot(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    dst: u8,
    j: nat,
    v: nat,
)
    requires
        x64::wf(m),
        ctx_ok(m),
        dst < 16,
        j < max_slots(),
        slot_holds(m.mem, ctx_of(m), j, v),
        v < 0x1_0000_0000_0000_0000,
        x64::canonical(m.rip + x64::instr_len(super::templates::load_slot(dst, j))),
    ensures
        x64::step(cu, m, super::templates::load_slot(dst, j)) == Some(
            x64::State {
                rgf: m.rgf.update(dst as int, v as u64),
                rip: m.rip + x64::instr_len(super::templates::load_slot(dst, j)),
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    lemma_slot_ea(m, j);
    let i = super::templates::load_slot(dst, j);
    assert(x64::read_operand_mem(m, x64::Size::W64, slot_mem(j)) == Some(v as int));
    assert(x64::loghead(64, v as int) == v as int);
    assert(x64::wr64(m, dst, v as int) == x64::State { rgf: m.rgf.update(dst as int, v as u64), ..m });
}

/// `mov [slot j], src` writes the word in `src` to the slot, and to no other
/// byte of memory: every other slot, and every byte outside the slot, is as
/// it was. Registers, flags and the XMM registers are unchanged.
pub proof fn lemma_step_store_slot(cu: spec_fn(nat) -> nat, m: x64::State, src: u8, j: nat)
    requires
        x64::wf(m),
        ctx_ok(m),
        src < 16,
        j < max_slots(),
        exit_area_mapped(m.mem, ctx_of(m)),
        x64::canonical(m.rip + x64::instr_len(super::templates::store_slot(j, src))),
    ensures
        x64::step(cu, m, super::templates::store_slot(j, src)) is Some,
        ({
            let m1 = x64::step(cu, m, super::templates::store_slot(j, src)).unwrap();
            &&& m1 == x64::State { mem: m1.mem, rip: m.rip + x64::instr_len(super::templates::store_slot(j, src)), ..m }
            &&& slot_holds(m1.mem, ctx_of(m), j, m.rgf[src as int] as nat)
            &&& forall|k: nat, w: nat|
                k < max_slots() && k != j && #[trigger] slot_holds(m.mem, ctx_of(m), k, w)
                    ==> slot_holds(m1.mem, ctx_of(m), k, w)
            &&& m1.mem.dom() =~= m.mem.dom()
            &&& forall|b: int|
                #![trigger m1.mem.dom().contains(b)]
                m.mem.dom().contains(b) && (b < ctx_of(m) + slot_disp(j) || ctx_of(m)
                    + slot_disp(j) + 8 <= b) ==> m1.mem[b] == m.mem[b]
        }),
{
    super::memlemmas::lemma_p2_consts();
    lemma_slot_ea(m, j);
    let ctxb = ctx_of(m);
    let addr = ctxb + slot_disp(j);
    let w = m.rgf[src as int] as int;
    assert(x64::rgfi_size(m, x64::Size::W64, src) == w);
    assert forall|i: int| 0 <= i < 8 implies m.mem.dom().contains(#[trigger] (addr + i)) by {
        assert(in_exit_area(ctxb, addr + i));
    }
    super::memlemmas::lemma_write_mem_some(m.mem, addr, 8, w);
    let m2 = x64::write_mem(m.mem, addr, 8, w).unwrap();
    super::memlemmas::lemma_write_mem_frame(m.mem, addr, 8, w, m2);
    assert(0 <= w < vstd::arithmetic::power2::pow2(8 * 8) as int) by {
        assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000);
    }
    super::memlemmas::lemma_read_after_write_same(m.mem, addr, 8, w, m2);
    assert(x64::store_mem(m, slot_mem(j), x64::Size::W64, w) == Some(x64::State { mem: m2, ..m }));
    let m1 = x64::step(cu, m, super::templates::store_slot(j, src)).unwrap();
    assert(m1.mem == m2);
    assert forall|k: nat, v: nat|
        k < max_slots() && k != j && #[trigger] slot_holds(m.mem, ctxb, k, v) implies slot_holds(
        m1.mem,
        ctxb,
        k,
        v,
    ) by {
        lemma_abi_consts();
        super::memlemmas::lemma_read_after_write_disjoint(m.mem, addr, 8, w, m2, ctxb + slot_disp(k), 8);
    }
}

/// `mov dst, imm64` and `mov dst, imm32` (zero-extending).
pub proof fn lemma_step_imm(cu: spec_fn(nat) -> nat, m: x64::State, i: x64::Instr)
    requires
        x64::wf(m),
        x64::canonical(m.rip + x64::instr_len(i)),
        i is MovImm64 || i is MovImm32,
        i is MovImm64 ==> i->MovImm64_dst < 16,
        i is MovImm32 ==> i->MovImm32_dst < 16,
    ensures
        i is MovImm64 ==> x64::step(cu, m, i) == Some(
            x64::State {
                rgf: m.rgf.update(i->MovImm64_dst as int, i->MovImm64_imm_u64),
                rip: m.rip + x64::instr_len(i),
                ..m
            },
        ),
        i is MovImm32 ==> x64::step(cu, m, i) == Some(
            x64::State {
                rgf: m.rgf.update(i->MovImm32_dst as int, i->MovImm32_imm_u32 as u64),
                rip: m.rip + x64::instr_len(i),
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    if i is MovImm64 {
        assert(x64::loghead(64, i->MovImm64_imm_u64 as int) == i->MovImm64_imm_u64 as int);
    } else {
        assert(x64::loghead(32, i->MovImm32_imm_u32 as int) == i->MovImm32_imm_u32 as int);
        assert(x64::loghead(64, i->MovImm32_imm_u32 as int) == i->MovImm32_imm_u32 as int);
    }
}

/// `mov dst32, src32`: the low 32 bits of `src`, zero-extended, into `dst`.
pub proof fn lemma_step_mov_rr32(cu: spec_fn(nat) -> nat, m: x64::State, dst: u8, src: u8)
    requires
        x64::wf(m),
        dst < 16,
        src < 16,
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::MovRR { sz: x64::Size::W32, dst: dst, src: src }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::MovRR { sz: x64::Size::W32, dst: dst, src: src }) == Some(
            x64::State {
                rgf: m.rgf.update(dst as int, (m.rgf[src as int] % 0x1_0000_0000) as u64),
                rip: m.rip + x64::instr_len(
                    x64::Instr::MovRR { sz: x64::Size::W32, dst: dst, src: src },
                ),
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    let v = m.rgf[src as int] as int % 0x1_0000_0000;
    assert(x64::loghead(64, v) == v);
}

} // verus!
