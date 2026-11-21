//! What one [`isa::step`] does for the two instruction forms every template
//! has: a load from, and a store to, a frame slot. Each lemma computes the
//! state `step` returns, in terms of the state it is given, so a template's
//! proof is a chain of them. The A64 counterpart of [`crate::steps`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The ABI constants the lemmas need, evaluated.
pub proof fn lemma_abi_consts()
    ensures
        abi::ctx_reg() == 28,
        abi::link_reg() == 30,
        abi::sp_reg() == 31,
        abi::exit_code_off() == 256,
        abi::ctx_size() == 512,
        frame_off() == 264,
        max_slots() == 31,
        x0() == 0,
        x1() == 1,
        x2() == 2,
{
}

/// The A64 and the x86-64 ABIs put the frame in the same place, so
/// [`crate::spec`]'s frame lemmas and `agree` lemmas (which are stated with its
/// `max_slots`) apply here.
pub proof fn lemma_frame_agrees()
    ensures
        max_slots() == crate::spec::max_slots(),
        frame_off() == crate::spec::frame_off(),
        forall|j: nat| slot_disp(j) == crate::spec::slot_disp(j),
        abi::exit_code_off() == crate::spec::abi::exit_code_off(),
        abi::ctx_size() == crate::spec::abi::ctx_size(),
{
}

/// The `imm12` of slot `j`'s `ldr`/`str` is `33 + j`, and times 8 it is the
/// slot's displacement.
pub proof fn lemma_slot_imm(j: nat)
    requires
        j < max_slots(),
    ensures
        slot_imm(j) as int == 33 + j,
        slot_imm(j) as int * 8 == slot_disp(j),
        slot_imm(j) < 4096,
{
}

/// The address of frame slot `j`: the context plus the slot's displacement, no
/// wrap-around.
pub proof fn lemma_slot_addr(m: isa::State, j: nat)
    requires
        ctx_ok(m),
        j < max_slots(),
    ensures
        0 <= ctx_of(m) + slot_disp(j),
        ctx_of(m) + slot_disp(j) + 8 <= ctx_of(m) + abi::ctx_size(),
        ctx_of(m) + slot_disp(j) + 8 < 0x1_0000_0000_0000_0000,
        isa::trunc(64, ctx_of(m) + slot_disp(j)) == ctx_of(m) + slot_disp(j),
        isa::trunc(64, ctx_of(m) + isa::trunc(64, slot_imm(j) as int * 8)) == ctx_of(m) + slot_disp(j),
{
    super::memlemmas::lemma_p2_consts();
    lemma_abi_consts();
    lemma_slot_imm(j);
    super::memlemmas::lemma_trunc64(ctx_of(m) + slot_disp(j));
    super::memlemmas::lemma_trunc64(slot_imm(j) as int * 8);
    super::memlemmas::lemma_trunc64(ctx_of(m) + slot_disp(j));
}

/// `x_read(s, n, 64)` of a register is its value.
pub proof fn lemma_x_read64(s: isa::State, n: u8)
    requires
        s.r.len() == 31,
        n < 31,
    ensures
        isa::x_read(s, n, 64) == s.r[n as int] as int,
{
    super::memlemmas::lemma_p2_consts();
    super::memlemmas::lemma_trunc64(s.r[n as int] as int);
}

/// `ldr xr, [x28, #(264 + 8 j)]` loads the word in slot `j` into `xr`, advances
/// `pc` by 4, and changes nothing else.
pub proof fn lemma_step_load_slot(m: isa::State, r: u8, j: nat, v: nat)
    requires
        isa::wf(m),
        ctx_ok(m),
        r < 31,
        j < max_slots(),
        slot_holds(m.mem, ctx_of(m), j, v),
        v < 0x1_0000_0000_0000_0000,
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, super::templates::load_slot(r, j)) == Some(
            isa::State { r: m.r.update(r as int, v as u64), pc: (m.pc + 4) as u64, ..m },
        ),
{
    super::memlemmas::lemma_p2_consts();
    lemma_abi_consts();
    lemma_slot_imm(j);
    lemma_slot_addr(m, j);
    lemma_x_read64(m, 28);
    super::memlemmas::lemma_trunc64(v as int);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    let i = super::templates::load_slot(r, j);
    assert(isa::x_read(m, 28, 64) == ctx_of(m));
    assert(isa::mem_read(m.mem, ctx_of(m) + slot_disp(j), 8) == Some(v as int));
    assert(isa::execute(m, i) == Some(isa::x_set(m, r, 64, v as int)));
    assert(isa::x_set(m, r, 64, v as int) == isa::State { r: m.r.update(r as int, v as u64), ..m });
}

/// `str xr, [x28, #(264 + 8 j)]` writes the word in `xr` to slot `j` (the exit
/// area is mapped, so it does not fault), advances `pc` by 4, and changes
/// nothing but those 8 bytes.
pub proof fn lemma_step_store_slot(m: isa::State, src: u8, j: nat)
    requires
        isa::wf(m),
        ctx_ok(m),
        src < 31,
        j < max_slots(),
        exit_area_mapped(m.mem, ctx_of(m)),
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, super::templates::store_slot(j, src)) is Some,
        ({
            let m1 = isa::step(m, super::templates::store_slot(j, src)).unwrap();
            &&& m1 == isa::State { mem: m1.mem, pc: (m.pc + 4) as u64, ..m }
            &&& isa::mem_read(m1.mem, ctx_of(m) + slot_disp(j), 8) == Some(m.r[src as int] as int)
            &&& m1.mem.dom() =~= m.mem.dom()
            &&& forall|b: int|
                #![trigger m1.mem.dom().contains(b)]
                m.mem.dom().contains(b) && (b < ctx_of(m) + slot_disp(j) || ctx_of(m) + slot_disp(j)
                    + 8 <= b) ==> m1.mem[b] == m.mem[b]
        }),
{
    super::memlemmas::lemma_p2_consts();
    lemma_abi_consts();
    lemma_slot_imm(j);
    lemma_slot_addr(m, j);
    lemma_x_read64(m, 28);
    lemma_x_read64(m, src);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    let i = super::templates::store_slot(j, src);
    let ctxb = ctx_of(m);
    let addr = ctxb + slot_disp(j);
    let w = m.r[src as int] as int;
    assert(isa::x_read(m, 28, 64) == ctxb);
    assert(isa::x_read(m, src, 64) == w);
    assert forall|k: int| 0 <= k < 8 implies m.mem.dom().contains(#[trigger] (addr + k)) by {
        assert(in_exit_area(ctxb, addr + k));
    }
    super::memlemmas::lemma_mem_set_some(m.mem, addr, 8, w);
    let m2 = isa::mem_set(m.mem, addr, 8, w).unwrap();
    super::memlemmas::lemma_mem_set_frame(m.mem, addr, 8, w, m2);
    assert(0 <= w < vstd::arithmetic::power2::pow2(8 * 8) as int) by {
        assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000) by {
            vstd::arithmetic::power2::lemma2_to64_rest();
        }
    }
    super::memlemmas::lemma_read_after_write_same(m.mem, addr, 8, w, m2);
    assert(isa::execute(m, i) == Some(isa::State { mem: m2, ..m }));
}

} // verus!
