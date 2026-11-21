//! The effect of the frame-access blocks of [`super::lower`] on LIR's state,
//! under the relation [`rel`]: computing a slot's address (never failing its
//! bounds check), loading a slot, storing to a slot.

#[allow(unused_imports)]
use super::lirmem::*;
#[allow(unused_imports)]
use super::lower::*;
#[allow(unused_imports)]
use super::run::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `i64.add` of two small numbers is their sum.
pub proof fn lemma_add_small(x: u64, y: u64)
    requires
        (x as int) + (y as int) < 0x1_0000_0000_0000_0000,
    ensures
        lir::ibin64(lir::IBin::Add, x, y) == (x + y) as u64,
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    assert(((x as int) + (y as int)) % 0x1_0000_0000_0000_0000int == (x as int) + (y as int)) by (nonlinear_arith)
        requires
            0 <= (x as int) + (y as int) < 0x1_0000_0000_0000_0000int,
    ;
}

/// The slot `off` bytes from the frame base is inside region 0.
pub open spec fn slot_ok(s: js::State, off: nat) -> bool {
    off % 8 == 0 && s.fp + off / 8 < s.region.len()
}

/// The address block pushes the slot's byte index and never exits.
pub proof fn lemma_exec_addr(lay: lir::Layout, s: js::State, st: lir::St, off: nat)
    requires
        rel(lay, s, st),
        slot_ok(s, off),
    ensures
        exec(lay, addr_ins(off), st) == lir::Outcome::Normal(
            st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + off) as u64))),
        ),
{
    reveal_with_fuel(exec, 5);
    let base = (8 * s.fp) as u64;
    assert(8 * s.fp + off <= 8 * s.region.len());
    assert(lay[0].bound == 8 * s.region.len());
    assert(lir::layout_wf(lay));
    assert(lay[0].base + lay[0].bound <= 0x1_0000_0000_0000_0000);
    assert(8 * s.fp + off + 8 <= lay[0].bound);
    assert(lay[0].bound <= 0x1_0000_0000_0000_0000);
    lemma_add_small(base, off as u64);
    let s1 = st.stack.push(lir::Val::I64(base));
    let s2 = s1.push(lir::Val::I64(off as u64));
    let s3 = st.stack.push(lir::Val::I64((8 * s.fp + off) as u64));
    assert(lir::below(s2, 2) =~= st.stack);
    assert(lir::below(s2, 2).push(lir::Val::I64((8 * s.fp + off) as u64)) =~= s3);
}


/// The load block pushes the slot's value, and never exits.
pub proof fn lemma_exec_load(lay: lir::Layout, s: js::State, st: lir::St, off: nat)
    requires
        rel(lay, s, st),
        slot_ok(s, off),
    ensures
        exec(lay, load_ins(off), st) == lir::Outcome::Normal(
            st.with_stack(st.stack.push(lir::Val::I64(s.region[(s.fp + off / 8) as int]))),
        ),
{
    lemma_exec_addr(lay, s, st, off);
    let sa = st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + off) as u64)));
    let ld = seq![lir::Instr::Load { region: 0, ty: lir::Ty::I64 }];
    assert(load_ins(off) =~= addr_ins(off) + ld);
    lemma_exec_concat(lay, addr_ins(off), ld, st);
    reveal_with_fuel(exec, 2);
    let j = (s.fp + off / 8) as int;
    assert(8 * s.fp + off == 8 * j);
    assert(lay[0].base + lir::masked(lay[0].bound, (8 * s.fp + off) as nat) == slot_addr(lay, j));
    assert(mem_rel(lay, s.region, st.mem));
    assert(lir::read_le(st.mem, slot_addr(lay, j), 8) == s.region[j] as nat);
    assert(lir::below(sa.stack, 1) =~= st.stack);
}

/// A store: the address block, the value block `val` (which pushes `v` above
/// the address and leaves the memory alone), then the store. The memory
/// holds `v` in the slot, and the relation holds for the region updated.
pub proof fn lemma_exec_store(
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    off: nat,
    val: Seq<lir::Instr>,
    v: u64,
    mid: lir::St,
)
    requires
        rel(lay, s, st),
        slot_ok(s, off),
        exec(
            lay,
            val,
            st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + off) as u64))),
        ) == lir::Outcome::Normal(mid),
        mid.stack == st.stack.push(lir::Val::I64((8 * s.fp + off) as u64)).push(lir::Val::I64(v)),
        mid.mem == st.mem,
        locals_rel(s, mid.locals),
    ensures
        ({
            let j = (s.fp + off / 8) as int;
            let st2 = lir::St {
                stack: st.stack,
                locals: mid.locals,
                mem: lir::write_le(st.mem, slot_addr(lay, j), v as nat, 8),
            };
            &&& exec(lay, store_ins(off, val), st) == lir::Outcome::Normal(st2)
            &&& rel(lay, js::State { region: s.region.update(j, v), ..s }, st2)
        }),
{
    lemma_exec_addr(lay, s, st, off);
    let sa = st.with_stack(st.stack.push(lir::Val::I64((8 * s.fp + off) as u64)));
    let stor = seq![lir::Instr::Store { region: 0, ty: lir::Ty::I64 }];
    assert(store_ins(off, val) =~= (addr_ins(off) + val) + stor);
    lemma_exec_concat(lay, addr_ins(off) + val, stor, st);
    lemma_exec_concat(lay, addr_ins(off), val, st);
    reveal_with_fuel(exec, 2);
    let j = (s.fp + off / 8) as int;
    assert(8 * s.fp + off == 8 * j);
    assert(lay[0].base + lir::masked(lay[0].bound, (8 * s.fp + off) as nat) == slot_addr(lay, j));
    let n = mid.stack.len();
    assert(mid.stack[n - 1] == lir::Val::I64(v));
    assert(mid.stack[n - 2] == lir::Val::I64((8 * s.fp + off) as u64));
    assert(lir::below(mid.stack, 2) =~= st.stack);
    lemma_store_mem_rel(lay, s.region, st.mem, j, v);
    let s2 = js::State { region: s.region.update(j, v), ..s };
    assert(layout_ok(lay, s2));
}

} // verus!
