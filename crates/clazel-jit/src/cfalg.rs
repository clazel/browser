//! The algebra of the control-flow statements: [`preserved_mem_r`] is
//! transitive, it carries the native stack word and the region table, the
//! relation survives truncating the stack to a prefix, and a [`cf_refines`]
//! statement can be used at one state.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`preserved_r`] is [`preserved_mem_r`] with the stack pointer.
pub proof fn lemma_pr_mem(lay: lir::Layout, m: x64::State, m2: x64::State)
    requires
        preserved_r(lay, m, m2),
    ensures
        preserved_mem_r(lay, m, m2),
{
}

/// [`preserved_mem_r`] is transitive.
pub proof fn lemma_pmr_trans(lay: lir::Layout, m: x64::State, m1: x64::State, m2: x64::State)
    requires
        preserved_mem_r(lay, m, m1),
        preserved_mem_r(lay, m1, m2),
    ensures
        preserved_mem_r(lay, m, m2),
{
    super::steps::lemma_abi_consts();
    assert(ctx_of(m1) == ctx_of(m));
    assert forall|b: int|
        #[trigger] m.mem.dom().contains(b) && !in_exit_area(ctx_of(m), b) && !in_regions_i(
            lay,
            b,
        ) implies m2.mem[b] == m.mem[b] by {
        assert(m1.mem.dom().contains(b));
        assert(m1.mem[b] == m.mem[b]);
        assert(m2.mem[b] == m1.mem[b]);
    }
}

/// [`preserved_r`] is transitive.
pub proof fn lemma_pr_trans(lay: lir::Layout, m: x64::State, m1: x64::State, m2: x64::State)
    requires
        preserved_r(lay, m, m1),
        preserved_r(lay, m1, m2),
    ensures
        preserved_r(lay, m, m2),
{
    lemma_pmr_trans(lay, m, m1, m2);
}

/// [`preserved_r`] then [`preserved_mem_r`] is [`preserved_mem_r`].
pub proof fn lemma_pr_pmr_trans(lay: lir::Layout, m: x64::State, m1: x64::State, m2: x64::State)
    requires
        preserved_r(lay, m, m1),
        preserved_mem_r(lay, m1, m2),
    ensures
        preserved_mem_r(lay, m, m2),
{
    lemma_pmr_trans(lay, m, m1, m2);
}

/// A successful read of `n` bytes means each byte is mapped.
pub proof fn read_mem_some_dom(mm: Map<int, u8>, a: int, n: nat, i: int)
    requires
        x64::read_mem(mm, a, n) is Some,
        0 <= i < n,
    ensures
        mm.dom().contains(a + i),
    decreases n,
{
    if i > 0 {
        read_mem_some_dom(mm, a + 1, (n - 1) as nat, i - 1);
        assert(a + 1 + (i - 1) == a + i);
    }
}

/// A read of mapped bytes that are outside the exit area and every region
/// gives the same result after a run that preserves everything else.
pub proof fn lemma_read_pres(
    lay: lir::Layout,
    m: x64::State,
    m1: x64::State,
    a: int,
    n: nat,
)
    requires
        preserved_mem_r(lay, m, m1),
        x64::read_mem(m.mem, a, n) is Some,
        forall|i: int| 0 <= i < n ==> !in_exit_area(ctx_of(m), #[trigger] (a + i)) && !in_regions_i(lay, a + i),
    ensures
        x64::read_mem(m1.mem, a, n) == x64::read_mem(m.mem, a, n),
{
    assert forall|i: int| 0 <= i < n implies (m.mem.dom().contains(#[trigger] (a + i))
        == m1.mem.dom().contains(a + i)) && (m.mem.dom().contains(a + i) ==> m.mem[a + i]
        == m1.mem[a + i]) by {
        read_mem_some_dom(m.mem, a, n, i);
    }
    super::memlemmas::lemma_read_mem_congr(m.mem, m1.mem, a, n);
}

/// **The native stack word survives.** After a run that preserves
/// everything outside the exit area and the regions and keeps `rsp`, the stack is
/// still as the exit sequence's `ret` needs it, and holds the same word.
pub proof fn lemma_stack_pres(lay: lir::Layout, m: x64::State, m1: x64::State)
    requires
        stack_ok_r(lay, m),
        preserved_r(lay, m, m1),
    ensures
        stack_ok_r(lay, m1),
        x64::read_mem(m1.mem, x64::logext(64, m.rgf[abi::sp_reg() as int] as int), 8)
            == x64::read_mem(m.mem, x64::logext(64, m.rgf[abi::sp_reg() as int] as int), 8),
{
    super::steps::lemma_abi_consts();
    let rsp = x64::logext(64, m.rgf[abi::sp_reg() as int] as int);
    assert(ctx_of(m1) == ctx_of(m));
    assert(m1.rgf[abi::sp_reg() as int] == m.rgf[abi::sp_reg() as int]);
    assert(x64::read_mem(m.mem, rsp, 8) is Some);
    assert forall|i: int| 0 <= i < 8 implies !in_exit_area(ctx_of(m), #[trigger] (rsp + i))
        && !in_regions_i(lay, rsp + i) by {
        assert(!in_regions_i(lay, rsp + i));
    }
    lemma_read_pres(lay, m, m1, rsp, 8);
}

/// **The region table survives.** What is outside the exit area and every
/// region is unchanged, and the table is both.
pub proof fn lemma_table_pres(lay: lir::Layout, m: x64::State, m1: x64::State)
    requires
        table_ok(lay, m),
        preserved_mem_r(lay, m, m1),
    ensures
        table_ok(lay, m1),
{
    super::steps::lemma_abi_consts();
    assert(ctx_of(m1) == ctx_of(m));
    assert forall|k: int| 0 <= k < lay.len() implies {
        &&& x64::read_mem(m1.mem, ctx_of(m1) + abi::base_off(k), 8) == Some(
            (#[trigger] lay[k]).base as int,
        )
        &&& x64::read_mem(m1.mem, ctx_of(m1) + abi::bound_off(k), 8) == Some(lay[k].bound as int)
    } by {
        let a1 = ctx_of(m) + abi::base_off(k);
        let a2 = ctx_of(m) + abi::bound_off(k);
        assert(x64::read_mem(m.mem, a1, 8) == Some(lay[k].base as int));
        assert(x64::read_mem(m.mem, a2, 8) == Some(lay[k].bound as int));
        assert forall|i: int| 0 <= i < 8 implies !in_exit_area(ctx_of(m), #[trigger] (a1 + i))
            && !in_regions_i(lay, a1 + i) by {
            assert(ctx_of(m) <= a1 + i < ctx_of(m) + abi::table_end());
        }
        assert forall|i: int| 0 <= i < 8 implies !in_exit_area(ctx_of(m), #[trigger] (a2 + i))
            && !in_regions_i(lay, a2 + i) by {
            assert(ctx_of(m) <= a2 + i < ctx_of(m) + abi::table_end());
        }
        lemma_read_pres(lay, m, m1, a1, 8);
        lemma_read_pres(lay, m, m1, a2, 8);
    }
    assert forall|b: int| ctx_of(m1) <= b < ctx_of(m1) + abi::table_end() implies !#[trigger] in_regions_i(
        lay,
        b,
    ) by {
        assert(ctx_of(m) <= b < ctx_of(m) + abi::table_end());
    }
}

/// The relation survives truncating the stack to a prefix.
pub proof fn lemma_rel_prefix(
    lay: lir::Layout,
    a: lir::St,
    full: Seq<lir::Val>,
    pre: Seq<lir::Val>,
    m: x64::State,
    nl: nat,
)
    requires
        rel(lay, a.with_stack(full), m, nl),
        pre.len() <= full.len(),
        pre =~= full.take(pre.len() as int),
    ensures
        rel(lay, a.with_stack(pre), m, nl),
{
    let a1 = a.with_stack(full);
    let a2 = a.with_stack(pre);
    assert(super::rel::slots_agree(a1, a2, nl)) by {
        assert forall|j: nat| j < nl + a2.stack.len() implies j < nl + a1.stack.len()
            && #[trigger] lir::val_bits(slot_val(a2, nl, j)) == lir::val_bits(slot_val(a1, nl, j)) by {
            if j >= nl {
                assert(a2.stack[(j - nl) as int] == a1.stack[(j - nl) as int]);
            }
        }
    }
    super::rel::lemma_rel_agree(lay, a1, a2, m, nl);
}

/// What [`rel_base`] says, unfolded (it is opaque elsewhere).
pub proof fn lemma_rel_base_unfold(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    nl: nat,
)
    requires
        rel_base(lay, base, a, m, nl),
    ensures
        rel(lay, a.with_stack(base + a.stack), m, nl),
        table_ok(lay, m),
        x64::wf(m),
        ctx_ok(m),
{
    reveal(rel_base);
}

/// **A [`cf_refines`] statement, used at one state.**
pub proof fn lemma_use_cf(
    i: lir::Instr,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    code: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    fuel: nat,
)
    requires
        cf_refines(i, nl, h, offs, code),
        base.len() + a.stack.len() == h,
        rel_base(lay, base, a, m, nl),
        stack_ok_r(lay, m),
        cf_canon(m.rip, offs, code),
    ensures
        cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, i, a, fuel)),
{
}

} // verus!
