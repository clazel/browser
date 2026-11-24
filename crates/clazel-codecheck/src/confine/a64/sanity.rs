//! **The hypotheses of the A64 theorem are satisfiable**: a concrete
//! configuration ([`sa_cfg`], the exit sequence `movz w0, #7; str x0, [x28,
//! #256]; ret`, entered at 0, with 16 empty regions) that passes [`cfg_ok`],
//! and a concrete state ([`sa_state`]) that satisfies [`inv`] at its entry. A
//! theorem whose hypotheses nothing satisfies would say nothing; this is the
//! check that it does.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exit sequence's instructions.
pub open spec fn sa_ins() -> Seq<Instr> {
    crate::a64::examples::exit_seq(0, 7)
}

/// Its bytes.
pub open spec fn sa_blob() -> Seq<u8> {
    crate::a64::examples::exit_blob()
}

/// The configuration: code at 4096, the context at 65536, sixteen empty
/// regions at address 0, `SP` 131072, the stub's return address 8.
pub open spec fn sa_cfg() -> Cfg {
    Cfg {
        blob: sa_blob(),
        ins: sa_ins(),
        entries: seq![0int],
        code: 4096,
        ctx: 65536,
        bases: Seq::new(16, |k: int| 0int),
        bounds: Seq::new(16, |k: int| 0int),
        sp: 131072,
        lr: 8,
    }
}

/// The mapped bytes: the code and the context.
pub open spec fn sa_mapped(a: int) -> bool {
    (4096 <= a < 4108) || (65536 <= a < 66048)
}

/// The byte at `a`.
pub open spec fn sa_byte(a: int) -> u8 {
    if 4096 <= a < 4108 {
        sa_blob()[a - 4096]
    } else {
        0u8
    }
}

/// The domain of the memory: the mapped bytes, as a finite set.
pub open spec fn sa_dom() -> Set<int> {
    Set::<int>::range(4096, 4108) + Set::<int>::range(65536, 66048)
}

/// The memory.
pub open spec fn sa_mem() -> Map<int, u8> {
    Map::new(sa_dom(), |a: int| sa_byte(a))
}

/// The domain is the mapped bytes.
pub proof fn lemma_sa_dom(a: int)
    ensures
        sa_dom().contains(a) == sa_mapped(a),
{
    vstd::set_lib::lemma_int_range(4096, 4108);
    vstd::set_lib::lemma_int_range(65536, 66048);
    assert(Set::<int>::range(4096, 4108) == vstd::set_lib::set_int_range(4096, 4108));
    assert(Set::<int>::range(65536, 66048) == vstd::set_lib::set_int_range(65536, 66048));
}

/// The state at entry: `x28` the context, `x30` the return address, `SP`,
/// the program counter at the entry.
pub open spec fn sa_state() -> State {
    State {
        r: Seq::new(31, |r: int| if r == 28 {
            65536u64
        } else if r == 30 {
            8u64
        } else {
            0u64
        }),
        sp: 131072,
        pc: 4096,
        flag_n: false,
        flag_z: false,
        flag_c: false,
        flag_v: false,
        vreg: Seq::new(32, |r: int| 0u128),
        mem: sa_mem(),
    }
}

/// Reading `n` bytes that are mapped and zero gives 0.
pub proof fn lemma_read_zero(m: Map<int, u8>, p: int, n: nat)
    requires
        0 <= p,
        p + n < p2(64),
        forall|x: int| p <= x < p + n ==> #[trigger] m.dom().contains(x),
        forall|x: int| p <= x < p + n ==> #[trigger] m[x] == 0u8,
    ensures
        mem_read(m, p, n) == Some(0int),
    decreases n,
{
    if n > 0 {
        lemma_trunc64_id(p);
        assert(m.dom().contains(p));
        assert(m[p] == 0u8);
        lemma_read_zero(m, p + 1, (n - 1) as nat);
    }
}

/// **The configuration is one the sandbox may hand over.**
pub proof fn example_cfg_ok()
    ensures
        cfg_ok(sa_cfg()),
{
    lemma_p2();
    crate::a64::examples::example_exit_accepted();
    crate::a64::examples::example_exit_valid();
    crate::a64::examples::example_bytes_decode();
    reveal(cfg_ok);
    let c = sa_cfg();
    assert(decodes_to(sa_blob(), sa_ins()));
    assert(policy(sa_ins(), seq![0int]));
    assert(sa_blob().len() == 12) by (compute_only);
    assert forall|k: int| 0 <= k < abi::num_regions() implies #[trigger] region_ok(c, k) by {
        assert(c.bases[k] == 0 && c.bounds[k] == 0);
    }
    assert(cfg_ok(c));
}

/// **The state at the entry satisfies the invariant.**
pub proof fn example_inv()
    ensures
        inv(sa_cfg(), sa_state()),
{
    lemma_p2();
    example_cfg_ok();
    let c = sa_cfg();
    let s = sa_state();
    let m = sa_mem();
    lemma_cfg(c);
    assert(wf(s)) by {
        assert forall|a: int| s.mem.dom().contains(a) implies 0 <= a < 0x100_0000_0000_0000 by {
            lemma_sa_dom(a);
            assert(sa_mapped(a));
        }
    }
    assert(s.r[28int] == 65536u64 && s.r[30int] == 8u64);
    lemma_xr(s, 28);
    lemma_xr(s, 30);
    assert forall|k: int| 0 <= k < abi::num_regions() implies mem_read(
        m,
        c.ctx + abi::base_off(k),
        8,
    ) == Some(c.bases[k]) && #[trigger] mem_read(m, c.ctx + abi::bound_off(k), 8) == Some(
        c.bounds[k],
    ) by {
        assert(c.bases[k] == 0 && c.bounds[k] == 0);
        let p1 = c.ctx + abi::base_off(k);
        let p2_ = c.ctx + abi::bound_off(k);
        assert forall|x: int| p1 <= x < p1 + 8 implies #[trigger] m.dom().contains(x) by {
            lemma_sa_dom(x);
        }
        assert forall|x: int| p1 <= x < p1 + 8 implies #[trigger] m[x] == 0u8 by {}
        assert forall|x: int| p2_ <= x < p2_ + 8 implies #[trigger] m.dom().contains(x) by {
            lemma_sa_dom(x);
        }
        assert forall|x: int| p2_ <= x < p2_ + 8 implies #[trigger] m[x] == 0u8 by {}
        lemma_read_zero(m, p1, 8);
        lemma_read_zero(m, p2_, 8);
    }
    assert forall|q: int| 0 <= q < c.blob.len() implies #[trigger] m.dom().contains(c.code + q)
        && m[c.code + q] == c.blob[q] by {
        lemma_sa_dom(c.code + q);
        assert(sa_mapped(c.code + q));
    }
    assert(base_inv(c, s));
    // The position: the first instruction of the exit sequence.
    reveal_with_fuel(chain_facts, 2);
    assert(start_facts(c, 0) == Some(no_facts()));
    assert(exit_unit_at(sa_ins(), 0)) by (compute_only);
    assert(unit_at(sa_ins(), 0, no_facts()) == Some(Unit { len: 3, facts: no_facts() }));
    assert(start_of(sa_ins(), 0) == 0);
    lemma_no_facts_hold(c, s);
    assert(pos_inv(c, s, 0, 0));
}

} // verus!
