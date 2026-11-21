//! **The hypotheses of the theorem are satisfiable**: a concrete
//! configuration ([`sx_cfg`], the exit sequence `mov eax, 7; mov [r15 + 256],
//! rax; ret`, entered at 0, with 16 empty regions) that passes [`cfg_ok`], and
//! a concrete state ([`sx_state`]) that satisfies [`inv`] at its entry. A
//! theorem whose hypotheses nothing satisfies would say nothing; this is the
//! check that it does.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exit sequence's instructions.
pub open spec fn sx_ins() -> Seq<Instr> {
    crate::examples::exit_seq(0, 7)
}

/// Its bytes: `mov eax, 7`, `mov [r15 + 256], rax`, `ret`.
pub open spec fn sx_blob() -> Seq<u8> {
    seq![0xB8u8, 0x07, 0x00, 0x00, 0x00, 0x49, 0x89, 0x84, 0x27, 0x00, 0x01, 0x00, 0x00, 0xC3]
}

/// The configuration: code at 4096, the context at 65536, the stub's slot at
/// 131072 holding the return address 8, sixteen empty regions at address 0.
pub open spec fn sx_cfg() -> Cfg {
    Cfg {
        blob: sx_blob(),
        ins: sx_ins(),
        entries: seq![0int],
        code: 4096,
        ctx: 65536,
        bases: Seq::new(16, |k: int| 0int),
        bounds: Seq::new(16, |k: int| 0int),
        sp: 131072,
        ret_raw: 8,
    }
}

/// The mapped bytes: the code, the context, the stub's slot.
pub open spec fn sx_mapped(a: int) -> bool {
    (4096 <= a < 4110) || (65536 <= a < 66048) || (131072 <= a < 131080)
}

/// The byte at `a`.
pub open spec fn sx_byte(a: int) -> u8 {
    if 4096 <= a < 4110 {
        sx_blob()[a - 4096]
    } else if a == 131072 {
        8u8
    } else {
        0u8
    }
}

/// The domain of the memory: the mapped bytes, as a finite set.
pub open spec fn sx_dom() -> Set<int> {
    Set::<int>::range(4096, 4110) + Set::<int>::range(65536, 66048) + Set::<int>::range(
        131072,
        131080,
    )
}

/// The memory.
pub open spec fn sx_mem() -> Map<int, u8> {
    Map::new(sx_dom(), |a: int| sx_byte(a))
}

/// The domain is the mapped bytes.
pub proof fn lemma_sx_dom(a: int)
    ensures
        sx_dom().contains(a) == sx_mapped(a),
{
    vstd::set_lib::lemma_int_range(4096, 4110);
    vstd::set_lib::lemma_int_range(65536, 66048);
    vstd::set_lib::lemma_int_range(131072, 131080);
    assert(Set::<int>::range(4096, 4110) == vstd::set_lib::set_int_range(4096, 4110));
    assert(Set::<int>::range(65536, 66048) == vstd::set_lib::set_int_range(65536, 66048));
    assert(Set::<int>::range(131072, 131080) == vstd::set_lib::set_int_range(131072, 131080));
}

/// The state at entry: `r15` the context, `rsp` the slot, RIP at the entry.
pub open spec fn sx_state() -> State {
    State {
        rgf: Seq::new(16, |r: int| if r == 15 {
            65536u64
        } else if r == 4 {
            131072u64
        } else {
            0u64
        }),
        rip: 4096,
        rflags: 2,
        undef: 0,
        xmm: Seq::new(16, |r: int| 0u128),
        mem: sx_mem(),
    }
}

/// Reading `n` bytes that are mapped and zero gives 0.
pub proof fn lemma_read_zero(m: Map<int, u8>, p: int, n: nat)
    requires
        forall|x: int| p <= x < p + n ==> #[trigger] m.dom().contains(x),
        forall|x: int| p <= x < p + n ==> #[trigger] m[x] == 0u8,
    ensures
        read_mem(m, p, n) == Some(0int),
    decreases n,
{
    if n > 0 {
        assert(m.dom().contains(p));
        assert(m[p] == 0u8);
        lemma_read_zero(m, p + 1, (n - 1) as nat);
    }
}

/// **The configuration is one the sandbox may hand over.**
pub proof fn example_cfg_ok()
    ensures
        cfg_ok(sx_cfg()),
{
    lemma_p2();
    crate::examples::example_exit_accepted();
    crate::examples::example_exit_valid();
    crate::examples::example_bytes_decode();
    reveal_with_fuel(le_bytes, 5);
    reveal_with_fuel(enc_all, 4);
    let c = sx_cfg();
    assert(enc_all(sx_ins()) =~= sx_blob());
    assert(decodes_to(sx_blob(), sx_ins()));
    assert(policy(sx_ins(), seq![0int]));
    assert(sx_blob().len() == 14);
    lemma_logext64_id(8);
    assert forall|k: int| 0 <= k < abi::num_regions() implies #[trigger] region_ok(c, k) by {
        assert(c.bases[k] == 0 && c.bounds[k] == 0);
    }
    assert(cfg_ok(c));
}

/// **The state at the entry satisfies the invariant.**
pub proof fn example_inv()
    ensures
        inv(sx_cfg(), sx_state()),
{
    lemma_p2();
    example_cfg_ok();
    let c = sx_cfg();
    let s = sx_state();
    let m = sx_mem();
    assert(wf(s)) by {
        assert forall|a: int| s.mem.dom().contains(a) implies #[trigger] canonical(a) by {
            lemma_sx_dom(a);
            assert(sx_mapped(a));
        }
    }
    assert(rr64(s, 15) == 65536 && rr64(s, 4) == 131072);
    assert forall|k: int| 0 <= k < abi::num_regions() implies read_mem(
        m,
        c.ctx + abi::base_off(k),
        8,
    ) == Some(c.bases[k]) && #[trigger] read_mem(m, c.ctx + abi::bound_off(k), 8) == Some(
        c.bounds[k],
    ) by {
        assert(c.bases[k] == 0 && c.bounds[k] == 0);
        let p1 = c.ctx + abi::base_off(k);
        let p2_ = c.ctx + abi::bound_off(k);
        assert forall|x: int| p1 <= x < p1 + 8 implies #[trigger] m.dom().contains(x) by {
            lemma_sx_dom(x);
        }
        assert forall|x: int| p1 <= x < p1 + 8 implies #[trigger] m[x] == 0u8 by {}
        assert forall|x: int| p2_ <= x < p2_ + 8 implies #[trigger] m.dom().contains(x) by {
            lemma_sx_dom(x);
        }
        assert forall|x: int| p2_ <= x < p2_ + 8 implies #[trigger] m[x] == 0u8 by {}
        lemma_read_zero(m, p1, 8);
        lemma_read_zero(m, p2_, 8);
    }
    assert forall|q: int| 0 <= q < c.blob.len() implies #[trigger] m.dom().contains(c.code + q)
        && m[c.code + q] == c.blob[q] by {
        lemma_sx_dom(c.code + q);
        assert(sx_mapped(c.code + q));
    }
    reveal_with_fuel(read_mem, 9);
    assert(read_mem(m, c.sp, 8) == Some(8int));
    assert(base_inv(c, s));
    // The position: the first instruction of the exit sequence.
    reveal_with_fuel(chain_facts, 2);
    assert(start_facts(c, 0) == Some(no_facts()));
    assert(exit_unit_at(sx_ins(), 0)) by (compute_only);
    assert(unit_at(sx_ins(), 0, no_facts()) == Some(Unit { len: 3, facts: no_facts() }));
    assert(start_of(sx_ins(), 0) == 0);
    crate::confine::pos::lemma_no_facts_hold(c, s);
    assert(pos_inv(c, s, 0, 0));
}

} // verus!
