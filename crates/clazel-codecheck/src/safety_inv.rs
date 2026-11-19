//! The machine-level invariant of the safety theorem ([`super::safety`]):
//! what the validator's register facts mean about a machine state, and the
//! preservation of the context invariant and of those facts by one ordinary
//! instruction.
//!
//! - [`holds`]: a register the scan calls [`Fact::Base`] holds that region's
//!   base address; one it calls [`Fact::Idx`] holds an index that, with `n`
//!   more bytes, still lies inside that region's bound.
//! - [`lemma_access_allowed`]: a permitted access ([`access_ok`]) under
//!   [`holds`] is inside the context or a handed region.
//! - [`lemma_ctx_inv_preserved`]: a step that stores only inside what
//!   [`access_allowed`] allows keeps the context invariant (the table and the
//!   code are not written).
//! - [`lemma_plain_step`]: one instruction the scan takes alone is safe, keeps
//!   the invariant and keeps the facts the scan derives for what follows.

#[allow(unused_imports)]
use super::safety::*;
#[allow(unused_imports)]
use super::safety_sem::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the fact `f` about register `r` says of the state.
pub open spec fn fact_holds(s: State, h: Handed, r: u8, f: Fact) -> bool {
    match f {
        Fact::Unknown => true,
        Fact::Base(k) => 0 <= k < 16 && s.rgf[r as int] as int == h.rg[k].base,
        Fact::Idx(k, n) => 0 <= k < 16 && s.rgf[r as int] as int + n <= h.rg[k].bound,
    }
}

/// Every fact in `fs` is true of `s`.
pub open spec fn holds(s: State, h: Handed, fs: Facts) -> bool {
    forall|r: u8| r < 16 ==> fact_holds(s, h, r, #[trigger] fact_of(fs, r))
}

/// Nothing is known of any register, in `no_facts()`.
pub proof fn lemma_no_facts_hold(s: State, h: Handed)
    ensures
        holds(s, h, no_facts()),
{
    assert forall|r: u8| r < 16 implies fact_holds(s, h, r, #[trigger] fact_of(no_facts(), r)) by {
        assert(fact_of(no_facts(), r) == Fact::Unknown);
    }
}

/// The latest binding of `set_fact`.
pub proof fn lemma_fact_of_set(fs: Facts, d: u8, f: Fact, r: u8)
    ensures
        fact_of(set_fact(fs, d, f), r) == if r == d {
            f
        } else {
            fact_of(fs, r)
        },
{
    let b = Binding { reg: d, fact: f };
    let fs2 = fs.push(b);
    assert(fs2.last() == b);
    assert(fs2.drop_last() =~= fs);
}

/// A write to `d` only, after which `d`'s fact is `f`, keeps the other facts.
pub proof fn lemma_holds_set(s: State, s2: State, h: Handed, fs: Facts, d: u8, f: Fact)
    requires
        holds(s, h, fs),
        d < 16,
        s.rgf.len() == 16,
        gpr_kept(s, s2, Some(d)),
        fact_holds(s2, h, d, f),
    ensures
        holds(s2, h, set_fact(fs, d, f)),
{
    assert forall|r: u8| r < 16 implies fact_holds(
        s2,
        h,
        r,
        #[trigger] fact_of(set_fact(fs, d, f), r),
    ) by {
        lemma_fact_of_set(fs, d, f, r);
        if r != d {
            assert(fact_holds(s, h, r, fact_of(fs, r)));
        }
    }
}

/// No write to a general register keeps every fact.
pub proof fn lemma_holds_kept(s: State, s2: State, h: Handed, fs: Facts)
    requires
        holds(s, h, fs),
        s.rgf.len() == 16,
        gpr_kept(s, s2, None),
    ensures
        holds(s2, h, fs),
{
    assert forall|r: u8| r < 16 implies fact_holds(s2, h, r, #[trigger] fact_of(fs, r)) by {
        assert(fact_holds(s, h, r, fact_of(fs, r)));
    }
}

/// `logext` of an address below 2^63 is itself.
pub proof fn lemma_logext_small(x: int)
    requires
        0 <= x < 0x8000_0000_0000_0000,
    ensures
        logext(64, x) == x,
{
    lemma_p2_vals();
}

/// The sizes of memory accesses are 4 or 8 bytes, and their operands valid.
pub proof fn lemma_mem_access_valid(i: Instr)
    requires
        valid_instr(i),
    ensures
        mem_access(i) matches Some(a) ==> mem_ok(a.mem) && (a.size == 4 || a.size == 8),
{
    match i {
        Instr::MovLoad { sz, dst, mem } => {},
        Instr::MovStore { sz, mem, src } => {},
        Instr::AluRM { alu, sz, dst, mem } => {},
        Instr::FpArith { fop, dst, xsrc } => {},
        Instr::Sqrtsd { dst, xsrc } => {},
        Instr::Ucomisd { a, xsrc } => {},
        Instr::MovsdLoad { dst, mem } => {},
        Instr::MovsdStore { mem, src } => {},
        _ => {},
    }
}

/// **A permitted access is allowed**: if the scan permits `a` given facts
/// that hold, the bytes `eff_addr` addresses lie in the context (loads), the
/// exit area (stores) or a handed region.
pub proof fn lemma_access_allowed(s: State, h: Handed, fs: Facts, a: Access)
    requires
        handed_ok(h),
        s.rgf.len() == 16,
        s.rgf[15] as int == h.ctx,
        holds(s, h, fs),
        access_ok(fs, a),
        mem_ok(a.mem),
        1 <= a.size,
    ensures
        access_allowed(h, eff_addr(s, a.mem), a),
{
    lemma_p2_vals();
    if a.mem.base == abi::ctx_reg() {
        assert(rr64(s, 15) == h.ctx);
        let x = h.ctx + a.mem.disp as int;
        assert(eff_addr(s, a.mem) == logext(64, x));
        assert(0 <= x < 0x8000_0000_0000_0000) by {
            lemma_p2_vals();
        }
        lemma_logext_small(x);
    } else {
        let ix = a.mem.index->Some_0;
        let b = a.mem.base;
        assert(b < 16 && ix.reg < 16);
        assert(fact_holds(s, h, b, fact_of(fs, b)));
        assert(fact_holds(s, h, ix.reg, fact_of(fs, ix.reg)));
        let k = match fact_of(fs, b) {
            Fact::Base(k) => k,
            _ => 0,
        };
        assert(0 <= k < 16);
        assert(region_ok(h, h.rg[k]));
        let x = rr64(s, b) + rr64(s, ix.reg) * p2(ix.scale as nat) + a.mem.disp as int;
        assert(ix.scale == 0);
        assert(x == h.rg[k].base + rr64(s, ix.reg));
        assert(0 <= x < 0x8000_0000_0000_0000) by {
            lemma_p2_vals();
        }
        lemma_logext_small(x);
        assert(within(eff_addr(s, a.mem), a.size, h.rg[k].base, h.rg[k].bound));
    }
}

/// A store that is allowed lies in the exit area or a region, so it shares no
/// byte with the region table or the code.
pub proof fn lemma_store_disjoint(h: Handed, addr: int, a: Access)
    requires
        handed_ok(h),
        a.store,
        0 <= a.size,
        access_allowed(h, addr, a),
    ensures
        disjoint(addr, a.size, h.ctx, abi::table_end()),
        disjoint(addr, a.size, h.code, h.len),
{
    if exists|k: int| 0 <= k < 16 && within(addr, a.size, (#[trigger] h.rg[k]).base, h.rg[k].bound) {
        let k = choose|k: int|
            0 <= k < 16 && within(addr, a.size, (#[trigger] h.rg[k]).base, h.rg[k].bound);
        assert(region_ok(h, h.rg[k]));
    }
}

/// A read of bytes a store did not touch gives the same value.
pub proof fn lemma_read_untouched(
    m: Map<int, u8>,
    m2: Map<int, u8>,
    lo: int,
    n: int,
    a: int,
    cnt: nat,
)
    requires
        mem_frame(m, m2, lo, n),
        a + cnt <= lo || lo + n <= a,
    ensures
        read_mem(m2, a, cnt) == read_mem(m, a, cnt),
{
    assert forall|i: int| #![trigger m2.dom().contains(a + i)]
        0 <= i < cnt implies (m.dom().contains(a + i) == m2.dom().contains(a + i)) && (
    m.dom().contains(a + i) ==> m2[a + i] == m[a + i]) by {
        assert(m2.dom().contains(a + i) == m.dom().contains(a + i));
    }
    lemma_read_mem_frame(m, m2, a, cnt);
}

/// **The context invariant survives a step** that keeps `r15` and `rsp` and
/// whose store, if any, is allowed.
pub proof fn lemma_ctx_inv_preserved(h: Handed, blob: Seq<u8>, s: State, s2: State, i: Instr)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        valid_instr(i),
        s2.rgf.len() == 16,
        s2.rgf[15] == s.rgf[15],
        s2.rgf[4] == s.rgf[4],
        match mem_access(i) {
            Some(a) => if a.store {
                access_allowed(h, eff_addr(s, a.mem), a) && mem_frame(
                    s.mem,
                    s2.mem,
                    eff_addr(s, a.mem),
                    a.size,
                )
            } else {
                s2.mem == s.mem
            },
            None => s2.mem == s.mem,
        },
    ensures
        ctx_inv(s2, h, blob),
{
    lemma_mem_access_valid(i);
    if mem_access(i) is Some && mem_access(i)->Some_0.store {
        let a = mem_access(i)->Some_0;
        let addr = eff_addr(s, a.mem);
        lemma_store_disjoint(h, addr, a);
        assert forall|k: int| 0 <= k < 16 implies read_mem(
            s2.mem,
            h.ctx + abi::base_off(k),
            8,
        ) == read_mem(s.mem, h.ctx + abi::base_off(k), 8) && read_mem(
            s2.mem,
            h.ctx + abi::bound_off(k),
            8,
        ) == read_mem(s.mem, h.ctx + abi::bound_off(k), 8) by {
            lemma_read_untouched(s.mem, s2.mem, addr, a.size, h.ctx + abi::base_off(k), 8);
            lemma_read_untouched(s.mem, s2.mem, addr, a.size, h.ctx + abi::bound_off(k), 8);
        }
        assert forall|j: int| 0 <= j < h.len implies s2.mem.dom().contains(h.code + j)
            && s2.mem[h.code + j] == blob[j] by {
            assert(s.mem.dom().contains(h.code + j));
            assert(s2.mem[h.code + j] == s.mem[h.code + j]);
        }
    }
}

/// Facts about the base-load of a region's base: the loaded register holds
/// the base.
proof fn lemma_base_load(
    u: spec_fn(nat) -> nat,
    h: Handed,
    blob: Seq<u8>,
    s: State,
    s2: State,
    i: Instr,
    k: int,
)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        valid_instr(i),
        step(u, s, i) == Some(s2),
        base_load_region(i) == Some(k),
    ensures
        0 <= k < 16,
        s2.rgf[i->MovLoad_dst as int] as int == h.rg[k].base,
{
    lemma_p2_vals();
    let mem = i->MovLoad_mem;
    let d = i->MovLoad_dst;
    assert(mem.disp % 16 == 0 && 0 <= mem.disp < 256);
    assert(k == mem.disp as int / 16);
    assert(mem.disp as int == 16 * k);
    assert(rr64(s, 15) == h.ctx);
    let x = h.ctx + mem.disp as int;
    lemma_logext_small(x);
    assert(eff_addr(s, mem) == x);
    assert(abi::base_off(k) == mem.disp as int);
    let s1 = effect(u, s, i)->Some_0;
    let v = read_operand_mem(s, Size::W64, mem)->Some_0;
    assert(v == h.rg[k].base);
    assert(region_ok(h, h.rg[k]));
    lemma_p2_vals();
    assert(s1 == wr64(s, d, v));
    assert(loghead(64, v) == v);
}

/// **One plain instruction**: if the scan takes `i` alone (`plain_ok`), at a
/// state where its facts hold, then the step is safe, the context invariant
/// holds after it, and the facts the scan derives hold after it. `rip` moves
/// to the next instruction, except for a jump.
pub proof fn lemma_plain_step(
    u: spec_fn(nat) -> nat,
    h: Handed,
    blob: Seq<u8>,
    s: State,
    s2: State,
    i: Instr,
    fs: Facts,
    fs2: Facts,
)
    requires
        handed_ok(h),
        ctx_inv(s, h, blob),
        valid_instr(i),
        holds(s, h, fs),
        plain_ok(fs, i) == Some(fs2),
        step(u, s, i) == Some(s2),
    ensures
        ctx_inv(s2, h, blob),
        step_safe(h, s, i, s2),
        holds(s2, h, fs2),
        !(i is Jcc) && !(i is Jmp) ==> s2.rip == s.rip + instr_len(i),
        i is Jmp ==> s2.rip == s.rip + instr_len(i) + i->Jmp_rel,
        i is Jcc ==> s2.rip == if jcc_cmovcc_setcc_spec(s, i->Jcc_cc) {
            s.rip + instr_len(i) + i->Jcc_rel
        } else {
            s.rip + instr_len(i)
        },
        s2.rgf.len() == 16,
{
    super::lemmas::lemma_plain_ok_safe(fs, i);
    assert(!(i is Ret));
    lemma_step_frame(u, s, i, s2);
    lemma_mem_access_valid(i);
    assert(s2.rgf[15] == s.rgf[15]);
    assert(s2.rgf[4] == s.rgf[4]);
    if mem_access(i) is Some {
        let a = mem_access(i)->Some_0;
        lemma_access_allowed(s, h, fs, a);
    }
    lemma_ctx_inv_preserved(h, blob, s, s2, i);
    if i is Jmp {
        lemma_no_facts_hold(s2, h);
    } else {
        match written_gpr(i) {
            None => {
                assert(fs2 == fs);
                lemma_holds_kept(s, s2, h, fs);
            },
            Some(d) => {
                assert(d < 16);
                match base_load_region(i) {
                    Some(k) => {
                        lemma_base_load(u, h, blob, s, s2, i, k);
                        lemma_holds_set(s, s2, h, fs, d, Fact::Base(k));
                    },
                    None => {
                        lemma_holds_set(s, s2, h, fs, d, Fact::Unknown);
                    },
                }
            },
        }
    }
}

} // verus!
