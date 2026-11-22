//! **Infrastructure of the confinement proof**: the memory part of the
//! invariant and how stores and register writes keep it, the scan's facts
//! under register writes, a summary of a straight-line step, the safety of a
//! permitted access, and the instruction the invariant puts at RIP.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ----------------------------------------------------------------------------
// Section: the memory part of the invariant
// ----------------------------------------------------------------------------

/// The memory part of [`base_inv`]: the region table, the code and the stub's
/// return slot are as configured.
pub open spec fn mem_inv(c: Cfg, m: Map<int, u8>) -> bool {
    (forall|k: int|
        0 <= k < abi::num_regions() ==> read_mem(m, c.ctx + abi::base_off(k), 8) == Some(
            c.bases[k],
        ) && #[trigger] read_mem(m, c.ctx + abi::bound_off(k), 8) == Some(c.bounds[k]))
        && (forall|q: int|
        0 <= q < c.blob.len() ==> #[trigger] m.dom().contains(c.code + q) && m[c.code + q]
            == c.blob[q]) && read_mem(m, c.sp, 8) == Some(c.ret_raw)
}

/// The register part of [`base_inv`].
pub open spec fn regs_inv(c: Cfg, s: State) -> bool {
    wf(s) && rr64(s, abi::ctx_reg()) == c.ctx && rr64(s, abi::sp_reg()) == c.sp
}

/// [`base_inv`] is the register part and the memory part.
pub proof fn lemma_base_inv_split(c: Cfg, s: State)
    ensures
        base_inv(c, s) == (regs_inv(c, s) && mem_inv(c, s.mem)),
{
}

/// Region `k` of a configuration is well placed.
pub proof fn lemma_region(c: Cfg, k: int)
    requires
        cfg_ok(c),
        0 <= k < abi::num_regions(),
    ensures
        region_ok(c, k),
        0 <= c.bases[k],
        0 <= c.bounds[k],
        c.bases[k] + c.bounds[k] <= lim(),
        disjoint(c.bases[k], c.bounds[k], c.code, c.blob.len() as int),
        disjoint(c.bases[k], c.bounds[k], c.ctx, 256),
        disjoint(c.bases[k], c.bounds[k], c.sp, 8),
{
}

/// A write that is `writable` is disjoint from the table, the code and the
/// stub's slot.
pub proof fn lemma_writable_disjoint(c: Cfg, addr: int, size: int)
    requires
        cfg_ok(c),
        size >= 0,
        writable(c, addr, size),
    ensures
        disjoint(addr, size, c.ctx, 256),
        disjoint(addr, size, c.code, c.blob.len() as int),
        disjoint(addr, size, c.sp, 8),
{
    if c.ctx + 256 <= addr && addr + size <= c.ctx + 512 {
        assert(disjoint(c.code, c.blob.len() as int, c.ctx, abi::ctx_size()));
        assert(disjoint(c.sp, 8, c.ctx, abi::ctx_size()));
    } else {
        let k = choose|k: int|
            0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + size <= c.bases[k]
                + c.bounds[k];
        lemma_region(c, k);
    }
}

/// A store to writable bytes keeps the memory invariant.
pub proof fn lemma_mem_inv_store(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>, addr: int, size: int)
    requires
        cfg_ok(c),
        mem_inv(c, m),
        size >= 0,
        writable(c, addr, size),
        m2.dom() =~= m.dom(),
        forall|x: int| (x < addr || x >= addr + size) && m.dom().contains(x) ==> #[trigger] m2[x] == m[x],
    ensures
        mem_inv(c, m2),
{
    lemma_writable_disjoint(c, addr, size);
    assert forall|k: int| 0 <= k < abi::num_regions() implies read_mem(
        m2,
        c.ctx + abi::base_off(k),
        8,
    ) == Some(c.bases[k]) && #[trigger] read_mem(m2, c.ctx + abi::bound_off(k), 8) == Some(
        c.bounds[k],
    ) by {
        let p1 = c.ctx + abi::base_off(k);
        let p2_ = c.ctx + abi::bound_off(k);
        assert(same_on(m, m2, p1, 8)) by {
            assert forall|x: int| p1 <= x < p1 + 8 implies (#[trigger] m2.dom().contains(x)
                == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
                assert(x < addr || x >= addr + size);
            }
        }
        assert(same_on(m, m2, p2_, 8)) by {
            assert forall|x: int| p2_ <= x < p2_ + 8 implies (#[trigger] m2.dom().contains(x)
                == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
                assert(x < addr || x >= addr + size);
            }
        }
        lemma_read_mem_same(m, m2, p1, 8);
        lemma_read_mem_same(m, m2, p2_, 8);
    }
    assert forall|q: int| 0 <= q < c.blob.len() implies #[trigger] m2.dom().contains(c.code + q)
        && m2[c.code + q] == c.blob[q] by {
        assert(m.dom().contains(c.code + q));
        assert(c.code + q < addr || c.code + q >= addr + size);
    }
    assert(same_on(m, m2, c.sp, 8)) by {
        assert forall|x: int| c.sp <= x < c.sp + 8 implies (#[trigger] m2.dom().contains(x)
            == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
            assert(x < addr || x >= addr + size);
        }
    }
    lemma_read_mem_same(m, m2, c.sp, 8);
}

/// **A register write that is not to a reserved register, with RIP moved
/// canonically, and memory kept**, keeps [`base_inv`].
pub proof fn lemma_base_inv_after(c: Cfg, s: State, s2: State, d: Option<u8>)
    requires
        cfg_ok(c),
        base_inv(c, s),
        s2.rgf.len() == s.rgf.len(),
        s2.xmm.len() == s.xmm.len(),
        canonical(s2.rip),
        forall|r: int| 0 <= r < s.rgf.len() && d != Some(r as u8) ==> #[trigger] s2.rgf[r] == s.rgf[r],
        d is None || !abi::reserved(d->Some_0),
        mem_inv(c, s2.mem),
        s2.mem.dom() =~= s.mem.dom(),
    ensures
        base_inv(c, s2),
{
    lemma_base_inv_split(c, s);
    lemma_base_inv_split(c, s2);
    assert(wf(s2)) by {
        assert forall|a: int| s2.mem.dom().contains(a) implies #[trigger] canonical(a) by {
            assert(s.mem.dom().contains(a));
        }
    }
    assert(rr64(s2, abi::ctx_reg()) == rr64(s, abi::ctx_reg()));
    assert(rr64(s2, abi::sp_reg()) == rr64(s, abi::sp_reg()));
}

// ----------------------------------------------------------------------------
// Section: the scan's facts under register writes
// ----------------------------------------------------------------------------

/// A write to a register whose fact is `Unknown` (or to none) keeps the facts.
pub proof fn lemma_facts_keep(c: Cfg, s: State, s2: State, fs: Facts, d: Option<u8>)
    requires
        facts_hold(c, s, fs),
        s.rgf.len() == 16,
        s2.rgf.len() == 16,
        forall|r: int| 0 <= r < 16 && d != Some(r as u8) ==> #[trigger] s2.rgf[r] == s.rgf[r],
        d is None || fact_of(fs, d->Some_0) is Unknown,
    ensures
        facts_hold(c, s2, fs),
{
    assert forall|r: u8| r < 16 implies match #[trigger] fact_of(fs, r) {
        Fact::Unknown => true,
        Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s2, r) == c.bases[k],
        Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s2, r) + n <= c.bounds[k],
    } by {
        assert(d != Some(r as int as u8) || fact_of(fs, r) is Unknown);
        if fact_of(fs, r) is Unknown {
        } else {
            assert(d != Some(r));
            assert(s2.rgf[r as int] == s.rgf[r as int]);
        }
    }
}

/// A write to register `d` that makes its fact `f` (which holds in `s2`)
/// gives the facts with `d` bound to `f`.
pub proof fn lemma_facts_set(c: Cfg, s: State, s2: State, fs: Facts, d: u8, f: Fact)
    requires
        facts_hold(c, s, fs),
        s.rgf.len() == 16,
        s2.rgf.len() == 16,
        forall|r: int| 0 <= r < 16 && Some(r as u8) != Some(d) ==> #[trigger] s2.rgf[r] == s.rgf[r],
        d < 16,
        match f {
            Fact::Unknown => true,
            Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s2, d) == c.bases[k],
            Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s2, d) + n
                <= c.bounds[k],
        },
    ensures
        facts_hold(c, s2, set_fact(fs, d, f)),
{
    assert forall|r: u8| r < 16 implies match #[trigger] fact_of(set_fact(fs, d, f), r) {
        Fact::Unknown => true,
        Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s2, r) == c.bases[k],
        Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s2, r) + n <= c.bounds[k],
    } by {
        crate::unit_exec::lemma_fact_of_set(fs, d, f, r);
        if r != d {
            assert(s2.rgf[r as int] == s.rgf[r as int]);
        }
    }
}

// ----------------------------------------------------------------------------
// Section: a straight-line step
// ----------------------------------------------------------------------------

/// The summary of a successful step of an instruction that is not a jump or
/// `ret`: RIP moves to the next instruction (canonically), the destination
/// register is the only one written, and memory is kept except for the bytes
/// of a store.
pub proof fn lemma_step_straight(cu: spec_fn(nat) -> nat, s: State, i: Instr, s2: State)
    requires
        step(cu, s, i) == Some(s2),
        !(i is Jcc),
        !(i is Jmp),
        !(i is Ret),
    ensures
        effect(cu, s, i) is Some,
        s2 == write_ip(effect(cu, s, i)->Some_0, s.rip + instr_len(i) as int),
        s2.rip == s.rip + instr_len(i) as int,
        canonical(s2.rip),
        effect_regs_frame(State { rip: s.rip + instr_len(i) as int, ..s }, s2, written_gpr(i)),
        match mem_access(i) {
            Some(a) => if a.store {
                store_frame(s, s2, eff_addr(s, a.mem), a.size)
            } else {
                s2.mem == s.mem
            },
            None => s2.mem == s.mem,
        },
{
    lemma_effect_frame(cu, s, i);
    let s1 = effect(cu, s, i)->Some_0;
    assert(s2 == write_ip(s1, s.rip + instr_len(i)));
}

// ----------------------------------------------------------------------------
// Section: the safety of a permitted access
// ----------------------------------------------------------------------------

/// A valid memory operand names registers below 16 and no `rsp` index.
pub proof fn lemma_access_regs(i: Instr)
    requires
        valid_instr(i),
        mem_access(i) is Some,
    ensures
        mem_ok(mem_access(i)->Some_0.mem),
{
}

/// **A permitted access is in bounds**: if the scan permits an access given
/// facts that hold, the bytes it touches are in the context (a load), in the
/// context's exit area (a store), or in a handed region.
pub proof fn lemma_access_safe(c: Cfg, s: State, fs: Facts, a: Access)
    requires
        cfg_ok(c),
        regs_inv(c, s),
        facts_hold(c, s, fs),
        access_ok(fs, a),
        mem_ok(a.mem),
        0 < a.size <= abi::max_access(),
    ensures
        readable(c, eff_addr(s, a.mem), a.size),
        a.store ==> writable(c, eff_addr(s, a.mem), a.size),
{
    lemma_p2();
    if a.mem.base == abi::ctx_reg() {
        assert(a.mem.index is None);
        let addr = c.ctx + a.mem.disp as int;
        assert(eff_addr(s, a.mem) == logext(64, rr64(s, a.mem.base) + 0 + a.mem.disp as int));
        lemma_logext64_id(addr);
        assert(eff_addr(s, a.mem) == addr);
    } else {
        let ix = a.mem.index->Some_0;
        assert(ix.scale == 0 && a.mem.disp == 0);
        let r1 = a.mem.base;
        let r2 = ix.reg;
        assert(r1 < 16 && r2 < 16);
        match (fact_of(fs, r1), fact_of(fs, r2)) {
            (Fact::Base(k), Fact::Idx(k2, n)) => {
                lemma_region(c, k);
                let b = rr64(s, r1);
                let i = rr64(s, r2);
                assert(b == c.bases[k]);
                assert(i + n <= c.bounds[k]);
                assert(eff_addr(s, a.mem) == logext(64, b + i * p2(0) + 0));
                assert(p2(0) == 1);
                lemma_logext64_id(b + i);
                assert(eff_addr(s, a.mem) == b + i);
                assert(in_region(c, eff_addr(s, a.mem), a.size));
            },
            _ => {},
        }
    }
}

// ----------------------------------------------------------------------------
// Section: the instruction at RIP
// ----------------------------------------------------------------------------

/// `enc_all` has the encoding of each instruction at its start.
pub proof fn lemma_blob_byte(c: Cfg, j: int, k: int)
    requires
        cfg_ok(c),
        0 <= j < c.ins.len(),
        0 <= k < instr_len(c.ins[j]),
    ensures
        0 <= start_of(c.ins, j) + k < c.blob.len(),
        c.blob[start_of(c.ins, j) + k] == encode(c.ins[j])[k],
{
    crate::uniq::lemma_enc_all_index(c.ins, j);
    assert(c.blob == enc_all(c.ins));
    let a = start_of(c.ins, j);
    let e = encode(c.ins[j]);
    crate::validate::lemma_start_of_ge(c.ins, j);
    assert(e.len() == instr_len(c.ins[j]));
    assert(a + e.len() <= enc_all(c.ins).len());
    assert(0 <= k < e.len());
    assert(enc_all(c.ins).subrange(a, a + e.len())[k] == e[k]);
    assert(enc_all(c.ins).subrange(a, a + e.len())[k] == enc_all(c.ins)[a + k]);
}

/// **The invariant puts the instruction `ins[j0 + m]` at RIP**: it is the next
/// instruction, it is valid, and its bytes are in memory.
pub proof fn lemma_cur_instr(c: Cfg, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
    ensures
        0 <= j0 + m < c.ins.len(),
        next_instr(c, s) == Some(c.ins[j0 + m]),
        fetch_ok(s, c.ins[j0 + m]),
        valid_instr(c.ins[j0 + m]),
{
    let fs0 = start_facts(c, j0)->Some_0;
    let u = unit_at(c.ins, j0, fs0)->Some_0;
    let j = j0 + m;
    assert(j < c.ins.len());
    assert(s.rip - c.code == start_of(c.ins, j));
    assert(exists|jj: int| 0 <= jj < c.ins.len() && start_of(c.ins, jj) == s.rip - c.code);
    let jj = choose|jj: int| 0 <= jj < c.ins.len() && start_of(c.ins, jj) == s.rip - c.code;
    lemma_start_unique(c.ins, jj, j);
    assert(index_at(c, s) == Some(j));
    assert(all_valid(c.ins));
    assert(valid_instr(c.ins[j]));
    assert forall|k: int| 0 <= k < instr_len(c.ins[j]) implies #[trigger] s.mem.dom().contains(
        s.rip + k,
    ) && s.mem[s.rip + k] == encode(c.ins[j])[k] by {
        lemma_blob_byte(c, j, k);
        assert(base_inv(c, s));
        assert(s.mem.dom().contains(c.code + (start_of(c.ins, j) + k)));
    }
}

} // verus!
