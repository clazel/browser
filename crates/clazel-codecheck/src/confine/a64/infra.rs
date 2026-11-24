//! **Infrastructure of the A64 confinement proof**: the memory part of the
//! invariant and how stores and register writes keep it, the scan's facts
//! under register writes, the safety of a permitted access, the instruction
//! the invariant puts at the program counter, and the construction of the
//! invariant at the next position of a step.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ----------------------------------------------------------------------------
// Section: the memory part of the invariant
// ----------------------------------------------------------------------------

/// The memory part of [`base_inv`]: the region table and the code are as
/// configured.
pub open spec fn mem_inv(c: Cfg, m: Map<int, u8>) -> bool {
    (forall|k: int|
        0 <= k < abi::num_regions() ==> mem_read(m, c.ctx + abi::base_off(k), 8) == Some(
            c.bases[k],
        ) && #[trigger] mem_read(m, c.ctx + abi::bound_off(k), 8) == Some(c.bounds[k]))
        && (forall|q: int|
        0 <= q < c.blob.len() ==> #[trigger] m.dom().contains(c.code + q) && m[c.code + q]
            == c.blob[q])
}

/// The register part of [`base_inv`].
pub open spec fn regs_inv(c: Cfg, s: State) -> bool {
    wf(s) && x_read(s, abi::ctx_reg(), 64) == c.ctx && x_read(s, abi::link_reg(), 64) == c.lr
        && s.sp as int == c.sp
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
{
    lemma_cfg(c);
}

/// A write that is `writable` is disjoint from the table and the code.
pub proof fn lemma_writable_disjoint(c: Cfg, addr: int, size: int)
    requires
        cfg_ok(c),
        size >= 0,
        writable(c, addr, size),
    ensures
        disjoint(addr, size, c.ctx, 256),
        disjoint(addr, size, c.code, c.blob.len() as int),
{
    lemma_cfg(c);
    if c.ctx + 256 <= addr && addr + size <= c.ctx + 512 {
        assert(disjoint(c.code, c.blob.len() as int, c.ctx, abi::ctx_size()));
    } else {
        let k = choose|k: int|
            0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + size <= c.bases[k]
                + c.bounds[k];
        lemma_region(c, k);
    }
}

/// The 8 bytes at `p` are the same in `m` and `m2`, if neither the store of
/// `[addr, addr + size)` nor anything else changed them.
pub proof fn lemma_read8_same(m: Map<int, u8>, m2: Map<int, u8>, p: int, addr: int, size: int)
    requires
        0 <= p,
        p + 8 <= p2(64),
        m2.dom() =~= m.dom(),
        forall|x: int|
            (x < addr || x >= addr + size) && m.dom().contains(x) ==> #[trigger] m2[x] == m[x],
        p + 8 <= addr || addr + size <= p,
    ensures
        mem_read(m2, p, 8) == mem_read(m, p, 8),
{
    assert forall|x: int| p <= x < p + 8 implies (#[trigger] m2.dom().contains(x)
        == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
        assert(x < addr || x >= addr + size);
    }
    lemma_mem_read_same(m, m2, p, 8);
}

/// A store to writable bytes keeps the memory invariant.
pub proof fn lemma_mem_inv_store(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>, addr: int, size: int)
    requires
        cfg_ok(c),
        mem_inv(c, m),
        size >= 0,
        writable(c, addr, size),
        m2.dom() =~= m.dom(),
        forall|x: int|
            (x < addr || x >= addr + size) && m.dom().contains(x) ==> #[trigger] m2[x] == m[x],
    ensures
        mem_inv(c, m2),
{
    lemma_p2();
    lemma_cfg(c);
    lemma_writable_disjoint(c, addr, size);
    assert forall|k: int| 0 <= k < abi::num_regions() implies mem_read(
        m2,
        c.ctx + abi::base_off(k),
        8,
    ) == Some(c.bases[k]) && #[trigger] mem_read(m2, c.ctx + abi::bound_off(k), 8) == Some(
        c.bounds[k],
    ) by {
        lemma_read8_same(m, m2, c.ctx + abi::base_off(k), addr, size);
        lemma_read8_same(m, m2, c.ctx + abi::bound_off(k), addr, size);
    }
    assert forall|q: int| 0 <= q < c.blob.len() implies #[trigger] m2.dom().contains(c.code + q)
        && m2[c.code + q] == c.blob[q] by {
        assert(m.dom().contains(c.code + q));
        assert(c.code + q < addr || c.code + q >= addr + size);
    }
}

/// **A register write that is not to a reserved register, with the program
/// counter and `SP` kept and memory kept**, keeps [`base_inv`].
pub proof fn lemma_base_inv_after(c: Cfg, s: State, s2: State, d: Option<u8>)
    requires
        cfg_ok(c),
        base_inv(c, s),
        s2.r.len() == 31,
        s2.vreg.len() == 32,
        forall|r: int| 0 <= r < 31 && d != Some(r as u8) ==> #[trigger] s2.r[r] == s.r[r],
        d is None || !abi::reserved(d->Some_0),
        s2.sp == s.sp,
        mem_inv(c, s2.mem),
        s2.mem.dom() =~= s.mem.dom(),
    ensures
        base_inv(c, s2),
{
    lemma_base_inv_split(c, s);
    lemma_base_inv_split(c, s2);
    assert(wf(s2)) by {
        assert forall|a: int| s2.mem.dom().contains(a) implies 0 <= a < 0x100_0000_0000_0000 by {
            assert(s.mem.dom().contains(a));
        }
    }
    lemma_xr(s, abi::ctx_reg());
    lemma_xr(s2, abi::ctx_reg());
    lemma_xr(s, abi::link_reg());
    lemma_xr(s2, abi::link_reg());
    assert(d != Some(28u8));
    assert(d != Some(30u8));
    assert(s2.r[28int] == s.r[28int]);
    assert(s2.r[30int] == s.r[30int]);
}

// ----------------------------------------------------------------------------
// Section: the scan's facts under register writes
// ----------------------------------------------------------------------------

/// What [`facts_hold`] says of one register `r`, as a predicate.
pub open spec fn fact_ok(c: Cfg, s: State, r: u8, f: Fact) -> bool {
    match f {
        Fact::Unknown => true,
        Fact::Base(k) => r < 31 && 0 <= k < abi::num_regions() && x_read(s, r, 64) == c.bases[k],
        Fact::Idx(k, n) => r < 31 && 0 <= k < abi::num_regions() && 0 <= n && x_read(s, r, 64) + n
            <= c.bounds[k],
    }
}

/// [`facts_hold`] by [`fact_ok`].
pub proof fn lemma_facts_hold_iff(c: Cfg, s: State, fs: Facts)
    ensures
        facts_hold(c, s, fs) == (forall|r: u8| r < 32 ==> fact_ok(c, s, r, #[trigger] fact_of(fs, r))),
{
}

/// A write to a register whose fact is `Unknown` (or to none) keeps the facts.
pub proof fn lemma_facts_keep(c: Cfg, s: State, s2: State, fs: Facts, d: Option<u8>)
    requires
        facts_hold(c, s, fs),
        s.r.len() == 31,
        s2.r.len() == 31,
        forall|r: int| 0 <= r < 31 && d != Some(r as u8) ==> #[trigger] s2.r[r] == s.r[r],
        d is None || fact_of(fs, d->Some_0) is Unknown,
    ensures
        facts_hold(c, s2, fs),
{
    assert forall|r: u8| r < 32 implies fact_ok(c, s2, r, #[trigger] fact_of(fs, r)) by {
        assert(fact_ok(c, s, r, fact_of(fs, r)));
        if fact_of(fs, r) is Unknown {
        } else {
            assert(d != Some(r));
            assert(r < 31);
            lemma_xr(s, r);
            lemma_xr(s2, r);
            assert(s2.r[r as int] == s.r[r as int]);
        }
    }
}

/// A write to register `d` that makes its fact `f` (which holds in `s2`)
/// gives the facts with `d` bound to `f`.
pub proof fn lemma_facts_set(c: Cfg, s: State, s2: State, fs: Facts, d: u8, f: Fact)
    requires
        facts_hold(c, s, fs),
        s.r.len() == 31,
        s2.r.len() == 31,
        d < 32,
        forall|r: int| 0 <= r < 31 && r != d ==> #[trigger] s2.r[r] == s.r[r],
        fact_ok(c, s2, d, f),
    ensures
        facts_hold(c, s2, set_fact(fs, d, f)),
{
    assert forall|r: u8| r < 32 implies fact_ok(c, s2, r, #[trigger] fact_of(set_fact(fs, d, f), r)) by {
        crate::a64::unit_exec::lemma_fact_of_set(fs, d, f, r);
        assert(fact_ok(c, s, r, fact_of(fs, r)));
        if r != d {
            if !(fact_of(fs, r) is Unknown) {
                assert(r < 31);
                lemma_xr(s, r);
                lemma_xr(s2, r);
                assert(s2.r[r as int] == s.r[r as int]);
            }
        }
    }
}

/// Facts that hold still hold with a register's fact made `Unknown` (with the
/// state as it was).
pub proof fn lemma_facts_unknown(c: Cfg, s: State, fs: Facts, r0: u8)
    requires
        facts_hold(c, s, fs),
    ensures
        facts_hold(c, s, set_fact(fs, r0, Fact::Unknown)),
{
    assert forall|r: u8| r < 32 implies fact_ok(
        c,
        s,
        r,
        #[trigger] fact_of(set_fact(fs, r0, Fact::Unknown), r),
    ) by {
        crate::a64::unit_exec::lemma_fact_of_set(fs, r0, Fact::Unknown, r);
        assert(fact_ok(c, s, r, fact_of(fs, r)));
    }
}

/// No facts hold trivially.
pub proof fn lemma_no_facts_hold(c: Cfg, s: State)
    ensures
        facts_hold(c, s, no_facts()),
{
    assert forall|r: u8| r < 32 implies fact_ok(c, s, r, #[trigger] fact_of(no_facts(), r)) by {
        reveal_with_fuel(fact_of, 1);
    }
}

/// Forgetting keeps facts that hold.
pub proof fn lemma_forgotten_hold(c: Cfg, s: State, j: int, fs: Facts)
    requires
        facts_hold(c, s, fs),
    ensures
        facts_hold(c, s, forgotten(c, j, fs)),
{
    lemma_no_facts_hold(c, s);
}

// ----------------------------------------------------------------------------
// Section: the safety of a permitted access
// ----------------------------------------------------------------------------

/// **A permitted access is in bounds**: if the scan permits an access given
/// facts that hold, the bytes it touches are in the context (a load), in the
/// context's exit area (a store), or in a handed region.
pub proof fn lemma_access_safe(c: Cfg, s: State, fs: Facts, a: Access)
    requires
        cfg_ok(c),
        regs_inv(c, s),
        facts_hold(c, s, fs),
        access_ok(fs, a),
        a.base < 32,
        match a.index {
            Some(m) => m < 32,
            None => true,
        },
        0 < a.size <= abi::max_access(),
    ensures
        readable(c, eff_addr(s, a), a.size),
        a.store ==> writable(c, eff_addr(s, a), a.size),
{
    lemma_p2();
    lemma_cfg(c);
    if a.base == abi::ctx_reg() {
        assert(a.index is None);
        lemma_xr(s, abi::ctx_reg());
        let addr = c.ctx + a.off;
        assert(0 <= addr < p2(64));
        lemma_trunc64_id(addr);
        assert(eff_addr(s, a) == addr);
    } else {
        let m = a.index->Some_0;
        let r1 = a.base;
        assert(fact_ok(c, s, r1, fact_of(fs, r1)));
        assert(fact_ok(c, s, m, fact_of(fs, m)));
        match (fact_of(fs, r1), fact_of(fs, m)) {
            (Fact::Base(k), Fact::Idx(k2, n)) => {
                lemma_region(c, k);
                assert(r1 < 31 && m < 31);
                lemma_xr(s, r1);
                lemma_xr(s, m);
                let b = x_read(s, r1, 64);
                let i = x_read(s, m, 64);
                assert(b == c.bases[k]);
                assert(i + n <= c.bounds[k]);
                assert(!a.scaled);
                assert(extend_reg_uxtx(s, m, 0nat) == trunc(64, i) * p2(0));
                lemma_trunc64_id(i);
                assert(extend_reg_uxtx(s, m, 0nat) == i);
                assert(0 <= b + i < p2(64));
                lemma_trunc64_id(b + i);
                assert(eff_addr(s, a) == b + i);
                assert(in_region(c, eff_addr(s, a), a.size));
            },
            _ => {},
        }
    }
}

// ----------------------------------------------------------------------------
// Section: the instruction at the program counter
// ----------------------------------------------------------------------------

/// The instruction at offset `4 j` is the next instruction.
pub proof fn lemma_next_at(c: Cfg, s: State, j: int)
    requires
        0 <= j < c.ins.len(),
        s.pc as int - c.code == start_of(c.ins, j),
    ensures
        next_instr(c, s) == Some(c.ins[j]),
{
    assert(exists|jj: int|
        0 <= jj < c.ins.len() && start_of(c.ins, jj) == s.pc as int - c.code);
    let jj = choose|jj: int| 0 <= jj < c.ins.len() && start_of(c.ins, jj) == s.pc as int - c.code;
    assert(jj == j);
    assert(index_at(c, s) == Some(j));
}

/// `fetch_ok` from the bytes of [`word_of`].
pub proof fn lemma_fetch_from(s: State, i: Instr)
    requires
        valid_instr(i),
        (s.pc as int) % 4 == 0,
        word_of(i).len() == 4,
        forall|k: int|
            0 <= k < 4 ==> #[trigger] s.mem.dom().contains(s.pc as int + k) && s.mem[s.pc as int
                + k] == word_of(i)[k],
    ensures
        fetch_ok(s, i),
{
    reveal(word_of);
}

/// The bytes of the word at the program counter are the encoding of the
/// instruction, if the blob is in memory there.
pub proof fn lemma_fetch_blob(
    s: State,
    code: int,
    blob: Seq<u8>,
    i: Instr,
    j: int,
)
    requires
        valid_instr(i),
        code % 4 == 0,
        0 <= j,
        4 * j + 4 <= blob.len(),
        blob.subrange(4 * j, 4 * j + 4) == word_of(i),
        word_of(i).len() == 4,
        forall|q: int|
            0 <= q < blob.len() ==> #[trigger] s.mem.dom().contains(code + q) && s.mem[code + q]
                == blob[q],
        s.pc as int == code + 4 * j,
    ensures
        fetch_ok(s, i),
{
    let w = word_of(i);
    assert((s.pc as int) % 4 == 0);
    assert forall|k: int| 0 <= k < 4 implies #[trigger] s.mem.dom().contains(s.pc as int + k)
        && s.mem[s.pc as int + k] == w[k] by {
        assert(blob[4 * j + k] == blob.subrange(4 * j, 4 * j + 4)[k]);
        assert(0 <= 4 * j + k < blob.len());
        assert(s.mem.dom().contains(code + (4 * j + k)));
    }
    lemma_fetch_from(s, i);
}

/// `fetch_ok` of the instruction at the program counter.
pub proof fn lemma_fetch(c: Cfg, s: State, j: int)
    requires
        cfg_ok(c),
        base_inv(c, s),
        0 <= j < c.ins.len(),
        s.pc as int == c.code + start_of(c.ins, j),
    ensures
        fetch_ok(s, c.ins[j]),
{
    lemma_cfg(c);
    lemma_word_of_len();
    assert(valid_instr(c.ins[j]));
    lemma_fetch_blob(s, c.code, c.blob, c.ins[j], j);
}

/// **The invariant puts the instruction `ins[j0 + m]` at the program
/// counter**: it is the next instruction, it is valid, and its bytes are in
/// memory.
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
    lemma_next_at(c, s, j);
    lemma_fetch(c, s, j);
    lemma_cfg(c);
}

// ----------------------------------------------------------------------------
// Section: positions
// ----------------------------------------------------------------------------

/// A step that leaves memory as it was confines writes.
pub proof fn lemma_confined_same(c: Cfg, s: State, s2: State)
    requires
        s2.mem == s.mem,
    ensures
        writes_confined(c, s, s2),
{
}

/// A store to writable bytes confines writes.
pub proof fn lemma_confined_store(c: Cfg, s: State, s2: State, addr: int, size: int)
    requires
        size >= 0,
        writable(c, addr, size),
        store_frame(s, s2, addr, size),
    ensures
        writes_confined(c, s, s2),
{
    assert forall|a: int| !writable_byte(c, a) implies (#[trigger] s2.mem.dom().contains(a)
        == s.mem.dom().contains(a) && (s.mem.dom().contains(a) ==> s2.mem[a] == s.mem[a])) by {
        if addr <= a < addr + size {
            if c.ctx + abi::exit_code_off() <= addr && addr + size <= c.ctx + abi::ctx_size() {
                assert(writable(c, a, 1));
            } else {
                let k = choose|k: int|
                    0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + size <= c.bases[k]
                        + c.bounds[k];
                assert(in_region(c, a, 1));
                assert(writable(c, a, 1));
            }
            assert(false);
        }
        assert(s2.mem.dom() =~= s.mem.dom());
    }
}

/// **The last instruction of a blob is a `ret` or `b`**, so an instruction
/// that is neither is followed by another.
pub proof fn lemma_not_last(c: Cfg, k: int)
    requires
        cfg_ok(c),
        0 <= k < c.ins.len(),
        !(c.ins[k] is Ret),
        !(c.ins[k] is B),
    ensures
        k + 1 < c.ins.len(),
{
    lemma_cfg(c);
    assert(c.ins.last() is Ret || c.ins.last() is B);
    if k + 1 == c.ins.len() {
        assert(c.ins[k] == c.ins.last());
    }
}

/// **The position inside a unit**: after an instruction that is not the last of
/// its unit, the invariant at the next instruction of the unit holds if
/// the base invariant, the program counter and the registers' invariant do.
pub proof fn lemma_pos_mid(c: Cfg, s: State, s2: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        unit_at(c.ins, j0, start_facts(c, j0)->Some_0)->Some_0.len > m + 1,
        base_inv(c, s2),
        s2.pc as int == s.pc as int + 4,
        mid_inv(c, s2, j0, start_facts(c, j0)->Some_0, m + 1),
    ensures
        pos_inv(c, s2, j0, m + 1),
{
    lemma_cur_instr(c, s, j0, m);
}

/// **The position after the last instruction of a unit** that falls through:
/// the next unit start, with the unit's facts (forgotten there).
pub proof fn lemma_pos_fall(c: Cfg, s: State, s2: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        unit_at(c.ins, j0, start_facts(c, j0)->Some_0)->Some_0.len == m + 1,
        j0 + m + 1 < c.ins.len(),
        base_inv(c, s2),
        s2.pc as int == s.pc as int + 4,
        facts_hold(c, s2, unit_at(c.ins, j0, start_facts(c, j0)->Some_0)->Some_0.facts),
    ensures
        pos_inv(c, s2, j0 + m + 1, 0),
{
    lemma_cur_instr(c, s, j0, m);
    let fs0 = start_facts(c, j0)->Some_0;
    let u = unit_at(c.ins, j0, fs0)->Some_0;
    lemma_next_start(c, j0, fs0, u);
    let t = j0 + u.len;
    let f = forgotten(c, t, u.facts);
    assert(start_facts(c, t) == Some(f));
    lemma_unit_ok(c, t, f);
    lemma_forgotten_hold(c, s2, t, u.facts);
}

/// **The position after a jump**: the target is a unit start with no facts.
pub proof fn lemma_pos_jump(c: Cfg, s: State, s2: State, j: int)
    requires
        cfg_ok(c),
        0 <= j < c.ins.len(),
        jump_rel(c.ins[j]) is Some,
        base_inv(c, s2),
        s.pc as int == c.code + start_of(c.ins, j),
        s2.pc as int == trunc(64, s.pc as int + jump_rel(c.ins[j])->Some_0),
    ensures
        inv(c, s2),
{
    lemma_cfg(c);
    lemma_p2();
    lemma_jump_target_is_start(c, j);
    let x = start_of(c.ins, j) + jump_rel(c.ins[j])->Some_0;
    let t = choose|t: int|
        0 <= t < c.ins.len() && x == start_of(c.ins, t) && start_facts(c, t) is Some && start_facts(
            c,
            t,
        )->Some_0 == no_facts();
    assert(0 <= c.code + x < p2(64));
    lemma_trunc64_id(c.code + x);
    assert(s2.pc as int == c.code + start_of(c.ins, t));
    let f = start_facts(c, t)->Some_0;
    lemma_unit_ok(c, t, f);
    lemma_no_facts_hold(c, s2);
    assert(pos_inv(c, s2, t, 0));
}

} // verus!
