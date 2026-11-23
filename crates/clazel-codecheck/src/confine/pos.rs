//! **Positions**: building the invariant at the next position of a step, and
//! the shared facts about steps (writes are confined, a unit is not the last
//! instruction, `Unknown` facts).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `start_of` after one more instruction.
pub proof fn lemma_start_of_succ(ins: Seq<Instr>, j: int)
    requires
        0 <= j < ins.len(),
    ensures
        start_of(ins, j + 1) == start_of(ins, j) + instr_len(ins[j]) as int,
{
}

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

/// Facts that hold still hold with a register's fact made `Unknown`.
pub proof fn lemma_facts_unknown(c: Cfg, s: State, fs: Facts, r0: u8)
    requires
        facts_hold(c, s, fs),
    ensures
        facts_hold(c, s, set_fact(fs, r0, Fact::Unknown)),
{
    assert forall|r: u8| r < 16 implies match #[trigger] fact_of(
        set_fact(fs, r0, Fact::Unknown),
        r,
    ) {
        Fact::Unknown => true,
        Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s, r) == c.bases[k],
        Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s, r) + n <= c.bounds[k],
    } by {
        crate::unit_exec::lemma_fact_of_set(fs, r0, Fact::Unknown, r);
    }
}

/// No facts hold trivially.
pub proof fn lemma_no_facts_hold(c: Cfg, s: State)
    ensures
        facts_hold(c, s, no_facts()),
{
    assert forall|r: u8| r < 16 implies match #[trigger] fact_of(no_facts(), r) {
        Fact::Unknown => true,
        Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s, r) == c.bases[k],
        Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s, r) + n <= c.bounds[k],
    } by {
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

/// **The last instruction of a blob is a `ret` or `jmp`**, so an instruction
/// that is neither is followed by another.
pub proof fn lemma_not_last(c: Cfg, k: int)
    requires
        cfg_ok(c),
        0 <= k < c.ins.len(),
        !(c.ins[k] is Ret),
        !(c.ins[k] is Jmp),
    ensures
        k + 1 < c.ins.len(),
{
    assert(policy(c.ins, c.entries));
    assert(c.ins.last() is Ret || c.ins.last() is Jmp);
    if k + 1 == c.ins.len() {
        assert(c.ins[k] == c.ins.last());
    }
}

/// **The position inside a unit**: after an instruction that is not the last of
/// its unit, the invariant at the next instruction of the unit holds if
/// the base invariant, RIP and the registers' invariant do.
pub proof fn lemma_pos_mid(c: Cfg, s: State, s2: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        unit_at(c.ins, j0, start_facts(c, j0)->Some_0)->Some_0.len > m + 1,
        base_inv(c, s2),
        s2.rip == s.rip + instr_len(c.ins[j0 + m]) as int,
        mid_inv(c, s2, j0, start_facts(c, j0)->Some_0, m + 1),
    ensures
        pos_inv(c, s2, j0, m + 1),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_start_of_succ(c.ins, j0 + m);
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
        s2.rip == s.rip + instr_len(c.ins[j0 + m]) as int,
        facts_hold(c, s2, unit_at(c.ins, j0, start_facts(c, j0)->Some_0)->Some_0.facts),
    ensures
        pos_inv(c, s2, j0 + m + 1, 0),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_start_of_succ(c.ins, j0 + m);
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
        s2.rip == c.code + start_of(c.ins, j + 1) + jump_rel(c.ins[j])->Some_0,
    ensures
        inv(c, s2),
{
    lemma_jump_target_is_start(c, j);
    let x = start_of(c.ins, j + 1) + jump_rel(c.ins[j])->Some_0;
    let t = choose|t: int|
        0 <= t < c.ins.len() && x == start_of(c.ins, t) && start_facts(c, t) is Some && start_facts(
            c,
            t,
        )->Some_0 == no_facts();
    let f = start_facts(c, t)->Some_0;
    lemma_unit_ok(c, t, f);
    lemma_no_facts_hold(c, s2);
    assert(pos_inv(c, s2, t, 0));
}

} // verus!
