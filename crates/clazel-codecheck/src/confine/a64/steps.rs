//! **One step, unit by unit** (A64): from the invariant at a position, the
//! next instruction's accesses are confined and the step either keeps the
//! invariant or leaves through the exit. This file does the exit sequence and
//! the single instructions; `super::check` does the bounds-check sequence.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Both of the accesses of `i` from `s` are in bounds.
pub open spec fn acc_ok(c: Cfg, s: State, i: Instr) -> bool {
    loads_ok(c, s, i) && stores_ok(c, s, i)
}

/// What the theorem says of a step from `s`, executing `i`, to `s2`.
pub open spec fn step_post(c: Cfg, s: State, i: Instr, s2: State) -> bool {
    writes_confined(c, s, s2) && if is_exit(c, s, i) {
        exited(c, s2) && next_instr(c, s2) is None
    } else {
        inv(c, s2) && reserved_same(s, s2)
    }
}

/// The instruction `ret` is the exit only in an exit sequence.
pub proof fn lemma_is_exit_ret(c: Cfg, s: State, i: Instr)
    requires
        is_exit(c, s, i),
    ensures
        i is Ret,
{
    let j = choose|j: int|
        exit_unit_at(c.ins, j) && i == c.ins[j + 2] && s.pc as int == c.code + start_of(
            c.ins,
            j + 2,
        );
}

/// An instruction that is not `ret` is not an exit.
pub proof fn lemma_not_exit(c: Cfg, s: State, i: Instr)
    requires
        !(i is Ret),
    ensures
        !is_exit(c, s, i),
{
    if is_exit(c, s, i) {
        lemma_is_exit_ret(c, s, i);
    }
}

/// An access of an instruction has a positive size of at most 8, and names
/// registers below 32.
pub proof fn lemma_access_regs(i: Instr)
    requires
        valid_instr(i),
        mem_access(i) is Some,
    ensures
        0 < mem_access(i)->Some_0.size <= abi::max_access(),
        mem_access(i)->Some_0.base < 32,
        match mem_access(i)->Some_0.index {
            Some(m) => m < 32,
            None => true,
        },
{
}

/// A permitted access (by the scan, given facts that hold) of the valid
/// instruction `i` is in bounds.
pub proof fn lemma_acc_ok(c: Cfg, s: State, fs: Facts, i: Instr)
    requires
        cfg_ok(c),
        base_inv(c, s),
        facts_hold(c, s, fs),
        valid_instr(i),
        match mem_access(i) {
            Some(a) => access_ok(fs, a),
            None => true,
        },
    ensures
        acc_ok(c, s, i),
{
    lemma_base_inv_split(c, s);
    match mem_access(i) {
        Some(a) => {
            lemma_access_regs(i);
            lemma_access_safe(c, s, fs, a);
        },
        None => {},
    }
}

/// `is_system` is false.
pub proof fn lemma_not_system(i: Instr)
    ensures
        !is_system(i),
{
}

/// A step that moves the program counter on by one word does not wrap.
pub proof fn lemma_pc_succ(c: Cfg, s: State, s2: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        s2.pc as int == trunc(64, s.pc as int + 4),
    ensures
        s2.pc as int == s.pc as int + 4,
{
    lemma_cfg(c);
    lemma_cur_instr(c, s, j0, m);
    lemma_p2();
    let v = s.pc as int + 4;
    assert(0 <= v < p2(64));
    lemma_trunc64_id(v);
}

// ----------------------------------------------------------------------------
// Section: the exit sequence
// ----------------------------------------------------------------------------

/// The step of the exit sequence's `ret`.
pub proof fn lemma_ret_step(c: Cfg, s: State, s2: State)
    requires
        cfg_ok(c),
        base_inv(c, s),
        step(s, Instr::Ret) == Some(s2),
    ensures
        s2.pc as int == c.lr,
        x_read(s2, abi::ctx_reg(), 64) == c.ctx,
        x_read(s2, abi::link_reg(), 64) == c.lr,
        s2.sp as int == c.sp,
        s2.mem == s.mem,
{
    lemma_cfg(c);
    lemma_p2();
    lemma_trunc64_id(c.lr);
    assert(x_read(s, 30, 64) == c.lr);
    assert(s2 == branch_to(s, x_read(s, 30, 64)));
    assert(trunc(64, c.lr) == c.lr);
    assert(s2.pc == c.lr as u64);
}

/// **After the exit `ret`, no instruction of the blob is next.**
pub proof fn lemma_exit_no_next(c: Cfg, s2: State)
    requires
        cfg_ok(c),
        s2.pc as int == c.lr,
    ensures
        next_instr(c, s2) is None,
{
    lemma_cfg(c);
    if index_at(c, s2) is Some {
        let j = choose|j: int| 0 <= j < c.ins.len() && start_of(c.ins, j) == s2.pc as int - c.code;
        assert(disjoint(c.lr, 1, c.code, c.blob.len() as int));
        assert(false);
    }
}

/// **The exit sequence** (three instructions at `j0`): its accesses are in
/// bounds, and each step either stays in the sequence or, at the `ret`,
/// leaves.
pub proof fn lemma_exit_unit(c: Cfg, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        exit_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + m]),
        forall|s2: State| step(s, c.ins[j0 + m]) == Some(s2) ==> step_post(c, s, c.ins[j0 + m], s2),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_base_inv_split(c, s);
    let fs0 = start_facts(c, j0)->Some_0;
    assert(unit_at(c.ins, j0, fs0) == Some(Unit { len: 3, facts: no_facts() }));
    let i = c.ins[j0 + m];
    assert(wf(s));
    match (c.ins[j0], c.ins[j0 + 1], c.ins[j0 + 2]) {
        (
            Instr::MoveWide { sf: Width::W32, opcode: MoveWideOp::Z, d: t, imm16, hw },
            Instr::LoadStoreImm { sf: Width::W64, load: false, t: src, n, imm12 },
            Instr::Ret,
        ) => {
            if m == 0 {
                assert(i == c.ins[j0]);
                assert(mem_access(i) is None);
                assert(acc_ok(c, s, i));
                lemma_not_exit(c, s, i);
                assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                    lemma_step_straight(s, i, s2);
                    lemma_pc_succ(c, s, s2, j0, m);
                    assert(written_gpr(i) == Some(t));
                    lemma_base_inv_after(c, s, s2, Some(t));
                    lemma_facts_set(c, s, s2, fs0, t, Fact::Unknown);
                    assert(exit_mid_facts(c.ins, j0, fs0) == set_fact(fs0, t, Fact::Unknown));
                    lemma_pos_mid(c, s, s2, j0, 0);
                    lemma_confined_same(c, s, s2);
                    assert(inv(c, s2));
                }
            } else if m == 1 {
                let fsm = exit_mid_facts(c.ins, j0, fs0);
                assert(i == c.ins[j0 + 1]);
                let a = mem_access(i)->Some_0;
                assert(access_ok(fsm, a));
                lemma_acc_ok(c, s, fsm, i);
                lemma_not_exit(c, s, i);
                assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                    lemma_step_straight(s, i, s2);
                    lemma_pc_succ(c, s, s2, j0, m);
                    let addr = eff_addr(s, a);
                    assert(writable(c, addr, a.size));
                    let data = choose|data: int|
                        #[trigger] mem_set(s.mem, addr, a.size as nat, data) == Some(s2.mem);
                    lemma_p2();
                    lemma_cfg(c);
                    assert(0 <= addr && addr + a.size <= p2(64)) by {
                        lemma_writable_in_range(c, addr, a.size);
                    }
                    lemma_mem_set_frame(s.mem, addr, a.size as nat, data, s2.mem);
                    lemma_mem_inv_store(c, s.mem, s2.mem, addr, a.size);
                    assert(written_gpr(i) is None);
                    lemma_base_inv_after(c, s, s2, None);
                    lemma_facts_keep(c, s, s2, fsm, None);
                    lemma_pos_mid(c, s, s2, j0, 1);
                    assert(store_frame(s, s2, addr, a.size));
                    lemma_confined_store(c, s, s2, addr, a.size);
                    assert(inv(c, s2));
                }
            } else {
                assert(m == 2);
                assert(i == c.ins[j0 + 2]);
                assert(mem_access(i) is None);
                assert(acc_ok(c, s, i));
                assert(is_exit(c, s, i)) by {
                    assert(exit_unit_at(c.ins, j0) && i == c.ins[j0 + 2] && s.pc as int == c.code
                        + start_of(c.ins, j0 + 2));
                }
                assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                    lemma_ret_step(c, s, s2);
                    lemma_confined_same(c, s, s2);
                    lemma_exit_no_next(c, s2);
                }
            }
        },
        _ => {
            assert(false);
        },
    }
}

/// Writable bytes lie within the positive canonical addresses.
pub proof fn lemma_writable_in_range(c: Cfg, addr: int, size: int)
    requires
        cfg_ok(c),
        writable(c, addr, size),
    ensures
        0 <= addr,
        addr + size <= lim(),
        lim() < p2(64),
{
    lemma_cfg(c);
    lemma_p2();
    if c.ctx + abi::exit_code_off() <= addr && addr + size <= c.ctx + abi::ctx_size() {
    } else {
        let k = choose|k: int|
            0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + size <= c.bases[k]
                + c.bounds[k];
        lemma_region(c, k);
    }
}

// ----------------------------------------------------------------------------
// Section: single instructions
// ----------------------------------------------------------------------------

/// A 64-bit load of `[x28, #16k]` loads region `k`'s base.
pub proof fn lemma_base_load_value(c: Cfg, s: State, i: Instr, s2: State, k: int)
    requires
        cfg_ok(c),
        base_inv(c, s),
        valid_instr(i),
        base_load_region(i) == Some(k),
        step(s, i) == Some(s2),
    ensures
        0 <= k < abi::num_regions(),
        written_gpr(i) is Some,
        written_gpr(i)->Some_0 < 31,
        x_read(s2, written_gpr(i)->Some_0, 64) == c.bases[k],
{
    lemma_cfg(c);
    lemma_p2();
    lemma_base_inv_split(c, s);
    match i {
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => {
            assert(imm12 as int * 8 == 16 * k);
            assert(0 <= k < abi::num_regions());
            lemma_xr(s, abi::ctx_reg());
            let addr = c.ctx + 16 * k;
            lemma_region(c, k);
            assert(0 <= addr < p2(64));
            lemma_trunc64_id(addr);
            assert(mem_read(s.mem, c.ctx + abi::bound_off(k), 8) == Some(c.bounds[k]));
            assert(mem_read(s.mem, c.ctx + abi::base_off(k), 8) == Some(c.bases[k]));
            lemma_step_straight(s, i, s2);
            let s1 = execute(s, i)->Some_0;
            assert(sf is W64 && load);
            lemma_trunc64_id(c.bases[k]);
            assert(s1 == x_set(s, t, 64, c.bases[k]));
            assert(t < 31);
            assert(s2.r == s1.r);
            lemma_xr(s2, t);
        },
        _ => {
            assert(false);
        },
    }
}

/// **A single instruction**: if the scan permits it (it is not part of a
/// recognized sequence), its accesses are in bounds and its step keeps the
/// invariant.
pub proof fn lemma_plain_unit(c: Cfg, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        !exit_unit_at(c.ins, j0),
        !check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + m]),
        forall|s2: State| step(s, c.ins[j0 + m]) == Some(s2) ==> step_post(c, s, c.ins[j0 + m], s2),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_base_inv_split(c, s);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let i = c.ins[j0];
    assert(m == 0);
    assert(facts_hold(c, s, fs0));
    let pk = plain_ok(fs0, i);
    assert(pk is Some);
    let fs1 = pk->Some_0;
    assert(unit_at(c.ins, j0, fs0) == Some(Unit { len: 1, facts: fs1 }));
    assert(!(i is Ret));
    assert(!writes_reserved(i));
    assert(wf(s));
    lemma_acc_ok(c, s, fs0, i);
    lemma_not_exit(c, s, i);
    match i {
        Instr::B { imm26 } => {
            assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                assert(s2 == branch_to(s, s.pc as int + imm26 as int * 4));
                lemma_base_inv_after(c, s, s2, None);
                lemma_confined_same(c, s, s2);
                assert(jump_rel(i) == Some(imm26 as int * 4));
                lemma_pos_jump(c, s, s2, j0);
                assert(inv(c, s2));
            }
        },
        Instr::BCond { cond, imm19 } => {
            assert(fs1 == fs0);
            assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                lemma_confined_same_branch(c, s, s2, i);
                lemma_base_inv_after(c, s, s2, None);
                lemma_confined_same(c, s, s2);
                if condition_holds(s, cond) {
                    assert(s2 == branch_to(s, s.pc as int + imm19 as int * 4));
                    assert(jump_rel(i) == Some(imm19 as int * 4));
                    lemma_pos_jump(c, s, s2, j0);
                } else {
                    assert(s2 == branch_to(s, s.pc as int + 4));
                    lemma_pc_succ(c, s, s2, j0, m);
                    lemma_not_last(c, j0);
                    lemma_pos_fall(c, s, s2, j0, 0);
                }
                assert(inv(c, s2));
            }
        },
        Instr::CompareBranch { sf, iszero, t, imm19 } => {
            assert(fs1 == fs0);
            assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                lemma_confined_same_branch(c, s, s2, i);
                lemma_base_inv_after(c, s, s2, None);
                lemma_confined_same(c, s, s2);
                let operand1 = x_read(s, t, datasize(sf));
                if (operand1 == 0) == iszero {
                    assert(s2 == branch_to(s, s.pc as int + imm19 as int * 4));
                    assert(jump_rel(i) == Some(imm19 as int * 4));
                    lemma_pos_jump(c, s, s2, j0);
                } else {
                    assert(s2 == branch_to(s, s.pc as int + 4));
                    lemma_pc_succ(c, s, s2, j0, m);
                    lemma_not_last(c, j0);
                    lemma_pos_fall(c, s, s2, j0, 0);
                }
                assert(inv(c, s2));
            }
        },
        Instr::Ret => {
            assert(false);
        },
        _ => {
            lemma_not_last(c, j0);
            assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                lemma_step_straight(s, i, s2);
                lemma_pc_succ(c, s, s2, j0, m);
                let d = written_gpr(i);
                // The memory invariant.
                match mem_access(i) {
                    Some(a) => {
                        if a.store {
                            let addr = eff_addr(s, a);
                            assert(writable(c, addr, a.size));
                            let data = choose|data: int|
                                #[trigger] mem_set(s.mem, addr, a.size as nat, data) == Some(s2.mem);
                            lemma_writable_in_range(c, addr, a.size);
                            lemma_mem_set_frame(s.mem, addr, a.size as nat, data, s2.mem);
                            lemma_mem_inv_store(c, s.mem, s2.mem, addr, a.size);
                            assert(store_frame(s, s2, addr, a.size));
                            lemma_confined_store(c, s, s2, addr, a.size);
                        } else {
                            lemma_confined_same(c, s, s2);
                        }
                    },
                    None => {
                        lemma_confined_same(c, s, s2);
                    },
                }
                lemma_base_inv_after(c, s, s2, d);
                // The facts.
                match d {
                    None => {
                        assert(fs1 == fs0);
                        lemma_facts_keep(c, s, s2, fs0, None);
                    },
                    Some(dd) => {
                        assert(dd < 32);
                        match base_load_region(i) {
                            Some(k) => {
                                lemma_base_load_value(c, s, i, s2, k);
                                lemma_facts_set(c, s, s2, fs0, dd, Fact::Base(k));
                            },
                            None => {
                                lemma_facts_set(c, s, s2, fs0, dd, Fact::Unknown);
                            },
                        }
                    },
                }
                lemma_pos_fall(c, s, s2, j0, 0);
                assert(inv(c, s2));
            }
        },
    }
}

/// The step of a conditional branch changes only the program counter.
pub proof fn lemma_confined_same_branch(c: Cfg, s: State, s2: State, i: Instr)
    requires
        i is BCond || i is CompareBranch,
        step(s, i) == Some(s2),
    ensures
        s2.mem == s.mem,
        s2.r == s.r,
        s2.vreg == s.vreg,
        s2.sp == s.sp,
        s2.r.len() == s.r.len(),
        s2.vreg.len() == s.vreg.len(),
{
}

} // verus!
