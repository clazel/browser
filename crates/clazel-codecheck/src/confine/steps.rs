//! **One step, unit by unit**: from the invariant at a position, the next
//! instruction's accesses are confined and the step either keeps the invariant
//! or leaves through the exit. This file does the exit sequence and the
//! single instructions; `super::check` does the bounds-check sequence.

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

/// The unit's shape: `unit_at` at a reached start.
pub proof fn lemma_unit_shape(c: Cfg, j0: int, m: int, s: State)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
    ensures
        ({
            let fs0 = start_facts(c, j0)->Some_0;
            let u = unit_at(c.ins, j0, fs0)->Some_0;
            start_facts(c, j0) is Some && unit_at(c.ins, j0, fs0) is Some && 0 <= m < u.len
                && facts_hold(c, s, if m == 0 {
                fs0
            } else {
                no_facts()
            })
        }),
{
    lemma_no_facts_hold(c, s);
    lemma_cur_instr(c, s, j0, m);
}

/// The instruction `ret` is the exit only in an exit sequence.
pub proof fn lemma_is_exit_ret(c: Cfg, s: State, i: Instr)
    requires
        is_exit(c, s, i),
    ensures
        i is Ret,
{
    let j = choose|j: int|
        exit_unit_at(c.ins, j) && i == c.ins[j + 2] && s.rip == c.code + start_of(c.ins, j + 2);
}

/// An access of an instruction has a positive size of at most 8.
pub proof fn lemma_access_size(i: Instr)
    requires
        mem_access(i) is Some,
    ensures
        0 < mem_access(i)->Some_0.size <= abi::max_access(),
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
            lemma_access_size(i);
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

// ----------------------------------------------------------------------------
// Section: the exit sequence
// ----------------------------------------------------------------------------

/// The step of the exit sequence's `ret`.
pub proof fn lemma_ret_step(c: Cfg, cu: spec_fn(nat) -> nat, s: State, s2: State)
    requires
        cfg_ok(c),
        base_inv(c, s),
        step(cu, s, Instr::Ret) == Some(s2),
    ensures
        s2.rip == logext(64, c.ret_raw),
        rr64(s2, abi::ctx_reg()) == c.ctx,
        rr64(s2, abi::sp_reg()) == c.sp + 8,
        s2.mem == s.mem,
{
    lemma_p2();
    lemma_base_inv_split(c, s);
    lemma_logext64_id(c.sp);
    lemma_logext64_id(c.sp + 8);
    let rsp = logext(64, rr64(s, 4));
    assert(rsp == c.sp);
    assert(read_mem(s.mem, rsp, 8) == Some(c.ret_raw));
    let new_rsp = logext(64, rsp + 8);
    assert(new_rsp == c.sp + 8);
    assert(canonical(new_rsp));
    assert(s2 == write_ip(wr64(s, 4, new_rsp), logext(64, c.ret_raw)));
    lemma_loghead64_id(c.sp + 8);
}

/// **After the exit `ret`, no instruction of the blob is next.**
pub proof fn lemma_exit_no_next(c: Cfg, s2: State)
    requires
        cfg_ok(c),
        s2.rip == logext(64, c.ret_raw),
    ensures
        next_instr(c, s2) is None,
{
    crate::validate::lemma_enc_all_len(c.ins);
    assert(c.blob == enc_all(c.ins));
    assert(c.blob.len() == start_of(c.ins, c.ins.len() as int));
    if index_at(c, s2) is Some {
        let j = choose|j: int| 0 <= j < c.ins.len() && start_of(c.ins, j) == s2.rip - c.code;
        crate::scan_exec::lemma_start_of_lt(c.ins, j, c.ins.len() as int);
        crate::validate::lemma_start_of_ge(c.ins, j);
        assert(disjoint(logext(64, c.ret_raw), 1, c.code, c.blob.len() as int));
        assert(false);
    }
}

/// **The exit sequence** (three instructions at `j0`): its accesses are in
/// bounds, and each step either stays in the sequence or, at the `ret`,
/// leaves.
pub proof fn lemma_exit_unit(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        exit_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + m]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + m]) == Some(s2) ==> step_post(c, s, c.ins[j0 + m], s2),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_base_inv_split(c, s);
    let fs0 = start_facts(c, j0)->Some_0;
    assert(unit_at(c.ins, j0, fs0) == Some(Unit { len: 3, facts: no_facts() }));
    let i = c.ins[j0 + m];
    assert(wf(s));
    match (c.ins[j0], c.ins[j0 + 1], c.ins[j0 + 2]) {
        (
            Instr::MovImm32 { dst: t, imm_u32: imm },
            Instr::MovStore { sz, mem, src },
            Instr::Ret,
        ) => {
            if m == 0 {
                assert(mem_access(i) is None);
                assert(acc_ok(c, s, i));
                assert(!is_exit(c, s, i)) by {
                    if is_exit(c, s, i) {
                        lemma_is_exit_ret(c, s, i);
                    }
                }
                assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(
                    c,
                    s,
                    i,
                    s2,
                ) by {
                    lemma_step_straight(cu, s, i, s2);
                    lemma_base_inv_after(c, s, s2, Some(t));
                    lemma_facts_set(c, s, s2, fs0, t, Fact::Unknown);
                    assert(exit_mid_facts(c.ins, j0, fs0) == set_fact(fs0, t, Fact::Unknown));
                    lemma_pos_mid(c, s, s2, j0, 0);
                    lemma_confined_same(c, s, s2);
                    assert(inv(c, s2));
                }
            } else if m == 1 {
                let fsm = exit_mid_facts(c.ins, j0, fs0);
                let a = mem_access(i)->Some_0;
                assert(access_ok(fsm, a));
                lemma_acc_ok(c, s, fsm, i);
                assert(!is_exit(c, s, i)) by {
                    if is_exit(c, s, i) {
                        lemma_is_exit_ret(c, s, i);
                    }
                }
                assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(
                    c,
                    s,
                    i,
                    s2,
                ) by {
                    lemma_step_straight(cu, s, i, s2);
                    let addr = eff_addr(s, a.mem);
                    assert(writable(c, addr, a.size));
                    lemma_mem_inv_store(c, s.mem, s2.mem, addr, a.size);
                    lemma_base_inv_after(c, s, s2, None);
                    lemma_facts_keep(c, s, s2, fsm, None);
                    lemma_pos_mid(c, s, s2, j0, 1);
                    lemma_confined_store(c, s, s2, addr, a.size);
                    assert(inv(c, s2));
                }
            } else {
                assert(m == 2);
                assert(mem_access(i) is None);
                assert(is_exit(c, s, i)) by {
                    assert(exit_unit_at(c.ins, j0) && i == c.ins[j0 + 2] && s.rip == c.code
                        + start_of(c.ins, j0 + 2));
                }
                assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(
                    c,
                    s,
                    i,
                    s2,
                ) by {
                    lemma_ret_step(c, cu, s, s2);
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

// ----------------------------------------------------------------------------
// Section: single instructions
// ----------------------------------------------------------------------------

/// A 64-bit load of `[r15 + 16k]` loads region `k`'s base.
pub proof fn lemma_base_load_value(
    c: Cfg,
    cu: spec_fn(nat) -> nat,
    s: State,
    i: Instr,
    s2: State,
    k: int,
)
    requires
        cfg_ok(c),
        base_inv(c, s),
        valid_instr(i),
        base_load_region(i) == Some(k),
        step(cu, s, i) == Some(s2),
    ensures
        0 <= k < abi::num_regions(),
        written_gpr(i) is Some,
        rr64(s2, written_gpr(i)->Some_0) == c.bases[k],
{
    lemma_p2();
    lemma_base_inv_split(c, s);
    match i {
        Instr::MovLoad { sz, dst, mem } => {
            let addr = c.ctx + mem.disp as int;
            lemma_logext64_id(addr);
            assert(eff_addr(s, mem) == addr);
            assert(mem.disp == 16 * k);
            assert(abi::base_off(k) == 16 * k);
            assert(0 <= k < abi::num_regions());
            assert(read_mem(s.mem, c.ctx + abi::bound_off(k), 8) == Some(c.bounds[k]));
            assert(read_mem(s.mem, addr, 8) == Some(c.bases[k]));
            lemma_step_straight(cu, s, i, s2);
            let v = c.bases[k];
            lemma_region(c, k);
            lemma_loghead64_id(v);
            assert(sz is W64);
            assert(read_operand_mem(s, sz, mem) == Some(v));
            let s1 = effect(cu, s, i)->Some_0;
            assert(s1 == set_rgfi_size(s, Size::W64, dst, v));
            assert(s1 == wr64(s, dst, v));
            assert(s2.rgf == s1.rgf);
            assert(dst < 16 && s.rgf.len() == 16);
            assert(s1.rgf[dst as int] == loghead(64, v) as u64);
            assert(rr64(s2, dst) == loghead(64, v));
        },
        _ => {
            assert(false);
        },
    }
}

/// **A single instruction**: if the scan permits it (it is not part of a
/// recognized sequence), its accesses are in bounds and its step keeps the
/// invariant.
pub proof fn lemma_plain_unit(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        !exit_unit_at(c.ins, j0),
        !check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + m]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + m]) == Some(s2) ==> step_post(c, s, c.ins[j0 + m], s2),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_base_inv_split(c, s);
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
    lemma_acc_ok(c, s, fs0, i);
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    match i {
        Instr::Jcc { cc, rel } => {
            assert(fs1 == fs0);
            assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                let end = s.rip + instr_len(i) as int;
                let taken = jcc_cmovcc_setcc_spec(s, cc);
                let target = if taken {
                    end + rel as int
                } else {
                    end
                };
                assert(add_to_ip(target, 0) is Some);
                assert(s2 == write_ip(s, target));
                lemma_base_inv_after(c, s, s2, None);
                lemma_confined_same(c, s, s2);
                if taken {
                    assert(jump_rel(i) == Some(rel as int));
                    lemma_start_of_succ(c.ins, j0);
                    lemma_pos_jump(c, s, s2, j0);
                } else {
                    lemma_not_last(c, j0);
                    lemma_pos_fall(c, s, s2, j0, 0);
                }
                assert(inv(c, s2));
            }
        },
        Instr::Jmp { rel } => {
            assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                let end = s.rip + instr_len(i) as int;
                assert(s2 == write_ip(s, end + rel as int));
                lemma_base_inv_after(c, s, s2, None);
                lemma_confined_same(c, s, s2);
                assert(jump_rel(i) == Some(rel as int));
                lemma_start_of_succ(c.ins, j0);
                lemma_pos_jump(c, s, s2, j0);
                assert(inv(c, s2));
            }
        },
        Instr::Ret => {
            assert(false);
        },
        _ => {
            lemma_not_last(c, j0);
            assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
                lemma_step_straight(cu, s, i, s2);
                let d = written_gpr(i);
                // The memory invariant.
                match mem_access(i) {
                    Some(a) => {
                        if a.store {
                            let addr = eff_addr(s, a.mem);
                            assert(writable(c, addr, a.size));
                            lemma_mem_inv_store(c, s.mem, s2.mem, addr, a.size);
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
                        assert(dd < 16);
                        match base_load_region(i) {
                            Some(k) => {
                                lemma_base_load_value(c, cu, s, i, s2, k);
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

} // verus!
