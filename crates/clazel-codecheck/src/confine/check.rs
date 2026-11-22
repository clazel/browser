//! **The bounds-check sequence** (eight instructions, [`check_instr`]): each
//! step keeps the invariant [`check_mid`] describes, and after the last the
//! index register is checked ([`Fact::Idx`]) for the region. This is where
//! the carry and zero flags are used: `jb` falls through only if the add did
//! not wrap, `ja` only if the sum is at most the bound, and the final
//! `cmovae` does not move because the index is below the bound.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What every step of a bounds check has in hand.
pub proof fn lemma_check_prelude(c: Cfg, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        start_facts(c, j0) is Some,
        ({
            let fs0 = start_facts(c, j0)->Some_0;
            let ch = check_params(c.ins, j0)->Some_0;
            check_ok(ch) && unit_at(c.ins, j0, fs0) == Some(
                Unit { len: 8, facts: check_facts(fs0, c.ins, j0) },
            ) && 0 <= m < 8 && c.ins[j0 + m] == check_instr(m, ch) && (forall|q: int|
                0 <= q < 8 ==> #[trigger] c.ins[j0 + q] == check_instr(q, ch)) && ch.t < 16
                && ch.i < 16 && ch.z < 16 && facts_hold(c, s, check_mid_facts(fs0, ch))
                && fact_of(check_mid_facts(fs0, ch), ch.t) is Unknown && fact_of(
                check_mid_facts(fs0, ch),
                ch.z,
            ) is Unknown && fact_of(check_mid_facts(fs0, ch), ch.i) is Unknown && base_inv(c, s)
                && read_mem(s.mem, c.ctx + abi::bound_off(ch.k), 8) == Some(c.bounds[ch.k])
                && 0 <= ch.k < abi::num_regions() && (m > 0 ==> check_mid(c, s, ch, fs0, m))
                && (m == 0 ==> facts_hold(c, s, fs0))
        }),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_base_inv_split(c, s);
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let u = unit_at(c.ins, j0, fs0)->Some_0;
    assert(!exit_unit_at(c.ins, j0));
    assert(u == (Unit { len: 8, facts: check_facts(fs0, c.ins, j0) }));
    assert(check_ok(ch));
    assert(all_valid(c.ins));
    assert(valid_instr(c.ins[j0]));
    assert(valid_instr(c.ins[j0 + 5]));
    let fsm = check_mid_facts(fs0, ch);
    let a = set_fact(fs0, ch.t, Fact::Unknown);
    let b = set_fact(a, ch.z, Fact::Unknown);
    crate::unit_exec::lemma_fact_of_set(fs0, ch.t, Fact::Unknown, ch.t);
    crate::unit_exec::lemma_fact_of_set(a, ch.z, Fact::Unknown, ch.t);
    crate::unit_exec::lemma_fact_of_set(a, ch.z, Fact::Unknown, ch.z);
    crate::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Unknown, ch.t);
    crate::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Unknown, ch.z);
    crate::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Unknown, ch.i);
    if m == 0 {
        lemma_facts_unknown(c, s, fs0, ch.t);
        lemma_facts_unknown(c, s, a, ch.z);
        lemma_facts_unknown(c, s, b, ch.i);
    }
    assert(read_mem(s.mem, c.ctx + abi::bound_off(ch.k), 8) == Some(c.bounds[ch.k]));
}

/// The scan's facts after the bounds check hold, if the check's own
/// invariant does and the registers are as at the end.
pub proof fn lemma_check_facts_hold(c: Cfg, s: State, s2: State, ch: Chk, fs0: Facts)
    requires
        facts_hold(c, s, check_mid_facts(fs0, ch)),
        check_ok(ch),
        ch.t < 16,
        ch.i < 16,
        ch.z < 16,
        0 <= ch.k < abi::num_regions(),
        s2.rgf == s.rgf,
        rr64(s, ch.i) + ch.n <= c.bounds[ch.k],
    ensures
        facts_hold(
            c,
            s2,
            set_fact(
                set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.z, Fact::Unknown),
                ch.i,
                Fact::Idx(ch.k, ch.n),
            ),
        ),
{
    let a = set_fact(fs0, ch.t, Fact::Unknown);
    let b = set_fact(a, ch.z, Fact::Unknown);
    let fin = set_fact(b, ch.i, Fact::Idx(ch.k, ch.n));
    let fsm = check_mid_facts(fs0, ch);
    assert forall|r: u8| r < 16 implies match #[trigger] fact_of(fin, r) {
        Fact::Unknown => true,
        Fact::Base(k) => 0 <= k < abi::num_regions() && rr64(s2, r) == c.bases[k],
        Fact::Idx(k, n) => 0 <= k < abi::num_regions() && 0 <= n && rr64(s2, r) + n <= c.bounds[k],
    } by {
        crate::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Idx(ch.k, ch.n), r);
        crate::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Unknown, r);
        crate::unit_exec::lemma_fact_of_set(a, ch.z, Fact::Unknown, r);
        crate::unit_exec::lemma_fact_of_set(fs0, ch.t, Fact::Unknown, r);
        if r == ch.i {
            assert(rr64(s2, r) == rr64(s, r));
        } else if r == ch.z || r == ch.t {
        } else {
            assert(fact_of(fsm, r) == fact_of(fs0, r));
            assert(fact_of(fin, r) == fact_of(fs0, r));
            assert(rr64(s2, r) == rr64(s, r));
        }
    }
}

/// Instruction 0 of a bounds check, `mov t, i`.
pub proof fn lemma_check_0(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 0),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0]),
        forall|s2: State| step(cu, s, c.ins[j0]) == Some(s2) ==> step_post(c, s, c.ins[j0], s2),
{
    lemma_check_prelude(c, s, j0, 0);
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == Instr::MovRR { sz: Size::W64, dst: ch.t, src: ch.i });
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(cu, s, i, s2);
        lemma_base_inv_after(c, s, s2, Some(ch.t));
        lemma_facts_keep(c, s, s2, fsm, Some(ch.t));
        let s1 = effect(cu, s, i)->Some_0;
        assert(s1 == wr64(s, ch.t, rr64(s, ch.i)));
        assert(s.rgf.len() == 16);
        lemma_loghead64_id(rr64(s, ch.i));
        assert(rr64(s2, ch.t) == rr64(s, ch.i));
        assert(rr64(s2, ch.i) == rr64(s, ch.i));
        assert(mid_inv(c, s2, j0, fs0, 1));
        lemma_pos_mid(c, s, s2, j0, 0);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 1, `add t, n`.
pub proof fn lemma_check_1(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 1),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 1]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 1]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 1], s2),
{
    lemma_check_prelude(c, s, j0, 1);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 1];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst: ch.t, imm: ch.n as i32 });
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    let tv = rr64(s, ch.t);
    let iv = rr64(s, ch.i);
    assert(tv == iv);
    assert(0 <= tv < 18446744073709551616);
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(cu, s, i, s2);
        lemma_base_inv_after(c, s, s2, Some(ch.t));
        lemma_facts_keep(c, s, s2, fsm, Some(ch.t));
        let n = ch.n;
        assert(loghead(64, n as int) == n);
        let r = gpr_arith_logic_spec(64, AluOp::Add, tv, n as int, s.rflags);
        assert(r == gpr_add_spec(64, tv, n as int, s.rflags));
        let s1 = set_rgfi_size(s, Size::W64, ch.t, r.result);
        assert(s1 == wr64(s, ch.t, r.result));
        lemma_add64_flags(cu, s1, tv, n as int);
        let e = effect(cu, s, i)->Some_0;
        assert(e == write_user_rflags(cu, s1, r.rflags, r.undef));
        assert(s2 == write_ip(e, s.rip + instr_len(i) as int));
        assert(flgi(s2, cf_bit()) == flgi(e, cf_bit()));
        lemma_loghead64_id((tv + n) % 18446744073709551616);
        assert(rr64(s2, ch.t) == (iv + n) % p2(64));
        assert(rr64(s2, ch.i) == iv);
        assert(mid_inv(c, s2, j0, fs0, 2));
        lemma_pos_mid(c, s, s2, j0, 1);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 2, `jb exit1`.
pub proof fn lemma_check_2(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 2),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 2]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 2]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 2], s2),
{
    lemma_check_prelude(c, s, j0, 2);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 2];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == Instr::Jcc { cc: 2, rel: ch.r1 });
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    let iv = rr64(s, ch.i);
    let tv = rr64(s, ch.t);
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        let end = s.rip + instr_len(i) as int;
        let taken = jcc_cmovcc_setcc_spec(s, 2);
        let target = if taken {
            end + ch.r1 as int
        } else {
            end
        };
        assert(add_to_ip(target, 0) is Some);
        assert(s2 == write_ip(s, target));
        lemma_base_inv_after(c, s, s2, None);
        lemma_confined_same(c, s, s2);
        lemma_start_of_succ(c.ins, j0 + 2);
        if taken {
            assert(jump_rel(i) == Some(ch.r1 as int));
            lemma_pos_jump(c, s, s2, j0 + 2);
        } else {
            assert(flgi(s, cf_bit()) != 1);
            assert(iv + ch.n < p2(64));
            assert(tv == iv + ch.n);
            assert(mid_inv(c, s2, j0, fs0, 3));
            lemma_pos_mid(c, s, s2, j0, 2);
        }
        assert(inv(c, s2));
    }
}

/// Instruction 3, `cmp t, [r15 + bound]`.
pub proof fn lemma_check_3(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 3),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 3]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 3]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 3], s2),
{
    lemma_check_prelude(c, s, j0, 3);
    lemma_p2();
    lemma_base_inv_split(c, s);
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 3];
    let fsm = check_mid_facts(fs0, ch);
    let bm = bound_mem(ch.k);
    assert(i == Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: ch.t, mem: bm });
    lemma_no_facts_hold(c, s);
    assert(access_ok(no_facts(), mem_access(i)->Some_0));
    lemma_acc_ok(c, s, no_facts(), i);
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    let tv = rr64(s, ch.t);
    let iv = rr64(s, ch.i);
    let b = c.bounds[ch.k];
    lemma_region(c, ch.k);
    assert(tv == iv + ch.n && iv + ch.n < p2(64));
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(cu, s, i, s2);
        let addr = c.ctx + abi::bound_off(ch.k);
        lemma_logext64_id(addr);
        assert(eff_addr(s, bm) == addr);
        assert(read_operand_mem(s, Size::W64, bm) == Some(b));
        let r = gpr_arith_logic_spec(64, AluOp::Cmp, tv, b, s.rflags);
        assert(r == gpr_sub_spec(64, tv, b, s.rflags));
        lemma_cmp64_flags(cu, s, tv, b);
        let e = effect(cu, s, i)->Some_0;
        assert(e == write_user_rflags(cu, s, r.rflags, r.undef));
        assert(s2 == write_ip(e, s.rip + instr_len(i) as int));
        assert(s2.rgf == s.rgf);
        lemma_base_inv_after(c, s, s2, None);
        lemma_facts_keep(c, s, s2, fsm, None);
        assert(mid_inv(c, s2, j0, fs0, 4));
        lemma_pos_mid(c, s, s2, j0, 3);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 4, `ja exit2`.
pub proof fn lemma_check_4(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 4),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 4]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 4]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 4], s2),
{
    lemma_check_prelude(c, s, j0, 4);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 4];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == Instr::Jcc { cc: 7, rel: ch.r2 });
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    let iv = rr64(s, ch.i);
    let tv = rr64(s, ch.t);
    let b = c.bounds[ch.k];
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        let end = s.rip + instr_len(i) as int;
        let taken = jcc_cmovcc_setcc_spec(s, 7);
        let target = if taken {
            end + ch.r2 as int
        } else {
            end
        };
        assert(add_to_ip(target, 0) is Some);
        assert(s2 == write_ip(s, target));
        lemma_base_inv_after(c, s, s2, None);
        lemma_confined_same(c, s, s2);
        lemma_start_of_succ(c.ins, j0 + 4);
        if taken {
            assert(jump_rel(i) == Some(ch.r2 as int));
            lemma_pos_jump(c, s, s2, j0 + 4);
        } else {
            assert(tv <= b);
            assert(iv + ch.n <= b);
            assert(mid_inv(c, s2, j0, fs0, 5));
            lemma_pos_mid(c, s, s2, j0, 4);
        }
        assert(inv(c, s2));
    }
}

/// Instruction 5, `mov z, 0`.
pub proof fn lemma_check_5(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 5),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 5]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 5]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 5], s2),
{
    lemma_check_prelude(c, s, j0, 5);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 5];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == Instr::MovImm32 { dst: ch.z, imm_u32: 0 });
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(cu, s, i, s2);
        lemma_base_inv_after(c, s, s2, Some(ch.z));
        lemma_facts_keep(c, s, s2, fsm, Some(ch.z));
        let e = effect(cu, s, i)->Some_0;
        assert(e == wr32(s, ch.z, 0));
        assert(s.rgf.len() == 16);
        assert(rr64(s2, ch.z) == 0);
        assert(rr64(s2, ch.i) == rr64(s, ch.i));
        assert(mid_inv(c, s2, j0, fs0, 6));
        lemma_pos_mid(c, s, s2, j0, 5);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 6, `cmp i, [r15 + bound]`.
pub proof fn lemma_check_6(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 6),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 6]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 6]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 6], s2),
{
    lemma_check_prelude(c, s, j0, 6);
    lemma_p2();
    lemma_base_inv_split(c, s);
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 6];
    let fsm = check_mid_facts(fs0, ch);
    let bm = bound_mem(ch.k);
    assert(i == Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: ch.i, mem: bm });
    lemma_no_facts_hold(c, s);
    assert(access_ok(no_facts(), mem_access(i)->Some_0));
    lemma_acc_ok(c, s, no_facts(), i);
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    let iv = rr64(s, ch.i);
    let b = c.bounds[ch.k];
    lemma_region(c, ch.k);
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(cu, s, i, s2);
        let addr = c.ctx + abi::bound_off(ch.k);
        lemma_logext64_id(addr);
        assert(eff_addr(s, bm) == addr);
        assert(read_operand_mem(s, Size::W64, bm) == Some(b));
        let r = gpr_arith_logic_spec(64, AluOp::Cmp, iv, b, s.rflags);
        assert(r == gpr_sub_spec(64, iv, b, s.rflags));
        lemma_cmp64_flags(cu, s, iv, b);
        let e = effect(cu, s, i)->Some_0;
        assert(e == write_user_rflags(cu, s, r.rflags, r.undef));
        assert(s2 == write_ip(e, s.rip + instr_len(i) as int));
        assert(s2.rgf == s.rgf);
        lemma_base_inv_after(c, s, s2, None);
        lemma_facts_keep(c, s, s2, fsm, None);
        assert(mid_inv(c, s2, j0, fs0, 7));
        lemma_pos_mid(c, s, s2, j0, 6);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 7, `cmovae i, z`, which does not move: the index is below the
/// bound.
pub proof fn lemma_check_7(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 7),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 7]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + 7]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 7], s2),
{
    lemma_check_prelude(c, s, j0, 7);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 7];
    assert(i == Instr::Cmovcc { cc: 3, sz: Size::W64, dst: ch.i, src: ch.z });
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    assert(!is_exit(c, s, i)) by {
        if is_exit(c, s, i) {
            lemma_is_exit_ret(c, s, i);
        }
    }
    let iv = rr64(s, ch.i);
    let b = c.bounds[ch.k];
    assert(iv + ch.n <= b);
    assert(iv < b);
    assert(flgi(s, cf_bit()) == 1);
    assert(!jcc_cmovcc_setcc_spec(s, 3));
    lemma_not_last(c, j0 + 7);
    assert forall|s2: State| step(cu, s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(cu, s, i, s2);
        assert(effect(cu, s, i) == Some(s));
        assert(s2 == write_ip(s, s.rip + instr_len(i) as int));
        assert(s2.rgf == s.rgf);
        lemma_base_inv_after(c, s, s2, None);
        lemma_check_facts_hold(c, s, s2, ch, fs0);
        assert(check_facts(fs0, c.ins, j0) == set_fact(
            set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.z, Fact::Unknown),
            ch.i,
            Fact::Idx(ch.k, ch.n),
        ));
        lemma_pos_fall(c, s, s2, j0, 7);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// **The bounds-check sequence**: at any of its eight positions, the
/// accesses of the next instruction are in bounds and its step keeps the
/// invariant.
pub proof fn lemma_check_unit(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + m]),
        forall|s2: State|
            step(cu, s, c.ins[j0 + m]) == Some(s2) ==> step_post(c, s, c.ins[j0 + m], s2),
{
    lemma_check_prelude(c, s, j0, m);
    if m == 0 {
        lemma_check_0(c, cu, s, j0);
    } else if m == 1 {
        lemma_check_1(c, cu, s, j0);
    } else if m == 2 {
        lemma_check_2(c, cu, s, j0);
    } else if m == 3 {
        lemma_check_3(c, cu, s, j0);
    } else if m == 4 {
        lemma_check_4(c, cu, s, j0);
    } else if m == 5 {
        lemma_check_5(c, cu, s, j0);
    } else if m == 6 {
        lemma_check_6(c, cu, s, j0);
    } else {
        lemma_check_7(c, cu, s, j0);
    }
}

} // verus!
