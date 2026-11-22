//! **The bounds-check sequence** (A64, seven instructions, [`check_instr`]):
//! each step keeps the invariant [`check_mid`] describes, and after the last
//! the index register is checked ([`Fact::Idx`]) for the region. This is where
//! the carry and zero flags are used: `b.hs` falls through only if the `adds`
//! did not wrap, `b.hi` only if the sum is at most the bound, and the final
//! `csel ..., lo` does not move because the index is below the bound.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The fact of register `r` under [`check_mid_facts`].
pub proof fn lemma_fact_of_mid(fs0: Facts, ch: Chk, r: u8)
    ensures
        fact_of(check_mid_facts(fs0, ch), r) == if r == ch.t || r == ch.bnd || r == ch.i {
            Fact::Unknown
        } else {
            fact_of(fs0, r)
        },
{
    let a = set_fact(fs0, ch.t, Fact::Unknown);
    let b = set_fact(a, ch.bnd, Fact::Unknown);
    crate::a64::unit_exec::lemma_fact_of_set(fs0, ch.t, Fact::Unknown, r);
    crate::a64::unit_exec::lemma_fact_of_set(a, ch.bnd, Fact::Unknown, r);
    crate::a64::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Unknown, r);
}

/// The fact of register `r` after the check ([`check_facts`]).
pub proof fn lemma_fact_of_fin(fs0: Facts, ch: Chk, r: u8)
    ensures
        fact_of(
            set_fact(
                set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.bnd, Fact::Unknown),
                ch.i,
                Fact::Idx(ch.k, ch.n),
            ),
            r,
        ) == if r == ch.i {
            Fact::Idx(ch.k, ch.n)
        } else if r == ch.t || r == ch.bnd {
            Fact::Unknown
        } else {
            fact_of(fs0, r)
        },
{
    let a = set_fact(fs0, ch.t, Fact::Unknown);
    let b = set_fact(a, ch.bnd, Fact::Unknown);
    crate::a64::unit_exec::lemma_fact_of_set(fs0, ch.t, Fact::Unknown, r);
    crate::a64::unit_exec::lemma_fact_of_set(a, ch.bnd, Fact::Unknown, r);
    crate::a64::unit_exec::lemma_fact_of_set(b, ch.i, Fact::Idx(ch.k, ch.n), r);
}

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
                Unit { len: 7, facts: check_facts(fs0, c.ins, j0) },
            ) && 0 <= m < 7 && c.ins[j0 + m] == check_instr(m, ch) && (forall|q: int|
                0 <= q < 7 ==> #[trigger] c.ins[j0 + q] == check_instr(q, ch)) && ch.t < 31
                && ch.i < 31 && ch.bnd < 31 && facts_hold(c, s, check_mid_facts(fs0, ch))
                && base_inv(c, s) && mem_read(s.mem, c.ctx + abi::bound_off(ch.k), 8) == Some(
                c.bounds[ch.k],
            ) && 0 <= ch.k < abi::num_regions() && 1 <= ch.n <= 8 && (m > 0 ==> check_mid(
                c,
                s,
                ch,
                fs0,
                m,
            )) && (m == 0 ==> facts_hold(c, s, fs0))
        }),
{
    lemma_cur_instr(c, s, j0, m);
    lemma_base_inv_split(c, s);
    lemma_cfg(c);
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let u = unit_at(c.ins, j0, fs0)->Some_0;
    assert(u == (Unit { len: 7, facts: check_facts(fs0, c.ins, j0) }));
    assert(check_ok(ch));
    assert(c.ins[j0 + 0] == check_instr(0, ch));
    assert(c.ins[j0 + 1] == check_instr(1, ch));
    assert(c.ins[j0 + 2] == check_instr(2, ch));
    assert(c.ins[j0 + 3] == check_instr(3, ch));
    assert(c.ins[j0 + 4] == check_instr(4, ch));
    assert(c.ins[j0 + 5] == check_instr(5, ch));
    assert(c.ins[j0 + 6] == check_instr(6, ch));
    let fsm = check_mid_facts(fs0, ch);
    let a = set_fact(fs0, ch.t, Fact::Unknown);
    let b = set_fact(a, ch.bnd, Fact::Unknown);
    if m == 0 {
        lemma_facts_unknown(c, s, fs0, ch.t);
        lemma_facts_unknown(c, s, a, ch.bnd);
        lemma_facts_unknown(c, s, b, ch.i);
    }
    assert(mem_read(s.mem, c.ctx + abi::bound_off(ch.k), 8) == Some(c.bounds[ch.k]));
}

/// The scan's facts after the bounds check hold, if the check's own
/// invariant does and the registers are as at the end.
pub proof fn lemma_check_facts_hold(c: Cfg, s: State, s2: State, ch: Chk, fs0: Facts)
    requires
        facts_hold(c, s, check_mid_facts(fs0, ch)),
        check_ok(ch),
        s2.r == s.r,
        0 <= ch.k < abi::num_regions(),
        x_read(s, ch.i, 64) + ch.n <= c.bounds[ch.k],
        s.r.len() == 31,
    ensures
        facts_hold(
            c,
            s2,
            set_fact(
                set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.bnd, Fact::Unknown),
                ch.i,
                Fact::Idx(ch.k, ch.n),
            ),
        ),
{
    let fin = set_fact(
        set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.bnd, Fact::Unknown),
        ch.i,
        Fact::Idx(ch.k, ch.n),
    );
    let fsm = check_mid_facts(fs0, ch);
    assert forall|r: u8| r < 32 implies fact_ok(c, s2, r, #[trigger] fact_of(fin, r)) by {
        lemma_fact_of_fin(fs0, ch, r);
        lemma_fact_of_mid(fs0, ch, r);
        assert(fact_ok(c, s, r, fact_of(fsm, r)));
        if r == ch.i {
            assert(x_read(s2, r, 64) == x_read(s, r, 64));
        } else if r == ch.t || r == ch.bnd {
        } else {
            assert(x_read(s2, r, 64) == x_read(s, r, 64));
        }
    }
}

/// Instruction 0 of a bounds check, `ldr bnd, [x28, #(16k + 8)]`.
pub proof fn lemma_check_0(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 0),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0]),
        forall|s2: State| step(s, c.ins[j0]) == Some(s2) ==> step_post(c, s, c.ins[j0], s2),
{
    lemma_check_prelude(c, s, j0, 0);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0];
    let fsm = check_mid_facts(fs0, ch);
    let imm12 = (abi::bound_off(ch.k) / 8) as u16;
    assert(i == (Instr::LoadStoreImm {
        sf: Width::W64,
        load: true,
        t: ch.bnd,
        n: abi::ctx_reg(),
        imm12,
    }));
    assert(imm12 as int * 8 == abi::bound_off(ch.k));
    lemma_no_facts_hold(c, s);
    assert(access_ok(no_facts(), mem_access(i)->Some_0));
    lemma_acc_ok(c, s, no_facts(), i);
    lemma_not_exit(c, s, i);
    lemma_region(c, ch.k);
    lemma_base_inv_split(c, s);
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(s, i, s2);
        lemma_pc_succ(c, s, s2, j0, 0);
        lemma_xr(s, abi::ctx_reg());
        let addr = c.ctx + abi::bound_off(ch.k);
        assert(0 <= addr < p2(64));
        lemma_trunc64_id(addr);
        assert(mem_read(s.mem, addr, 8) == Some(c.bounds[ch.k]));
        let s1 = execute(s, i)->Some_0;
        lemma_trunc64_id(c.bounds[ch.k]);
        assert(s1 == x_set(s, ch.bnd, 64, c.bounds[ch.k]));
        assert(s2.flag_c == s.flag_c && s2.flag_z == s.flag_z);
        assert(written_gpr(i) == Some(ch.bnd));
        lemma_base_inv_after(c, s, s2, Some(ch.bnd));
        lemma_fact_of_mid(fs0, ch, ch.bnd);
        lemma_facts_keep(c, s, s2, fsm, Some(ch.bnd));
        lemma_xr(s2, ch.bnd);
        assert(x_read(s2, ch.bnd, 64) == c.bounds[ch.k]);
        assert(mid_inv(c, s2, j0, fs0, 1));
        lemma_pos_mid(c, s, s2, j0, 0);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 1, `adds t, i, #n`.
pub proof fn lemma_check_1(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 1),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 1]),
        forall|s2: State| step(s, c.ins[j0 + 1]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 1], s2),
{
    lemma_check_prelude(c, s, j0, 1);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 1];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == (Instr::AddSubImm {
        sf: Width::W64,
        sub_op: false,
        setflags: true,
        d: ch.t,
        n: ch.i,
        imm12: ch.n as u16,
        sh: false,
    }));
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    lemma_not_exit(c, s, i);
    lemma_xr(s, ch.i);
    let iv = x_read(s, ch.i, 64);
    let n = ch.n;
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(s, i, s2);
        lemma_pc_succ(c, s, s2, j0, 1);
        assert(written_gpr(i) == Some(ch.t));
        lemma_base_inv_after(c, s, s2, Some(ch.t));
        lemma_fact_of_mid(fs0, ch, ch.t);
        lemma_facts_keep(c, s, s2, fsm, Some(ch.t));
        lemma_adds_effect(s, i, ch.t, ch.i, ch.n as u16, s2);
        assert(ch.n as u16 as int == ch.n);
        lemma_xr(s2, ch.t);
        lemma_xr(s2, ch.i);
        lemma_xr(s2, ch.bnd);
        assert(s2.r[ch.t as int] == (((iv + n) % p2(64)) as u64));
        vstd::arithmetic::div_mod::lemma_mod_bound(iv + n, p2(64));
        assert(x_read(s2, ch.t, 64) == (iv + n) % p2(64));
        assert(x_read(s2, ch.i, 64) == iv);
        assert(x_read(s2, ch.bnd, 64) == x_read(s, ch.bnd, 64));
        assert(mid_inv(c, s2, j0, fs0, 2));
        lemma_pos_mid(c, s, s2, j0, 1);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 2, `b.hs exit1`.
pub proof fn lemma_check_2(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 2),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 2]),
        forall|s2: State| step(s, c.ins[j0 + 2]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 2], s2),
{
    lemma_check_prelude(c, s, j0, 2);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 2];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == (Instr::BCond { cond: 2, imm19: ch.r1 }));
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    lemma_not_exit(c, s, i);
    lemma_base_inv_split(c, s);
    lemma_xr(s, ch.i);
    lemma_xr(s, ch.t);
    let iv = x_read(s, ch.i, 64);
    let tv = x_read(s, ch.t, 64);
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        assert(condition_holds(s, 2) == s.flag_c);
        lemma_confined_same_branch(c, s, s2, i);
        lemma_base_inv_after(c, s, s2, None);
        lemma_confined_same(c, s, s2);
        if s.flag_c {
            assert(s2 == branch_to(s, s.pc as int + ch.r1 as int * 4));
            assert(jump_rel(i) == Some(ch.r1 as int * 4));
            lemma_pos_jump(c, s, s2, j0 + 2);
        } else {
            assert(s2 == branch_to(s, s.pc as int + 4));
            lemma_pc_succ(c, s, s2, j0, 2);
            lemma_facts_keep(c, s, s2, fsm, None);
            assert(iv + ch.n < p2(64));
            assert(tv == iv + ch.n) by {
                vstd::arithmetic::div_mod::lemma_small_mod((iv + ch.n) as nat, p2(64) as nat);
            }
            lemma_xr(s2, ch.i);
            lemma_xr(s2, ch.t);
            lemma_xr(s2, ch.bnd);
            assert(mid_inv(c, s2, j0, fs0, 3));
            lemma_pos_mid(c, s, s2, j0, 2);
        }
        assert(inv(c, s2));
    }
}

/// Instruction 3, `cmp t, bnd`.
pub proof fn lemma_check_3(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 3),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 3]),
        forall|s2: State| step(s, c.ins[j0 + 3]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 3], s2),
{
    lemma_check_prelude(c, s, j0, 3);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 3];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == (Instr::AddSubShiftedReg {
        sf: Width::W64,
        sub_op: true,
        setflags: true,
        d: abi::sp_reg(),
        n: ch.t,
        m: ch.bnd,
        shift_type: ShiftType::Lsl,
        shift_amount: 0,
    }));
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    lemma_not_exit(c, s, i);
    lemma_xr(s, ch.t);
    lemma_xr(s, ch.bnd);
    lemma_region(c, ch.k);
    let tv = x_read(s, ch.t, 64);
    let bv = x_read(s, ch.bnd, 64);
    let b = c.bounds[ch.k];
    assert(bv == b);
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(s, i, s2);
        lemma_pc_succ(c, s, s2, j0, 3);
        assert(written_gpr(i) == Some(31u8));
        lemma_cmp_effect(s, i, ch.t, ch.bnd, s2);
        lemma_base_inv_after(c, s, s2, Some(31u8));
        lemma_facts_keep(c, s, s2, fsm, None);
        lemma_xr(s2, ch.i);
        lemma_xr(s2, ch.t);
        lemma_xr(s2, ch.bnd);
        assert(mid_inv(c, s2, j0, fs0, 4));
        lemma_pos_mid(c, s, s2, j0, 3);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 4, `b.hi exit2`.
pub proof fn lemma_check_4(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 4),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 4]),
        forall|s2: State| step(s, c.ins[j0 + 4]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 4], s2),
{
    lemma_check_prelude(c, s, j0, 4);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 4];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == (Instr::BCond { cond: 8, imm19: ch.r2 }));
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    lemma_not_exit(c, s, i);
    lemma_base_inv_split(c, s);
    lemma_xr(s, ch.i);
    lemma_xr(s, ch.t);
    let iv = x_read(s, ch.i, 64);
    let tv = x_read(s, ch.t, 64);
    let b = c.bounds[ch.k];
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        assert(condition_holds(s, 8) == (s.flag_c && !s.flag_z));
        lemma_confined_same_branch(c, s, s2, i);
        lemma_base_inv_after(c, s, s2, None);
        lemma_confined_same(c, s, s2);
        if s.flag_c && !s.flag_z {
            assert(s2 == branch_to(s, s.pc as int + ch.r2 as int * 4));
            assert(jump_rel(i) == Some(ch.r2 as int * 4));
            lemma_pos_jump(c, s, s2, j0 + 4);
        } else {
            assert(s2 == branch_to(s, s.pc as int + 4));
            lemma_pc_succ(c, s, s2, j0, 4);
            lemma_facts_keep(c, s, s2, fsm, None);
            assert(tv <= b);
            assert(iv + ch.n <= b);
            lemma_xr(s2, ch.i);
            lemma_xr(s2, ch.t);
            lemma_xr(s2, ch.bnd);
            assert(mid_inv(c, s2, j0, fs0, 5));
            lemma_pos_mid(c, s, s2, j0, 4);
        }
        assert(inv(c, s2));
    }
}

/// Instruction 5, `cmp i, bnd`.
pub proof fn lemma_check_5(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 5),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 5]),
        forall|s2: State| step(s, c.ins[j0 + 5]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 5], s2),
{
    lemma_check_prelude(c, s, j0, 5);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 5];
    let fsm = check_mid_facts(fs0, ch);
    assert(i == (Instr::AddSubShiftedReg {
        sf: Width::W64,
        sub_op: true,
        setflags: true,
        d: abi::sp_reg(),
        n: ch.i,
        m: ch.bnd,
        shift_type: ShiftType::Lsl,
        shift_amount: 0,
    }));
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    lemma_not_exit(c, s, i);
    lemma_xr(s, ch.i);
    lemma_xr(s, ch.bnd);
    lemma_region(c, ch.k);
    let iv = x_read(s, ch.i, 64);
    let bv = x_read(s, ch.bnd, 64);
    let b = c.bounds[ch.k];
    assert(bv == b);
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(s, i, s2);
        lemma_pc_succ(c, s, s2, j0, 5);
        assert(written_gpr(i) == Some(31u8));
        lemma_cmp_effect(s, i, ch.i, ch.bnd, s2);
        lemma_base_inv_after(c, s, s2, Some(31u8));
        lemma_facts_keep(c, s, s2, fsm, None);
        lemma_xr(s2, ch.i);
        lemma_xr(s2, ch.t);
        lemma_xr(s2, ch.bnd);
        assert(mid_inv(c, s2, j0, fs0, 6));
        lemma_pos_mid(c, s, s2, j0, 5);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// Instruction 6, `csel i, i, xzr, lo`, which does not move: the index is
/// below the bound.
pub proof fn lemma_check_6(c: Cfg, s: State, j0: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, 6),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + 6]),
        forall|s2: State| step(s, c.ins[j0 + 6]) == Some(s2) ==> step_post(c, s, c.ins[j0 + 6], s2),
{
    lemma_check_prelude(c, s, j0, 6);
    lemma_cfg(c);
    lemma_p2();
    let fs0 = start_facts(c, j0)->Some_0;
    let ch = check_params(c.ins, j0)->Some_0;
    let i = c.ins[j0 + 6];
    assert(i == (Instr::CondSelect {
        sf: Width::W64,
        else_inv: false,
        else_inc: false,
        d: ch.i,
        n: ch.i,
        m: abi::sp_reg(),
        cond: 3,
    }));
    assert(mem_access(i) is None);
    assert(acc_ok(c, s, i));
    lemma_not_exit(c, s, i);
    lemma_base_inv_split(c, s);
    lemma_xr(s, ch.i);
    let iv = x_read(s, ch.i, 64);
    let b = c.bounds[ch.k];
    assert(iv + ch.n <= b);
    assert(iv < b);
    assert(!s.flag_c);
    assert(condition_holds(s, 3));
    lemma_not_last(c, j0 + 6);
    assert forall|s2: State| step(s, i) == Some(s2) implies step_post(c, s, i, s2) by {
        lemma_step_straight(s, i, s2);
        lemma_pc_succ(c, s, s2, j0, 6);
        assert(execute(s, i) == Some(x_set(s, ch.i, 64, iv)));
        lemma_trunc64_id(iv);
        assert(s2.r =~= s.r);
        assert(written_gpr(i) == Some(ch.i));
        lemma_base_inv_after(c, s, s2, Some(ch.i));
        lemma_check_facts_hold(c, s, s2, ch, fs0);
        assert(check_facts(fs0, c.ins, j0) == set_fact(
            set_fact(set_fact(fs0, ch.t, Fact::Unknown), ch.bnd, Fact::Unknown),
            ch.i,
            Fact::Idx(ch.k, ch.n),
        ));
        lemma_pos_fall(c, s, s2, j0, 6);
        lemma_confined_same(c, s, s2);
        assert(inv(c, s2));
    }
}

/// **The bounds-check sequence**: at any of its seven positions, the
/// accesses of the next instruction are in bounds and its step keeps the
/// invariant.
pub proof fn lemma_check_unit(c: Cfg, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
        !exit_unit_at(c.ins, j0),
        check_unit_at(c.ins, j0),
    ensures
        acc_ok(c, s, c.ins[j0 + m]),
        forall|s2: State| step(s, c.ins[j0 + m]) == Some(s2) ==> step_post(c, s, c.ins[j0 + m], s2),
{
    lemma_check_prelude(c, s, j0, m);
    if m == 0 {
        lemma_check_0(c, s, j0);
    } else if m == 1 {
        lemma_check_1(c, s, j0);
    } else if m == 2 {
        lemma_check_2(c, s, j0);
    } else if m == 3 {
        lemma_check_3(c, s, j0);
    } else if m == 4 {
        lemma_check_4(c, s, j0);
    } else if m == 5 {
        lemma_check_5(c, s, j0);
    } else {
        lemma_check_6(c, s, j0);
    }
}

} // verus!
