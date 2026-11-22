//! **The proof of the x86-64 confinement theorem** ([`x64_confinement`]) and
//! of its corollary over finite executions ([`x64_run_confinement`]).
//!
//! [`lemma_step_conf`] is the theorem at one position: it dispatches on the
//! unit that starts at `j0` (the exit sequence, `super::steps`; the bounds
//! check, `super::check`; or a single instruction, `super::steps`).
//! [`theorem_x64`] quantifies it away; [`lemma_entry_inv`] says the invariant
//! holds at every accepted entry given the context invariant;
//! [`theorem_x64_runs`] is the induction over an execution.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// **The theorem at one position**: from the invariant at `(j0, m)`, the step
/// is confined.
pub proof fn lemma_step_conf(c: Cfg, cu: spec_fn(nat) -> nat, s: State, j0: int, m: int)
    requires
        cfg_ok(c),
        pos_inv(c, s, j0, m),
    ensures
        confined_step::<X64>(c, cu, s),
{
    lemma_cur_instr(c, s, j0, m);
    let i = c.ins[j0 + m];
    lemma_not_system(i);
    if exit_unit_at(c.ins, j0) {
        lemma_exit_unit(c, cu, s, j0, m);
    } else if check_unit_at(c.ins, j0) {
        lemma_check_unit(c, cu, s, j0, m);
    } else {
        lemma_plain_unit(c, cu, s, j0, m);
    }
    assert(inv(c, s));
    lemma_base_inv_split(c, s);
    lemma_reads_confined(c, cu, s, i);
    match step(cu, s, i) {
        None => {},
        Some(s2) => {
            assert(step_post(c, s, i, s2));
        },
    }
}

/// **The x86-64 confinement theorem** ([`x64_confinement`]).
pub proof fn theorem_x64()
    ensures
        x64_confinement(),
{
    assert forall|c: Cfg, e: spec_fn(nat) -> nat, s: State| cfg_ok(c) implies #[trigger] confined_step::<
        X64,
    >(c, e, s) by {
        if inv(c, s) {
            let (j0, m) = choose|j0: int, m: int| pos_inv(c, s, j0, m);
            lemma_step_conf(c, e, s, j0, m);
        }
    }
}

/// **The invariant holds at every accepted entry**, given the context
/// invariant: a state whose registers, memory and RIP are as the
/// configuration says, with RIP at an entry the validator accepted, satisfies
/// [`inv`]. (This is the hypothesis "started at an accepted entry with the
/// context invariant" of jit.md exit criterion 2.)
pub proof fn lemma_entry_inv(c: Cfg, s: State, e: int)
    requires
        cfg_ok(c),
        seq_has(c.entries, e),
        base_inv(c, s),
        s.rip == c.code + e,
    ensures
        inv(c, s),
{
    lemma_entry_is_start(c, e);
    let t = choose|t: int|
        0 <= t < c.ins.len() && e == start_of(c.ins, t) && start_facts(c, t) is Some
            && start_facts(c, t)->Some_0 == no_facts();
    lemma_unit_ok(c, t, no_facts());
    lemma_no_facts_hold(c, s);
    assert(pos_inv(c, s, t, 0));
}

/// The induction over an execution: every state but the last satisfies the
/// invariant, and the last does or was entered by the exit.
pub proof fn lemma_run_inv(
    c: Cfg,
    e: spec_fn(nat) -> nat,
    ex: Seq<State>,
    k: int,
)
    requires
        cfg_ok(c),
        ex.len() > 0,
        is_run::<X64>(c, e, ex),
        inv(c, ex[0]),
        0 <= k < ex.len(),
    ensures
        inv(c, ex[k]) || (k >= 1 && exited(c, ex[k]) && exists|i: Instr|
            is_exit(c, ex[k - 1], i) && next_instr(c, ex[k - 1]) == Some(i)),
        k + 1 < ex.len() ==> inv(c, ex[k]),
    decreases k,
{
    if k > 0 {
        lemma_run_inv(c, e, ex, k - 1);
        assert(inv(c, ex[k - 1]));
        assert(steps_to::<X64>(c, e, ex[k - 1], ex[k]));
        let i = choose|i: Instr|
            next_instr(c, ex[k - 1]) == Some(i) && #[trigger] step(e, ex[k - 1], i) == Some(ex[k]);
        let sp = ex[k - 1];
        let (j0, m) = choose|j0: int, m: int| pos_inv(c, sp, j0, m);
        lemma_step_conf(c, e, sp, j0, m);
        assert(confined_step::<X64>(c, e, ex[k - 1]));
        if is_exit(c, ex[k - 1], i) {
            assert(exited(c, ex[k]) && next_instr(c, ex[k]) is None);
            if k + 1 < ex.len() {
                assert(steps_to::<X64>(c, e, ex[k], ex[k + 1]));
                assert(false);
            }
        }
    }
}

/// **The corollary over every finite x86-64 execution** ([`x64_run_confinement`]).
pub proof fn theorem_x64_runs()
    ensures
        x64_run_confinement(),
{
    assert forall|c: Cfg, e: spec_fn(nat) -> nat, ex: Seq<State>|
        cfg_ok(c) && ex.len() > 0 && #[trigger] is_run::<X64>(c, e, ex) && inv(c, ex[0]) implies run_confined::<
        X64,
    >(c, ex) by {
        assert forall|k: int| 0 <= k && k + 1 < ex.len() implies #[trigger] inv(c, ex[k]) by {
            lemma_run_inv(c, e, ex, k);
        }
        lemma_run_inv(c, e, ex, ex.len() - 1);
    }
}

} // verus!
