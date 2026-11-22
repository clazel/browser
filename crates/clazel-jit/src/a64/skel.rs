//! The skeleton every storing template shares: *loads, a register-only middle,
//! one store*. [`lemma_loads`] runs the loads, and [`lemma_shape`] puts the
//! three parts together: given a middle that leaves the result word in `x0`
//! (the hypothesis, proven per template in [`super::mid`] and
//! [`super::bitmid`]), the whole template takes a state related to `a` to a
//! state related to the next LIR state `a2`. The A64 counterpart of
//! [`crate::skel`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The loads in `ls` read distinct scratch registers from existing slots.
pub open spec fn loads_ok(ls: Seq<(u8, nat)>, nl: nat, n: nat) -> bool {
    (forall|k: int|
        0 <= k < ls.len() ==> super::rel::scratch((#[trigger] ls[k]).0) && ls[k].1 < nl + n) && (forall|
        k1: int,
        k2: int,
    |
        0 <= k1 < k2 < ls.len() ==> (#[trigger] ls[k1]).0 != (#[trigger] ls[k2]).0)
}

/// What the middle of a template is started from: a well-formed state whose
/// registers hold the words the loads `ls` would have put there, with room
/// for the middle before the address space ends.
pub open spec fn mid_pre(
    a: lir::St,
    nl: nat,
    ls: Seq<(u8, nat)>,
    mid: Seq<isa::Instr>,
    s: isa::State,
) -> bool {
    isa::wf(s) && (forall|k: int|
        0 <= k < ls.len() ==> (#[trigger] s.r[ls[k].0 as int]) as nat == lir::val_bits(
            slot_val(a, nl, ls[k].1),
        )) && (s.pc as int) + code_len(mid) < 0x1_0000_0000_0000_0000
}

/// What the middle must do from there: not fault, and leave `w` in `x0`
/// changing only scratch registers, flags and `pc` ([`super::mid::mid_post`]).
pub open spec fn mid_goal(mid: Seq<isa::Instr>, w: nat, s: isa::State) -> bool {
    run_seq(s, mid) is Some && super::mid::mid_post(
        s,
        run_seq(s, mid).unwrap(),
        x0(),
        w,
        code_len(mid),
    )
}

/// The middle satisfies [`mid_goal`] from every state satisfying [`mid_pre`].
pub open spec fn mid_prop(
    a: lir::St,
    nl: nat,
    ls: Seq<(u8, nat)>,
    mid: Seq<isa::Instr>,
    w: nat,
) -> bool {
    forall|s: isa::State|
        #![trigger mid_goal(mid, w, s)]
        mid_pre(a, nl, ls, mid, s) ==> mid_goal(mid, w, s)
}

/// The loads `ls` run from a related state: no fault, each register holds its
/// slot's word, the relation still holds, and nothing but those registers and
/// `pc` changed.
#[verifier::rlimit(1000)]
pub proof fn lemma_loads(lay: lir::Layout, a: lir::St, m: isa::State, ls: Seq<(u8, nat)>, nl: nat)
    requires
        rel(lay, a, m, nl),
        loads_ok(ls, nl, a.stack.len()),
        (m.pc as int) + code_len(super::templates::loads_seq(ls)) < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(m, super::templates::loads_seq(ls)) is Some,
        ({
            let m1 = run_seq(m, super::templates::loads_seq(ls)).unwrap();
            &&& rel(lay, a, m1, nl)
            &&& m1.pc as int == m.pc as int + code_len(super::templates::loads_seq(ls))
            &&& m1.mem == m.mem
            &&& m1.r.len() == 31
            &&& m1.vreg == m.vreg
            &&& m1.r[abi::ctx_reg() as int] == m.r[abi::ctx_reg() as int]
            &&& m1.r[abi::link_reg() as int] == m.r[abi::link_reg() as int]
            &&& m1.sp == m.sp
            &&& forall|k: int|
                0 <= k < ls.len() ==> (#[trigger] m1.r[ls[k].0 as int]) as nat == lir::val_bits(
                    slot_val(a, nl, ls[k].1),
                )
        }),
    decreases ls.len(),
{
    super::steps::lemma_abi_consts();
    if ls.len() == 0 {
        assert(super::templates::loads_seq(ls) =~= seq![]);
    } else {
        let pre = ls.drop_last();
        let last = ls.last();
        let a_code = super::templates::loads_seq(pre);
        let b_code = seq![super::templates::load_slot(last.0, last.1)];
        assert(super::templates::loads_seq(ls) == a_code + b_code);
        assert(loads_ok(pre, nl, a.stack.len())) by {
            assert forall|k: int| 0 <= k < pre.len() implies super::rel::scratch((#[trigger] pre[k]).0)
                && pre[k].1 < nl + a.stack.len() by {
                assert(pre[k] == ls[k]);
            }
            assert forall|k1: int, k2: int|
                0 <= k1 < k2 < pre.len() implies (#[trigger] pre[k1]).0 != (#[trigger] pre[k2]).0 by {
                assert(pre[k1] == ls[k1] && pre[k2] == ls[k2]);
            }
        }
        lemma_loads(lay, a, m, pre, nl);
        let m1 = run_seq(m, a_code).unwrap();
        super::runseq::lemma_run_seq_append(m, a_code, b_code);
        assert(super::rel::scratch(last.0) && last.1 < nl + a.stack.len());
        super::rel::lemma_load_rel(lay, a, m1, last.0, last.1, nl);
        super::runseq::lemma_run_seq_one(m1, super::templates::load_slot(last.0, last.1));
        let m2 = isa::step(m1, super::templates::load_slot(last.0, last.1)).unwrap();
        assert(m2.r.len() == 31);
        assert(m2.vreg == m1.vreg);
        assert forall|k: int| 0 <= k < ls.len() implies (#[trigger] m2.r[ls[k].0 as int]) as nat
            == lir::val_bits(slot_val(a, nl, ls[k].1)) by {
            if k < ls.len() - 1 {
                assert(pre[k] == ls[k]);
                assert(ls[k].0 != last.0);
            }
        }
    }
}

/// **A whole template**: loads, middle, store. From a related state, the code
/// does not fault and ends in a state related to the next LIR state, `pc`
/// after the code, only the exit area changed.
#[verifier::rlimit(500)]
pub proof fn lemma_shape(
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: isa::State,
    nl: nat,
    ls: Seq<(u8, nat)>,
    mid: Seq<isa::Instr>,
    ts: nat,
    w: nat,
)
    requires
        rel(lay, a, m, nl),
        loads_ok(ls, nl, a.stack.len()),
        (m.pc as int) + code_len(super::templates::shape(ls, mid, ts)) < 0x1_0000_0000_0000_0000,
        ts < max_slots(),
        crate::rel::slots_agree_except(a, a2, nl, ts),
        w == lir::val_bits(slot_val(a2, nl, ts)),
        mid_prop(a, nl, ls, mid, w),
    ensures
        run_seq(m, super::templates::shape(ls, mid, ts)) is Some,
        ({
            let m4 = run_seq(m, super::templates::shape(ls, mid, ts)).unwrap();
            &&& rel(lay, a2, m4, nl)
            &&& m4.pc as int == m.pc as int + code_len(super::templates::shape(ls, mid, ts))
            &&& preserved(m, m4)
        }),
{
    super::steps::lemma_abi_consts();
    super::steps::lemma_frame_agrees();
    let ld = super::templates::loads_seq(ls);
    let st = seq![super::templates::store_slot(ts, x0())];
    assert(super::templates::shape(ls, mid, ts) == (ld + mid) + st);
    lemma_loads(lay, a, m, ls, nl);
    let m1 = run_seq(m, ld).unwrap();
    // the middle
    assert(isa::wf(m1));
    assert(mid_pre(a, nl, ls, mid, m1));
    assert(mid_goal(mid, w, m1));
    let m3 = run_seq(m1, mid).unwrap();
    super::runseq::lemma_run_seq_append(m, ld, mid);
    super::runseq::lemma_run_seq_append(m, ld + mid, st);
    super::rel::lemma_rel_regs(lay, a, m1, m3, nl);
    // the store
    assert(m3.pc as int + 4 < 0x1_0000_0000_0000_0000);
    super::rel::lemma_store_finish(lay, a, a2, m, m3, nl, ts, x0(), w);
    super::runseq::lemma_run_seq_one(m3, super::templates::store_slot(ts, x0()));
}

} // verus!
