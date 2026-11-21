//! The skeleton every storing template shares: *loads, a register-only middle,
//! one store*. [`lemma_loads`] runs the loads, and [`lemma_shape`] puts the
//! three parts together: given a middle that leaves the result word in `rax`
//! (the hypothesis, proven per template in [`crate::mid`]), the whole template
//! takes a state related to `a` to a state related to the next LIR state `a2`.

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
/// registers hold the words the loads `ls` would have put there.
pub open spec fn mid_pre(
    a: lir::St,
    nl: nat,
    ls: Seq<(u8, nat)>,
    mid: Seq<x64::Instr>,
    s: x64::State,
) -> bool {
    x64::wf(s) && s.rgf.len() == 16 && (forall|k: int|
        0 <= k < ls.len() ==> (#[trigger] s.rgf[ls[k].0 as int]) as nat == lir::val_bits(
            slot_val(a, nl, ls[k].1),
        )) && x64::canonical(s.rip + code_len(mid))
}

/// What the middle must do from there: not fault, and leave `w` in `rax`
/// changing only scratch registers and `rip` ([`mid_post`]).
pub open spec fn mid_goal(
    cu: spec_fn(nat) -> nat,
    mid: Seq<x64::Instr>,
    w: nat,
    s: x64::State,
) -> bool {
    run_seq(cu, s, mid) is Some && super::alu::mid_post(
        s,
        run_seq(cu, s, mid).unwrap(),
        rax(),
        w,
        code_len(mid),
    )
}

/// The middle does what it must from every state it can be started from.
pub open spec fn mid_prop(
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    nl: nat,
    ls: Seq<(u8, nat)>,
    mid: Seq<x64::Instr>,
    w: nat,
) -> bool {
    forall|s: x64::State|
        #![trigger mid_goal(cu, mid, w, s)]
        mid_pre(a, nl, ls, mid, s) ==> mid_goal(cu, mid, w, s)
}

/// Running the loads `ls`: each register holds its slot's word, and the state
/// is still related to `a`, with the same memory.
#[verifier::rlimit(1000)]
pub proof fn lemma_loads(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    a: lir::St,
    m: x64::State,
    ls: Seq<(u8, nat)>,
    nl: nat,
)
    requires
        rel(lay, a, m, nl),
        loads_ok(ls, nl, a.stack.len()),
        x64::canonical(m.rip + code_len(super::templates::loads_seq(ls))),
    ensures
        run_seq(cu, m, super::templates::loads_seq(ls)) is Some,
        ({
            let m1 = run_seq(cu, m, super::templates::loads_seq(ls)).unwrap();
            &&& rel(lay, a, m1, nl)
            &&& m1.rip == m.rip + code_len(super::templates::loads_seq(ls))
            &&& m1.mem == m.mem
            &&& m1.rgf.len() == 16
            &&& m1.xmm.len() == 16
            &&& m1.rgf[abi::ctx_reg() as int] == m.rgf[abi::ctx_reg() as int]
            &&& m1.rgf[abi::sp_reg() as int] == m.rgf[abi::sp_reg() as int]
            &&& forall|k: int|
                0 <= k < ls.len() ==> (#[trigger] m1.rgf[ls[k].0 as int]) as nat == lir::val_bits(
                    slot_val(a, nl, ls[k].1),
                )
        }),
    decreases ls.len(),
{
    super::steps::lemma_abi_consts();
    if ls.len() == 0 {
        assert(super::templates::loads_seq(ls) =~= seq![]);
        assert(code_len(Seq::<x64::Instr>::empty()) == 0);
    } else {
        let pre = ls.drop_last();
        let last = ls.last();
        let a_code = super::templates::loads_seq(pre);
        let b_code = seq![super::templates::load_slot(last.0, last.1)];
        assert(super::templates::loads_seq(ls) == a_code + b_code);
        super::runseq::lemma_code_len_append(a_code, b_code);
        super::runseq::lemma_code_len_one(super::templates::load_slot(last.0, last.1));
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
        lemma_loads(cu, lay, a, m, pre, nl);
        let m1 = run_seq(cu, m, a_code).unwrap();
        super::runseq::lemma_run_seq_append(cu, m, a_code, b_code);
        assert(super::rel::scratch(last.0) && last.1 < nl + a.stack.len());
        super::rel::lemma_load_rel(cu, lay, a, m1, last.0, last.1, nl);
        super::runseq::lemma_run_seq_one(cu, m1, super::templates::load_slot(last.0, last.1));
        let m2 = x64::step(cu, m1, super::templates::load_slot(last.0, last.1)).unwrap();
        assert(m2.rgf.len() == 16);
        assert forall|k: int| 0 <= k < ls.len() implies (#[trigger] m2.rgf[ls[k].0 as int]) as nat
            == lir::val_bits(slot_val(a, nl, ls[k].1)) by {
            if k < ls.len() - 1 {
                assert(pre[k] == ls[k]);
                assert(ls[k].0 != last.0);
            }
        }
    }
}

/// **The skeleton.** A template made of loads `ls`, a register-only middle
/// `mid` and a store of `rax` to slot `ts` takes a state related to `a` to one
/// related to `a2`, if:
///
/// - `a2` differs from `a` in slot `ts` only, where it holds `w`
///   ([`slots_agree_except`]);
/// - the middle, started from any well-formed state whose registers hold the
///   loaded words, leaves `w` in `rax` and changes only scratch registers and
///   `rip` ([`mid_post`]).
pub proof fn lemma_shape(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    m: x64::State,
    nl: nat,
    ls: Seq<(u8, nat)>,
    mid: Seq<x64::Instr>,
    ts: nat,
    w: nat,
)
    requires
        rel(lay, a, m, nl),
        loads_ok(ls, nl, a.stack.len()),
        x64::canonical(m.rip + code_len(super::templates::shape(ls, mid, ts))),
        ts < max_slots(),
        super::rel::slots_agree_except(a, a2, nl, ts),
        w == lir::val_bits(slot_val(a2, nl, ts)),
        mid_prop(cu, a, nl, ls, mid, w),
    ensures
        run_seq(cu, m, super::templates::shape(ls, mid, ts)) is Some,
        ({
            let m4 = run_seq(cu, m, super::templates::shape(ls, mid, ts)).unwrap();
            &&& rel(lay, a2, m4, nl)
            &&& m4.rip == m.rip + code_len(super::templates::shape(ls, mid, ts))
            &&& preserved(m, m4)
        }),
{
    super::steps::lemma_abi_consts();
    let ld = super::templates::loads_seq(ls);
    let st = seq![super::templates::store_slot(ts, rax())];
    super::runseq::lemma_code_len_append(ld, mid);
    super::runseq::lemma_code_len_append(ld + mid, st);
    super::runseq::lemma_code_len_one(super::templates::store_slot(ts, rax()));
    assert(super::templates::shape(ls, mid, ts) == (ld + mid) + st);
    lemma_loads(cu, lay, a, m, ls, nl);
    let m1 = run_seq(cu, m, ld).unwrap();
    // the middle
    assert(x64::wf(m1));
    assert(x64::canonical(m1.rip + code_len(mid)));
    assert(mid_pre(a, nl, ls, mid, m1));
    assert(mid_goal(cu, mid, w, m1));
    let m3 = run_seq(cu, m1, mid).unwrap();
    super::runseq::lemma_run_seq_append(cu, m, ld, mid);
    super::runseq::lemma_run_seq_append(cu, m, ld + mid, st);
    assert(x64::canonical(m3.rip)) by {
        super::mid::lemma_rip_between(m, m3.rip, m.rip + code_len(super::templates::shape(ls, mid, ts)));
    }
    super::rel::lemma_rel_regs(lay, a, m1, m3, nl);
    // the store
    assert(m3.rip + x64::instr_len(super::templates::store_slot(ts, rax())) <= m.rip + code_len(super::templates::shape(ls, mid, ts)));
    assert(x64::canonical(m3.rip + x64::instr_len(super::templates::store_slot(ts, rax()))));
    super::rel::lemma_store_finish(cu, lay, a, a2, m, m3, nl, ts, rax(), w);
    super::runseq::lemma_run_seq_one(cu, m3, super::templates::store_slot(ts, rax()));
}

} // verus!
