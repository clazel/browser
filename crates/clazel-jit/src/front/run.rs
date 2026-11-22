//! Running a list of simple LIR instructions: [`chain`] builds one `Then`
//! chain from a list, [`exec`] runs the list instruction by instruction, and
//! [`lemma_chain`] says `eval` of the chain is `exec` of the list. The
//! lowerings are chains, so each block's effect is proven on `exec`, with no
//! fuel in sight.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// LIR's `Then`.
pub open spec fn then(a: lir::Instr, b: lir::Instr) -> lir::Instr {
    lir::Instr::Then(Box::new(a), Box::new(b))
}

/// The instructions, one after the other, as one instruction (right-nested
/// `Then`; `Nop` for the empty list).
pub open spec fn chain(ins: Seq<lir::Instr>) -> lir::Instr
    decreases ins.len(),
{
    if ins.len() == 0 {
        lir::Instr::Nop
    } else if ins.len() == 1 {
        ins[0]
    } else {
        then(ins[0], chain(ins.skip(1)))
    }
}

/// The instruction has no structure: `eval` of it does not recurse.
pub open spec fn is_simple(i: lir::Instr) -> bool {
    match i {
        lir::Instr::Nop => true,
        lir::Instr::Const(_) => true,
        lir::Instr::LocalGet(_) => true,
        lir::Instr::LocalSet(_) => true,
        lir::Instr::LocalTee(_) => true,
        lir::Instr::Drop => true,
        lir::Instr::Select => true,
        lir::Instr::Bin(_) => true,
        lir::Instr::Un(_) => true,
        lir::Instr::BoundsCheck { .. } => true,
        lir::Instr::Load { .. } => true,
        lir::Instr::Store { .. } => true,
        lir::Instr::Exit(_, _) => true,
        lir::Instr::Br(_) => true,
        lir::Instr::BrIf(_) => true,
        _ => false,
    }
}

/// Every instruction of the list is simple.
pub open spec fn all_simple(ins: Seq<lir::Instr>) -> bool {
    forall|i: int| 0 <= i < ins.len() ==> is_simple(#[trigger] ins[i])
}

/// Run the list in order, each instruction with fuel 1 (enough for a simple
/// one), stopping at the first outcome that is not `Normal`.
pub open spec fn exec(lay: lir::Layout, ins: Seq<lir::Instr>, st: lir::St) -> lir::Outcome
    decreases ins.len(),
{
    if ins.len() == 0 {
        lir::Outcome::Normal(st)
    } else {
        match lir::eval(lay, ins[0], st, 1) {
            lir::Outcome::Normal(s1) => exec(lay, ins.skip(1), s1),
            o => o,
        }
    }
}

/// A simple instruction's outcome does not depend on the fuel, from 1.
pub proof fn lemma_simple_fuel(lay: lir::Layout, i: lir::Instr, st: lir::St, f1: nat, f2: nat)
    requires
        is_simple(i),
        f1 >= 1,
        f2 >= 1,
    ensures
        lir::eval(lay, i, st, f1) == lir::eval(lay, i, st, f2),
{
}

/// `eval` of the chain of a list of simple instructions is [`exec`] of it,
/// given enough fuel.
pub proof fn lemma_chain(lay: lir::Layout, ins: Seq<lir::Instr>, st: lir::St, fuel: nat)
    requires
        all_simple(ins),
        fuel > ins.len(),
    ensures
        lir::eval(lay, chain(ins), st, fuel) == exec(lay, ins, st),
    decreases ins.len(),
{
    if ins.len() == 0 {
        assert(chain(ins) == lir::Instr::Nop);
    } else if ins.len() == 1 {
        assert(chain(ins) == ins[0]);
        lemma_simple_fuel(lay, ins[0], st, fuel, 1);
        assert(ins.skip(1).len() == 0);
        match lir::eval(lay, ins[0], st, 1) {
            lir::Outcome::Normal(s1) => {
                assert(exec(lay, ins, st) == exec(lay, ins.skip(1), s1));
            },
            _ => {},
        }
    } else {
        let rest = ins.skip(1);
        assert(chain(ins) == then(ins[0], chain(rest)));
        assert(all_simple(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies is_simple(#[trigger] rest[i]) by {
                assert(rest[i] == ins[i + 1]);
            }
        }
        lemma_simple_fuel(lay, ins[0], st, (fuel - 1) as nat, 1);
        match lir::eval(lay, ins[0], st, 1) {
            lir::Outcome::Normal(s1) => {
                lemma_chain(lay, rest, s1, (fuel - 1) as nat);
            },
            _ => {},
        }
    }
}

/// Running two lists in a row.
pub proof fn lemma_exec_concat(lay: lir::Layout, a: Seq<lir::Instr>, b: Seq<lir::Instr>, st: lir::St)
    ensures
        exec(lay, a + b, st) == match exec(lay, a, st) {
            lir::Outcome::Normal(s1) => exec(lay, b, s1),
            o => o,
        },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).skip(1) =~= a.skip(1) + b);
        match lir::eval(lay, a[0], st, 1) {
            lir::Outcome::Normal(s1) => {
                lemma_exec_concat(lay, a.skip(1), b, s1);
            },
            _ => {},
        }
    }
}

/// `eval` of a chain of simple instructions followed by one arbitrary
/// instruction: the simple ones run, then `last` with the fuel that is left.
pub proof fn lemma_chain_last(
    lay: lir::Layout,
    ins: Seq<lir::Instr>,
    last: lir::Instr,
    st: lir::St,
    fuel: nat,
)
    requires
        all_simple(ins),
        fuel > ins.len(),
    ensures
        lir::eval(lay, chain(ins.push(last)), st, fuel) == match exec(lay, ins, st) {
            lir::Outcome::Normal(s1) => lir::eval(lay, last, s1, (fuel - ins.len()) as nat),
            o => o,
        },
    decreases ins.len(),
{
    if ins.len() == 0 {
        assert(ins.push(last) =~= seq![last]);
    } else {
        let rest = ins.skip(1);
        assert(all_simple(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies is_simple(#[trigger] rest[i]) by {
                assert(rest[i] == ins[i + 1]);
            }
        }
        assert(ins.push(last).len() >= 2);
        assert(ins.push(last).skip(1) =~= rest.push(last));
        assert(ins.push(last)[0] == ins[0]);
        lemma_simple_fuel(lay, ins[0], st, (fuel - 1) as nat, 1);
        match lir::eval(lay, ins[0], st, 1) {
            lir::Outcome::Normal(s1) => {
                lemma_chain_last(lay, rest, last, s1, (fuel - 1) as nat);
            },
            _ => {},
        }
    }
}

} // verus!
