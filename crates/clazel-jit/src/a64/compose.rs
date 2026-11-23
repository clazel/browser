//! Composition: a straight-line program's code refines the program
//! ([`lemma_prog_refines`]), by induction on its length from the refinement of
//! each template. The A64 counterpart of [`crate::compose`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`preserved`] is transitive.
pub proof fn lemma_preserved_trans(m: isa::State, m1: isa::State, m2: isa::State)
    requires
        preserved(m, m1),
        preserved(m1, m2),
    ensures
        preserved(m, m2),
{
    super::steps::lemma_abi_consts();
    assert(ctx_of(m1) == ctx_of(m));
    assert forall|b: int| #[trigger] m.mem.dom().contains(b) && !in_exit_area(ctx_of(m), b)
        implies m2.mem[b] == m.mem[b] by {
        assert(m1.mem.dom().contains(b));
        assert(m1.mem[b] == m.mem[b]);
        assert(m2.mem[b] == m1.mem[b]);
    }
}

/// A program's stack height after it is the one the static analysis computes.
pub proof fn lemma_prog_height(
    ops: Seq<Op>,
    nl: nat,
    h0: nat,
    lay: lir::Layout,
    a: lir::St,
    a2: lir::St,
    fuel: nat,
)
    requires
        prog_ok(ops, nl, h0),
        a.stack.len() == h0,
        lir::eval(lay, prog_instr(ops), a, fuel) == lir::Outcome::Normal(a2),
    ensures
        a2.stack.len() == height_after(ops, h0),
    decreases ops.len(),
{
    if ops.len() == 0 {
        assert(a2 == a);
    } else {
        let pre = ops.drop_last();
        let last = ops.last();
        assert(fuel > 0);
        match lir::eval(lay, prog_instr(pre), a, (fuel - 1) as nat) {
            lir::Outcome::Normal(a1) => {
                lemma_prog_height(pre, nl, h0, lay, a, a1, (fuel - 1) as nat);
                super::proofs::lemma_op_height(last, nl, height_after(pre, h0), lay, a1, a2, (fuel - 1) as nat);
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// **A straight-line program of templates refines the program** (the
/// left-nested `then` chain of its instructions), when every instruction has a
/// template ([`prog_ok`]).
#[verifier::rlimit(500)]
pub proof fn lemma_prog_refines(ops: Seq<Op>, nl: nat, h0: nat)
    requires
        prog_ok(ops, nl, h0),
    ensures
        super::contract::refines(prog_instr(ops), nl, h0, super::templates::code_of(ops, nl, h0)),
    decreases ops.len(),
{
    super::memlemmas::lemma_p2_consts();
    if ops.len() == 0 {
        super::proofs::lemma_op_refines(Op::Nop, nl, h0);
        assert(prog_instr(ops) == Op::Nop@);
        assert(super::templates::code_of(ops, nl, h0) == super::templates::tmpl(Op::Nop, nl, h0));
    } else {
        let pre = ops.drop_last();
        let last = ops.last();
        let hl = height_after(pre, h0);
        let ca = super::templates::code_of(pre, nl, h0);
        let cb = super::templates::tmpl(last, nl, hl);
        lemma_prog_refines(pre, nl, h0);
        super::proofs::lemma_op_refines(last, nl, hl);
        assert(super::templates::code_of(ops, nl, h0) == ca + cb);
        assert forall|lay: lir::Layout, a: lir::St, m: isa::State, fuel: nat|
            #![trigger lir::eval(lay, prog_instr(ops), a, fuel), run_seq(m, ca + cb)]
            a.stack.len() == h0 && rel(lay, a, m, nl) && (m.pc as int) + code_len(ca + cb)
                < isa::p2(64) implies match lir::eval(lay, prog_instr(ops), a, fuel) {
            lir::Outcome::Normal(a2) => super::contract::refines_post(lay, a2, m, nl, ca + cb, run_seq(m, ca + cb)),
            _ => true,
        } by {
            match lir::eval(lay, prog_instr(ops), a, fuel) {
                lir::Outcome::Normal(a2) => {
                    assert(fuel > 0);
                    let f = (fuel - 1) as nat;
                    // prog_instr(ops) = then(prog_instr(pre), last@)
                    match lir::eval(lay, prog_instr(pre), a, f) {
                        lir::Outcome::Normal(a1) => {
                            assert(lir::eval(lay, last@, a1, f) == lir::Outcome::Normal(a2));
                            assert((m.pc as int) + code_len(ca) < isa::p2(64));
                            super::proofs::lemma_use_refines(prog_instr(pre), nl, h0, ca, lay, a, m, f);
                            let m1 = run_seq(m, ca).unwrap();
                            lemma_prog_height(pre, nl, h0, lay, a, a1, f);
                            assert(a1.stack.len() == hl);
                            assert((m1.pc as int) + code_len(cb) < isa::p2(64));
                            super::proofs::lemma_use_refines(last@, nl, hl, cb, lay, a1, m1, f);
                            let m2 = run_seq(m1, cb).unwrap();
                            super::runseq::lemma_run_seq_append(m, ca, cb);
                            lemma_preserved_trans(m, m1, m2);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                },
                _ => {},
            }
        }
    }
}

} // verus!
