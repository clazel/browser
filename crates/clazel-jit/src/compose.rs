//! **Composition.** The templates of a straight-line program, one after the
//! other, refine the program: [`lemma_prog_refines`] is the induction over
//! [`prog_instr`] (the left-nested `then` chain) that turns the per-template
//! refinements of [`crate::proofs`] into one for the whole program.
//!
//! This is composition over *sequencing* only. Structured control flow
//! (`block`, `loop`, `if`, `br`) needs jump templates, a relation at labels,
//! and a proof about the validator's targets rule; it is not in this slice.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`preserved`] is transitive.
pub proof fn lemma_preserved_trans(m: x64::State, m1: x64::State, m2: x64::State)
    requires
        preserved(m, m1),
        preserved(m1, m2),
    ensures
        preserved(m, m2),
{
    lemma_abi_consts_c();
    assert(ctx_of(m1) == ctx_of(m));
    assert forall|b: int| #[trigger] m.mem.dom().contains(b) && !in_exit_area(ctx_of(m), b)
        implies m2.mem[b] == m.mem[b] by {
        assert(m1.mem.dom().contains(b));
        assert(m1.mem[b] == m.mem[b]);
        assert(m2.mem[b] == m1.mem[b]);
    }
}

/// The constants the lemma above needs (`ctx_reg`, `sp_reg`).
pub proof fn lemma_abi_consts_c()
    ensures
        abi::ctx_reg() == 15,
        abi::sp_reg() == 4,
{
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

/// **A straight-line program's code refines it.** The templates of the
/// instructions of `ops`, each at the height the ones before it leave, run
/// in order from a state related to the start and reach one related to the
/// end of LIR's evaluation of [`prog_instr`].
#[verifier::rlimit(500)]
pub proof fn lemma_prog_refines(ops: Seq<Op>, nl: nat, h0: nat)
    requires
        prog_ok(ops, nl, h0),
    ensures
        super::contract::refines(prog_instr(ops), nl, h0, super::templates::code_of(ops, nl, h0)),
    decreases ops.len(),
{
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
        super::runseq::lemma_code_len_append(ca, cb);
        assert(super::templates::code_of(ops, nl, h0) == ca + cb);
        assert forall|
            lay: lir::Layout,
            cu: spec_fn(nat) -> nat,
            a: lir::St,
            m: x64::State,
            fuel: nat,
        |
            #![trigger lir::eval(lay, prog_instr(ops), a, fuel), run_seq(cu, m, ca + cb)]
            a.stack.len() == h0 && rel(lay, a, m, nl) && x64::canonical(
                m.rip + code_len(ca + cb),
            ) implies match lir::eval(lay, prog_instr(ops), a, fuel) {
            lir::Outcome::Normal(a2) => super::contract::refines_post(lay, a2, m, nl, ca + cb, run_seq(cu, m, ca + cb)),
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
                            assert(x64::wf(m));
                            assert(x64::canonical(m.rip + code_len(ca))) by {
                                super::runseq::lemma_canonical_between(m.rip, m.rip + code_len(ca), m.rip + code_len(ca + cb));
                            }
                            super::proofs::lemma_use_refines(prog_instr(pre), nl, h0, ca, lay, cu, a, m, f);
                            let m1 = run_seq(cu, m, ca).unwrap();
                            lemma_prog_height(pre, nl, h0, lay, a, a1, f);
                            assert(a1.stack.len() == hl);
                            assert(x64::canonical(m1.rip + code_len(cb)));
                            super::proofs::lemma_use_refines(last@, nl, hl, cb, lay, cu, a1, m1, f);
                            let m2 = run_seq(cu, m1, cb).unwrap();
                            super::runseq::lemma_run_seq_append(cu, m, ca, cb);
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
