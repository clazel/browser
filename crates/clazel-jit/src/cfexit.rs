//! `exit` with operands, in the control-flow statement. The code is the exit
//! sequence the first slice proved ([`crate::exit::lemma_exit_refines`]); the
//! operands are the top `k` values of the stack, and the exit sequence
//! writes nothing but the exit-code word, so they are still in their frame
//! slots afterwards ([`exit_ops_refines`], [`cf_refines`]).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exit sequence is in two parts: two plain instructions, then `ret`.
pub proof fn lemma_exit_parts(c: u32)
    ensures
        exit_seq(c) == seq![
            x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
            x64::Instr::MovStore {
                sz: x64::Size::W64,
                mem: crate::exit::exit_mem(),
                src: rax(),
            },
        ] + seq![x64::Instr::Ret],
        no_jumps(
            seq![
                x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
                x64::Instr::MovStore {
                    sz: x64::Size::W64,
                    mem: crate::exit::exit_mem(),
                    src: rax(),
                },
            ],
        ),
{
    let pre = seq![
        x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
        x64::Instr::MovStore { sz: x64::Size::W64, mem: crate::exit::exit_mem(), src: rax() },
    ];
    assert(exit_seq(c) =~= pre + seq![x64::Instr::Ret]);
}

/// [`exit_refines`] used at one state, with fuel 1.
pub proof fn lemma_use_exit(
    c: u32,
    nl: nat,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    m: x64::State,
)
    requires
        rel(lay, a, m, nl),
        stack_ok(m),
        x64::canonical(m.rip + code_len(exit_seq(c))),
    ensures
        run_seq(cu, m, exit_seq(c)) is Some,
        ({
            let m2 = run_seq(cu, m, exit_seq(c)).unwrap();
            let rsp = x64::logext(64, m.rgf[abi::sp_reg() as int] as int);
            &&& rel(lay, a, m2, nl)
            &&& preserved_mem(m, m2)
            &&& exit_done(m, m2, c as nat)
        }),
{
    crate::exit::lemma_exit_refines(c, nl);
    assert(a.with_stack(lir::below(a.stack, 0)) == a) by {
        assert(lir::below(a.stack, 0) =~= a.stack);
    }
    assert(lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, 1) == lir::Outcome::Exit(
        c as nat,
        lir::top(a.stack, 0),
        a.with_stack(lir::below(a.stack, 0)),
    ));
}

/// **The run of the exit sequence** from a state related to `a`: it reaches a
/// state that is done ([`exit_done`]), still related to `a`, with nothing
/// outside the exit area changed.
#[verifier::rlimit(200)]
pub proof fn lemma_exit_reach(
    c: u32,
    nl: nat,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    a: lir::St,
    m: x64::State,
)
    requires
        rel(lay, a, m, nl),
        stack_ok(m),
        x64::canonical(m.rip + code_len(exit_seq(c))),
    ensures
        exists|m2: x64::State|
            #![trigger reaches(cu, exit_seq(c), m.rip, m, m2)]
            reaches(cu, exit_seq(c), m.rip, m, m2) && exit_done(m, m2, c as nat) && rel(
                lay,
                a,
                m2,
                nl,
            ) && preserved_mem(m, m2),
{
    let code = exit_seq(c);
    let pre = seq![
        x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
        x64::Instr::MovStore { sz: x64::Size::W64, mem: crate::exit::exit_mem(), src: rax() },
    ];
    lemma_exit_parts(c);
    lemma_use_exit(c, nl, lay, cu, a, m);
    let m2 = run_seq(cu, m, code).unwrap();
    super::runseq::lemma_run_seq_append(cu, m, pre, seq![x64::Instr::Ret]);
    let m1 = run_seq(cu, m, pre).unwrap();
    super::runseq::lemma_run_seq_one(cu, m1, x64::Instr::Ret);
    lemma_reaches_plain_then(cu, pre, x64::Instr::Ret, m, m1, m2);
    assert(pre + seq![x64::Instr::Ret] =~= code);
}

/// **`exit c` with `k` operands.** The code is the exit sequence for `c`.
#[verifier::rlimit(400)]
pub proof fn lemma_exit_cf(c: u32, k: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        k <= h,
        nl + h <= max_slots(),
    ensures
        cf_refines(Node::Exit(c, k)@, nl, h, offs, exit_seq(c)),
{
    let code = exit_seq(c);
    let pre = seq![
        x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
        x64::Instr::MovStore { sz: x64::Size::W64, mem: crate::exit::exit_mem(), src: rax() },
    ];
    lemma_exit_parts(c);
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, Node::Exit(c, k)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, code) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        cu,
        m,
        lir::eval(lay, Node::Exit(c, k)@, a, fuel),
    ) by {
        if fuel > 0 && a.stack.len() >= k {
            lemma_rel_base_unfold(lay, base, a, m, nl);
            let ac = a.with_stack(base + a.stack);
            let n = a.stack.len();
            lemma_exit_reach(c, nl, lay, cu, ac, m);
            let m2 = choose|m2: x64::State|
                reaches(cu, code, m.rip, m, m2) && exit_done(m, m2, c as nat) && rel(lay, ac, m2, nl)
                    && preserved_mem(m, m2);
            // the outcome
            let vals = lir::top(a.stack, k as nat);
            let s = a.with_stack(lir::below(a.stack, k as nat));
            assert(lir::eval(lay, Node::Exit(c, k)@, a, fuel) == lir::Outcome::Exit(
                c as nat,
                vals,
                s,
            ));
            // the relation, below the operands
            assert((base + a.stack).take((base + s.stack).len() as int) =~= base + s.stack);
            lemma_rel_prefix(lay, a, base + a.stack, base + s.stack, m2, nl);
            assert(preserved_mem_r(lay, m, m2)) by {
                assert(ctx_of(m2) == ctx_of(m)) by {
                    crate::steps::lemma_abi_consts();
                }
            }
            lemma_table_pres(lay, m, m2);
            assert(s.with_stack(base + s.stack) == a.with_stack(base + s.stack));
            reveal(rel_base);
            assert(rel_base(lay, base + Seq::<lir::Val>::empty(), s, m2, nl)) by {
                assert(base + Seq::<lir::Val>::empty() =~= base);
            }
            // the operands are still in their slots
            assert forall|i: int| 0 <= i < vals.len() implies #[trigger] slot_holds(
                m2.mem,
                ctx_of(m),
                (nl + (base + Seq::<lir::Val>::empty()).len() + s.stack.len() + i) as nat,
                lir::val_bits(vals[i]),
            ) by {
                let jj = (nl + base.len() + (n - k) + i) as nat;
                assert(vals[i] == a.stack[(n - k) as int + i]);
                assert((base + a.stack)[(base.len() + n - k) as int + i] == a.stack[(n - k) as int
                    + i]);
                assert(ctx_of(m2) == ctx_of(m));
                assert(slot_val(ac, nl, jj) == vals[i]);
            }
            assert(ops_in_frame(
                m2.mem,
                ctx_of(m),
                nl,
                (base + Seq::<lir::Val>::empty()).len() + s.stack.len(),
                vals,
            ));
            assert(exit_rel(lay, base, s, m2, nl, ctx_of(m), vals));
            assert(reaches(cu, code, m.rip, m, m2) && exit_done(m, m2, c as nat));
        }
    }
}

} // verus!
