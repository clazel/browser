//! `exit` with operands, in the control-flow statement. The code is the exit
//! sequence the first slice proved ([`super::exit::lemma_exit_refines`]); the
//! operands are the top `k` values of the stack, and the exit sequence writes
//! nothing but the exit-code word, so they are still in their frame slots
//! afterwards ([`exit_ops_refines`], [`cf_refines`]). The A64 counterpart of
//! [`crate::cfexit`].

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfalg::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cfleaf::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The exit sequence is in two parts: two plain instructions, then `ret`.
pub proof fn lemma_exit_parts(c: u16)
    ensures
        exit_seq(c) == seq![
            isa::Instr::MoveWide {
                sf: isa::Width::W32,
                opcode: isa::MoveWideOp::Z,
                d: x0(),
                imm16: c,
                hw: 0,
            },
            isa::Instr::LoadStoreImm {
                sf: isa::Width::W64,
                load: false,
                t: x0(),
                n: abi::ctx_reg(),
                imm12: (abi::exit_code_off() / 8) as u16,
            },
        ] + seq![isa::Instr::Ret],
        no_jumps(
            seq![
                isa::Instr::MoveWide {
                    sf: isa::Width::W32,
                    opcode: isa::MoveWideOp::Z,
                    d: x0(),
                    imm16: c,
                    hw: 0,
                },
                isa::Instr::LoadStoreImm {
                    sf: isa::Width::W64,
                    load: false,
                    t: x0(),
                    n: abi::ctx_reg(),
                    imm12: (abi::exit_code_off() / 8) as u16,
                },
            ],
        ),
{
    let pre = seq![
        isa::Instr::MoveWide {
            sf: isa::Width::W32,
            opcode: isa::MoveWideOp::Z,
            d: x0(),
            imm16: c,
            hw: 0,
        },
        isa::Instr::LoadStoreImm {
            sf: isa::Width::W64,
            load: false,
            t: x0(),
            n: abi::ctx_reg(),
            imm12: (abi::exit_code_off() / 8) as u16,
        },
    ];
    assert(exit_seq(c) =~= pre + seq![isa::Instr::Ret]);
}

/// **The run of the exit sequence** from a state related to `a`: it reaches a
/// state that is done ([`exit_done`]), still related to `a`, with nothing
/// outside the exit area changed and the link register and `SP` as they were.
#[verifier::rlimit(200)]
pub proof fn lemma_exit_reach(c: u16, nl: nat, lay: lir::Layout, a: lir::St, m: isa::State)
    requires
        rel(lay, a, m, nl),
        m.pc as int + code_len(exit_seq(c)) < isa::p2(64),
    ensures
        exists|m2: isa::State|
            #![trigger reaches(exit_seq(c), m.pc as int, m, m2)]
            reaches(exit_seq(c), m.pc as int, m, m2) && exit_done(m, m2, c as nat) && rel(
                lay,
                a,
                m2,
                nl,
            ) && preserved(m, m2),
{
    let code = exit_seq(c);
    let pre = seq![
        isa::Instr::MoveWide {
            sf: isa::Width::W32,
            opcode: isa::MoveWideOp::Z,
            d: x0(),
            imm16: c,
            hw: 0,
        },
        isa::Instr::LoadStoreImm {
            sf: isa::Width::W64,
            load: false,
            t: x0(),
            n: abi::ctx_reg(),
            imm12: (abi::exit_code_off() / 8) as u16,
        },
    ];
    lemma_exit_parts(c);
    super::exit::lemma_exit_refines(c, nl);
    assert(a.with_stack(lir::below(a.stack, 0)) == a) by {
        assert(lir::below(a.stack, 0) =~= a.stack);
    }
    assert(lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, 1) == lir::Outcome::Exit(
        c as nat,
        lir::top(a.stack, 0),
        a.with_stack(lir::below(a.stack, 0)),
    ));
    let m2 = run_seq(m, code).unwrap();
    super::runseq::lemma_run_seq_append(m, pre, seq![isa::Instr::Ret]);
    let m1 = run_seq(m, pre).unwrap();
    super::runseq::lemma_run_seq_one(m1, isa::Instr::Ret);
    assert(code_len(pre) == 8);
    lemma_reaches_plain_then(pre, isa::Instr::Ret, m, m1, m2);
    assert(pre + seq![isa::Instr::Ret] =~= code);
}

/// **`exit c` with `k` operands.** The code is the exit sequence for `c`.
#[verifier::rlimit(400)]
pub proof fn lemma_exit_cf(c: u32, k: usize, nl: nat, h: nat, offs: Seq<int>)
    requires
        c < 0x1_0000,
        k <= h,
        nl + h <= max_slots(),
    ensures
        cf_refines(Node::Exit(c, k)@, nl, h, offs, exit_seq(c as u16)),
{
    super::memlemmas::lemma_p2_consts();
    let c16 = c as u16;
    assert(c16 as nat == c as nat);
    let code = exit_seq(c16);
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, m, lir::eval(lay, Node::Exit(c, k)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && cf_canon(
            m.pc as int,
            offs,
            code,
        ) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        m,
        lir::eval(lay, Node::Exit(c, k)@, a, fuel),
    ) by {
        if fuel > 0 && a.stack.len() >= k {
            lemma_rel_base_unfold(lay, base, a, m, nl);
            let ac = a.with_stack(base + a.stack);
            let n = a.stack.len();
            assert(code_len(code) == 12);
            lemma_exit_reach(c16, nl, lay, ac, m);
            let m2 = choose|m2: isa::State|
                reaches(code, m.pc as int, m, m2) && exit_done(m, m2, c16 as nat) && rel(
                    lay,
                    ac,
                    m2,
                    nl,
                ) && preserved(m, m2);
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
                    super::steps::lemma_abi_consts();
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
            assert(reaches(code, m.pc as int, m, m2) && exit_done(m, m2, c as nat));
        }
    }
}

} // verus!
