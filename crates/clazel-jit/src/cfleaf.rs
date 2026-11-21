//! The leaves of the control-flow composition: `br` (a `jmp`), `br_if` (a
//! condition test and a `jcc`) and the pieces they need: one step of a
//! `jmp` and of a `jcc`, the test of a condition word, a run of plain
//! instructions followed by one more, and the relation surviving a change of
//! `rip`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `jmp rel` goes to the end of the instruction plus `rel`.
pub proof fn lemma_step_jmp(cu: spec_fn(nat) -> nat, m: x64::State, rel: int)
    requires
        x64::canonical(m.rip + 5),
        x64::canonical(m.rip + 5 + (rel as i32) as int),
    ensures
        x64::step(cu, m, jmp_i(rel)) == Some(
            x64::State { rip: m.rip + 5 + (rel as i32) as int, ..m },
        ),
{
    lemma_jmp_len(rel);
}

/// `jcc cc rel` goes to the end of the instruction plus `rel` when the
/// condition holds, and to the end of the instruction when not.
pub proof fn lemma_step_jcc(cu: spec_fn(nat) -> nat, m: x64::State, cc: u8, rel: int)
    requires
        x64::canonical(m.rip + 6),
        x64::canonical(m.rip + 6 + (rel as i32) as int),
    ensures
        x64::step(cu, m, jcc_i(cc, rel)) == Some(
            x64::State {
                rip: if x64::jcc_cmovcc_setcc_spec(m, cc) {
                    m.rip + 6 + (rel as i32) as int
                } else {
                    m.rip + 6
                },
                ..m
            },
        ),
{
    lemma_jcc_len(cc, rel);
}

/// `test eax, eax` on a word `x` below `2^32` sets `zf` exactly when `x` is
/// zero, and changes nothing but flags and `rip`.
pub proof fn lemma_test_eax(cu: spec_fn(nat) -> nat, m: x64::State, x: u32)
    requires
        x64::wf(m),
        m.rgf[0] == x as u64,
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 }) is Some,
        ({
            let m1 = x64::step(cu, m, x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 }).unwrap();
            &&& m1.rgf == m.rgf && m1.mem == m.mem && m1.xmm == m.xmm
            &&& m1.rip == m.rip + x64::instr_len(
                x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 },
            )
            &&& x64::jcc_cmovcc_setcc_spec(m1, 4) == (x == 0)
            &&& x64::jcc_cmovcc_setcc_spec(m1, 5) == (x != 0)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::flags::lemma_step_test(cu, m, x64::Size::W32, 0, 0);
    let m1 = x64::step(cu, m, x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 }).unwrap();
    assert(x64::rgfi_size(m, x64::Size::W32, 0) == x as int);
    assert(x64::loghead(32, x as int) == x as int);
    assert(((x as u64) & (x as u64)) == x as u64) by (bit_vector);
    assert(x64::zf_bit() == 6);
}

/// `m2` differs from `m` in registers other than `r15` (and `rip`, flags):
/// the relation, and the region table, carry over.
pub proof fn lemma_rel_base_same(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m2: x64::State,
    nl: nat,
)
    requires
        rel_base(lay, base, a, m, nl),
        m2.mem == m.mem,
        m2.rgf.len() == 16,
        m2.xmm.len() == 16,
        m2.rgf[15] == m.rgf[15],
        x64::canonical(m2.rip),
    ensures
        rel_base(lay, base, a, m2, nl),
{
    reveal(rel_base);
    super::steps::lemma_abi_consts();
    super::rel::lemma_rel_regs(lay, a.with_stack(base + a.stack), m, m2, nl);
    assert(ctx_of(m2) == ctx_of(m));
}

/// A state with the same memory and the same `r15` and `rsp` preserves
/// everything.
pub proof fn lemma_preserved_same(lay: lir::Layout, m: x64::State, m2: x64::State)
    requires
        m.rgf.len() == 16,
        m2.rgf.len() == 16,
        m2.mem == m.mem,
        m2.rgf[15] == m.rgf[15],
        m2.rgf[4] == m.rgf[4],
    ensures
        preserved_r(lay, m, m2),
{
    assert(ctx_of(m2) == ctx_of(m));
}

/// **Plain instructions, then one more**, for an abstract step function `f`
/// (so the solver does not unfold `x64::step` on the unknown instruction
/// `last`; see [`steps_g`]). If `pre` has no jumps and runs from `m` to `m1`,
/// and `last` steps from `m1` to `m2`, then `pre + [last]` placed at `m.rip`
/// reaches `m2` by `steps_g`, with `m1` at the end of `pre`.
pub proof fn lemma_steps_plain_then_g(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    pre: Seq<x64::Instr>,
    last: x64::Instr,
    m: x64::State,
    m1: x64::State,
    m2: x64::State,
)
    requires
        rip_plain(f),
        no_jumps(pre),
        super::runseq::run_gen(f, m, pre) == Some(m1),
        f(m1, last) == Some(m2),
    ensures
        m1.rip == m.rip + code_len(pre),
        steps_g(f, pre + seq![last], m.rip, m, pre.len() + 1) == Some(m2),
{
    let whole = pre + seq![last];
    assert(Seq::<x64::Instr>::empty() + pre + seq![last] =~= whole);
    assert(code_len(Seq::<x64::Instr>::empty()) == 0);
    lemma_run_gen_steps(f, Seq::empty(), pre, seq![last], m.rip, m, m1);
    super::runseq::lemma_code_len_append(pre, seq![last]);
    lemma_fetch_append_r(pre, seq![last], code_len(pre) as int);
    assert(fetch(seq![last], 0) == Some(last));
    assert(m1.rip - m.rip == code_len(pre));
    assert(code_len(pre) as int - code_len(pre) == 0);
    assert(fetch(whole, m1.rip - m.rip) == Some(last));
    reveal_with_fuel(steps_g, 2);
    assert(steps_g(f, whole, m.rip, m1, 1) == Some(m2));
    lemma_steps_g_trans(f, whole, m.rip, m, m1, m2, pre.len(), 1);
}

/// [`lemma_steps_plain_then_g`] for the machine's step: the `reaches` form.
pub proof fn lemma_reaches_plain_then(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    last: x64::Instr,
    m: x64::State,
    m1: x64::State,
    m2: x64::State,
)
    requires
        no_jumps(pre),
        run_seq(cu, m, pre) == Some(m1),
        x64::step(cu, m1, last) == Some(m2),
    ensures
        m1.rip == m.rip + code_len(pre),
        reaches(cu, pre + seq![last], m.rip, m, m2),
{
    let f = super::runseq::stepper(cu);
    lemma_stepper_rip_plain(cu);
    super::runseq::lemma_run_seq_is_gen(cu, m, pre);
    assert(f(m1, last) == Some(m2));
    lemma_steps_plain_then_g(f, pre, last, m, m1, m2);
    lemma_steps_is_gen(cu, pre + seq![last], m.rip, m, pre.len() + 1);
}

/// **`br l` is a `jmp`.** The code is `jmp` to label `l`; the machine is
/// then at the label, related to the same LIR state.
pub proof fn lemma_br(nl: nat, h: nat, offs: Seq<int>, l: usize)
    requires
        l < offs.len(),
        -0x8000_0000 <= offs[l as int] - 5 < 0x8000_0000,
    ensures
        cf_refines(Node::Br(l)@, nl, h, offs, seq![jmp_i(offs[l as int] - 5)]),
{
    let rel = offs[l as int] - 5;
    let code = seq![jmp_i(rel)];
    lemma_jmp_len(rel);
    super::runseq::lemma_code_len_one(jmp_i(rel));
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, Node::Br(l)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, code) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        cu,
        m,
        lir::eval(lay, Node::Br(l)@, a, fuel),
    ) by {
        if fuel > 0 {
            lemma_rel_base_unfold(lay, base, a, m, nl);
            assert(code_len(code) == 5);
            assert(x64::canonical(m.rip + offs[l as int]));
            lemma_step_jmp(cu, m, rel);
            let m2 = x64::State { rip: m.rip + 5 + rel, ..m };
            assert(m2.rip == m.rip + offs[l as int]);
            assert(fetch(code, 0) == Some(jmp_i(rel)));
            reveal_with_fuel(steps, 2);
            assert(steps(cu, code, m.rip, m, 1) == Some(m2));
            assert(reaches(cu, code, m.rip, m, m2));
            assert(base + Seq::<lir::Val>::empty() =~= base);
            lemma_rel_base_same(lay, base, a, m, m2, nl);
            lemma_preserved_same(lay, m, m2);
            assert(rel_base(lay, base + Seq::<lir::Val>::empty(), a, m2, nl));
            assert(rel_ext(lay, base, a, m2, nl));
        }
    }
}

/// **The condition test.** At height `h` with `nl` locals and the top of the
/// frame's stack holding the `i32` `c`, the first two instructions of
/// [`cond_pre`] (`mov rax, [top]; test eax, eax`) run from `m` to a state
/// `m2` with the relation unchanged, `rax` holding `c`, and `zf` saying whether
/// `c` is zero. `rel_a` is the relation to the LIR state `a`, whose stack
/// is `h` high with `c` on top.
pub proof fn lemma_cond_test(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    a: lir::St,
    m: x64::State,
    nl: nat,
    h: nat,
    c: u32,
    rest: nat,
)
    requires
        rel(lay, a, m, nl),
        a.stack.len() == h,
        1 <= h,
        a.stack[(h - 1) as int] == lir::Val::I32(c),
        x64::canonical(m.rip + rest),
        rest >= code_len(seq![
            load_slot(rax(), (nl + h - 1) as nat),
            x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() },
        ]),
    ensures
        run_seq(cu, m, seq![
            load_slot(rax(), (nl + h - 1) as nat),
            x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() },
        ]) is Some,
        ({
            let pre = seq![
                load_slot(rax(), (nl + h - 1) as nat),
                x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() },
            ];
            let m2 = run_seq(cu, m, pre).unwrap();
            &&& m2.rip == m.rip + code_len(pre)
            &&& m2.mem == m.mem && m2.rgf.len() == 16 && m2.xmm.len() == 16
            &&& m2.rgf[15] == m.rgf[15] && m2.rgf[4] == m.rgf[4]
            &&& rel(lay, a, m2, nl)
            &&& x64::jcc_cmovcc_setcc_spec(m2, 4) == (c == 0)
            &&& x64::jcc_cmovcc_setcc_spec(m2, 5) == (c != 0)
        }),
{
    super::steps::lemma_abi_consts();
    let j = (nl + h - 1) as nat;
    let i1 = load_slot(rax(), j);
    let i2 = x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() };
    let pre = seq![i1, i2];
    super::runseq::lemma_len2(i1, i2);
    assert(rax() == 0);
    assert(slot_val(a, nl, j) == lir::Val::I32(c));
    assert(j < nl + a.stack.len());
    assert(x64::canonical(m.rip + x64::instr_len(i1))) by {
        assert(x64::canonical(m.rip));
        super::runseq::lemma_canonical_between(m.rip, m.rip + x64::instr_len(i1), m.rip + rest);
    }
    super::rel::lemma_load_rel(cu, lay, a, m, 0, j, nl);
    let m1 = x64::step(cu, m, i1).unwrap();
    assert(m1.rgf[0] == c as u64);
    assert(x64::canonical(m1.rip + x64::instr_len(i2))) by {
        assert(x64::canonical(m.rip));
        super::runseq::lemma_canonical_between(
            m.rip,
            m.rip + x64::instr_len(i1) + x64::instr_len(i2),
            m.rip + rest,
        );
    }
    assert(x64::wf(m1));
    lemma_test_eax(cu, m1, c);
    let m2 = x64::step(cu, m1, i2).unwrap();
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen2(f, m, i1, i2, m1, m2);
    super::runseq::lemma_run_seq_is_gen(cu, m, pre);
    assert(m2.rgf == m1.rgf);
    assert(m1.rgf == m.rgf.update(0, c as u64));
    assert(m2.rgf[15] == m.rgf[15] && m2.rgf[4] == m.rgf[4]);
    assert(m2.rgf.len() == 16 && m2.xmm.len() == 16);
    assert(x64::canonical(m2.rip));
    super::rel::lemma_rel_regs(lay, a, m1, m2, nl);
}

/// **`br_if l`**: `mov rax, [cond]; test eax, eax; jne` to label `l`.
#[verifier::rlimit(400)]
pub proof fn lemma_brif(nl: nat, h: nat, offs: Seq<int>, l: usize)
    requires
        l < offs.len(),
        1 <= h,
        nl + h <= max_slots(),
        -0x8000_0000 <= offs[l as int] - (cond_len(nl, h) as int) < 0x8000_0000,
    ensures
        cf_refines(
            Node::BrIf(l)@,
            nl,
            h,
            offs,
            cond_pre(nl, h, 5, offs[l as int] - cond_len(nl, h) as int),
        ),
{
    super::steps::lemma_abi_consts();
    let pl = cond_len(nl, h) as int;
    let rel = offs[l as int] - pl;
    let code = cond_pre(nl, h, 5, rel);
    let j = (nl + h - 1) as nat;
    let i1 = load_slot(rax(), j);
    let i2 = x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() };
    let i3 = jcc_i(5, rel);
    let pre = seq![i1, i2];
    lemma_cond_pre_len(nl, h, 5, rel);
    lemma_jcc_len(5, rel);
    super::runseq::lemma_len3(i1, i2, i3);
    super::runseq::lemma_len2(i1, i2);
    assert(code == pre + seq![i3]);
    assert(code_len(code) == pl);
    assert(code_len(pre) + 6 == pl);
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, cu, m, lir::eval(lay, Node::BrIf(l)@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, code) implies cf_post(
        lay,
        base,
        nl,
        offs,
        code,
        cu,
        m,
        lir::eval(lay, Node::BrIf(l)@, a, fuel),
    ) by {
        if fuel > 0 {
            let n = a.stack.len();
            if n >= 1 {
                match a.stack[(n - 1) as int] {
                    lir::Val::I32(c) => {
                        lemma_rel_base_unfold(lay, base, a, m, nl);
                        let ac = a.with_stack(base + a.stack);
                        assert(ac.stack[(h - 1) as int] == lir::Val::I32(c));
                        assert(x64::canonical(m.rip + pl));
                        lemma_cond_test(cu, lay, ac, m, nl, h, c, pl as nat);
                        let m2 = run_seq(cu, m, pre).unwrap();
                        assert(m2.rip == m.rip + code_len(pre));
                        assert(x64::canonical(m2.rip + 6));
                        assert(x64::canonical(m.rip + offs[l as int]));
                        lemma_step_jcc(cu, m2, 5, rel);
                        let m3 = x64::step(cu, m2, i3).unwrap();
                        assert(no_jumps(pre));
                        lemma_reaches_plain_then(cu, pre, i3, m, m2, m3);
                        lemma_rel_regs_c(lay, ac, m2, m3, nl);
                        let s1 = a.with_stack(lir::below(a.stack, 1));
                        assert((base + a.stack).take((base + lir::below(a.stack, 1)).len() as int)
                            =~= base + lir::below(a.stack, 1));
                        lemma_rel_prefix(lay, a, base + a.stack, base + lir::below(a.stack, 1), m3, nl);
                        lemma_preserved_same(lay, m, m3);
                        lemma_table_pres(lay, m, m3);
                        assert(s1.with_stack(base + s1.stack) == a.with_stack(
                            base + lir::below(a.stack, 1),
                        ));
                        reveal(rel_base);
                        assert(rel_base(lay, base, s1, m3, nl));
                        assert(base + Seq::<lir::Val>::empty() =~= base);
                        assert(rel_ext(lay, base, s1, m3, nl));
                        assert(reaches(cu, code, m.rip, m, m3));
                        if c != 0 {
                            assert(m3.rip == m.rip + offs[l as int]);
                        } else {
                            assert(m3.rip == m.rip + code_len(code));
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}

/// `rel` survives a step that changes only `rip` and flags.
pub proof fn lemma_rel_regs_c(
    lay: lir::Layout,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
    nl: nat,
)
    requires
        rel(lay, a, m, nl),
        m3.mem == m.mem,
        m3.rgf == m.rgf,
        m3.xmm.len() == 16,
        x64::canonical(m3.rip),
    ensures
        rel(lay, a, m3, nl),
{
    super::rel::lemma_rel_regs(lay, a, m, m3, nl);
}

} // verus!
