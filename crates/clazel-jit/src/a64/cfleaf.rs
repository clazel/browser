//! The leaves of the control-flow composition: `br` (a `b`), `br_if` (a load
//! of the condition and a `cbnz`) and the pieces they need: one step of a
//! `b`, of a `b.cond` and of a `cbz`/`cbnz`, a run of plain instructions
//! followed by one more, and the relation surviving a change of `pc`. The A64
//! counterpart of [`crate::cfleaf`]. A branch is relative to its own address
//! and in words (choice 16 of [`super::cfspec`]).

#[cfg(verus_only)]
use super::cfalg::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `b rel` goes to its own address plus `rel`.
pub proof fn lemma_step_b(m: isa::State, rel: int)
    requires
        rel % 4 == 0,
        -0x800_0000 <= rel < 0x800_0000,
        0 <= m.pc as int + rel < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, b_i(rel)) == Some(isa::State { pc: (m.pc as int + rel) as u64, ..m }),
{
    super::memlemmas::lemma_p2_consts();
    super::memlemmas::lemma_trunc64(m.pc as int + rel);
    assert(((rel / 4) as i32) as int == rel / 4);
    assert((rel / 4) * 4 == rel);
}

/// `b.cc rel` goes to its own address plus `rel` when the condition holds, and
/// to the next instruction when not.
pub proof fn lemma_step_bcond(m: isa::State, cc: u8, rel: int)
    requires
        cc < 14,
        rel % 4 == 0,
        -0x10_0000 <= rel < 0x10_0000,
        0 <= m.pc as int + rel < 0x1_0000_0000_0000_0000,
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, bcond_i(cc, rel)) == Some(
            isa::State {
                pc: (if isa::condition_holds(m, cc) {
                    m.pc as int + rel
                } else {
                    m.pc as int + 4
                }) as u64,
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::memlemmas::lemma_trunc64(m.pc as int + rel);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    assert(((rel / 4) as i32) as int == rel / 4);
    assert((rel / 4) * 4 == rel);
}

/// `cbz w0, rel` (`iszero`) or `cbnz w0, rel` goes to its own address plus
/// `rel` when the low 32 bits of `x0` are zero (are not zero), and to the next
/// instruction when not.
pub proof fn lemma_step_cb(m: isa::State, iszero: bool, rel: int)
    requires
        m.r.len() == 31,
        rel % 4 == 0,
        -0x10_0000 <= rel < 0x10_0000,
        0 <= m.pc as int + rel < 0x1_0000_0000_0000_0000,
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, cb_i(iszero, rel)) == Some(
            isa::State {
                pc: (if (isa::trunc(32, m.r[0] as int) == 0) == iszero {
                    m.pc as int + rel
                } else {
                    m.pc as int + 4
                }) as u64,
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::memlemmas::lemma_trunc64(m.pc as int + rel);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    assert(((rel / 4) as i32) as int == rel / 4);
    assert((rel / 4) * 4 == rel);
    assert(isa::x_read(m, 0, 32) == isa::trunc(32, m.r[0] as int));
}

/// `m2` differs from `m` in registers other than `x28` (and `pc`, flags): the
/// relation, and the region table, carry over.
pub proof fn lemma_rel_base_same(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m2: isa::State,
    nl: nat,
)
    requires
        rel_base(lay, base, a, m, nl),
        m2.mem == m.mem,
        m2.r.len() == 31,
        m2.vreg.len() == 32,
        m2.r[abi::ctx_reg() as int] == m.r[abi::ctx_reg() as int],
    ensures
        rel_base(lay, base, a, m2, nl),
{
    reveal(rel_base);
    super::steps::lemma_abi_consts();
    super::rel::lemma_rel_regs(lay, a.with_stack(base + a.stack), m, m2, nl);
    assert(ctx_of(m2) == ctx_of(m));
}

/// A state with the same memory, the same `x28`, `x30` and `SP` preserves
/// everything.
pub proof fn lemma_preserved_same(lay: lir::Layout, m: isa::State, m2: isa::State)
    requires
        m.r.len() == 31,
        m2.r.len() == 31,
        m2.mem == m.mem,
        m2.r[abi::ctx_reg() as int] == m.r[abi::ctx_reg() as int],
        m2.r[abi::link_reg() as int] == m.r[abi::link_reg() as int],
        m2.sp == m.sp,
    ensures
        preserved_r(lay, m, m2),
{
    assert(ctx_of(m2) == ctx_of(m));
}

/// One step at the start of `code`, placed at `base`, is a run of one step.
pub proof fn lemma_steps_one(
    code: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    i: isa::Instr,
    s1: isa::State,
)
    requires
        fetch(code, s.pc as int - base) == Some(i),
        isa::step(s, i) == Some(s1),
    ensures
        steps(code, base, s, 1) == Some(s1),
{
    reveal_with_fuel(steps, 2);
}

/// **Plain instructions, then one more**, for an abstract step function `f`
/// (so the solver does not unfold `isa::step` on the unknown instruction
/// `last`; see [`steps_g`]). If `pre` has no jumps and runs from `m` to `m1`,
/// and `last` steps from `m1` to `m2`, then `pre + [last]` placed at `m.pc`
/// reaches `m2` by `steps_g`, with `m1` at the end of `pre`.
pub proof fn lemma_steps_plain_then_g(
    f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>,
    pre: Seq<isa::Instr>,
    last: isa::Instr,
    m: isa::State,
    m1: isa::State,
    m2: isa::State,
)
    requires
        pc_plain(f),
        no_jumps(pre),
        m.pc as int + code_len(pre) + 4 < isa::p2(64),
        run_gen(f, m, pre) == Some(m1),
        f(m1, last) == Some(m2),
    ensures
        m1.pc as int == m.pc as int + code_len(pre),
        steps_g(f, pre + seq![last], m.pc as int, m, pre.len() + 1) == Some(m2),
{
    let whole = pre + seq![last];
    assert(Seq::<isa::Instr>::empty() + pre + seq![last] =~= whole);
    assert(code_len(Seq::<isa::Instr>::empty()) == 0);
    lemma_run_gen_steps(f, Seq::empty(), pre, seq![last], m.pc as int, m, m1);
    super::runseq::lemma_code_len_append(pre, seq![last]);
    lemma_fetch_append_r(pre, seq![last], code_len(pre) as int);
    assert(fetch(seq![last], 0) == Some(last));
    assert(m1.pc as int - m.pc as int == code_len(pre));
    assert(code_len(pre) as int - code_len(pre) == 0);
    assert(fetch(whole, m1.pc as int - m.pc as int) == Some(last));
    reveal_with_fuel(steps_g, 2);
    assert(steps_g(f, whole, m.pc as int, m1, 1) == Some(m2));
    lemma_steps_g_trans(f, whole, m.pc as int, m, m1, m2, pre.len(), 1);
}

/// [`lemma_steps_plain_then_g`] for the machine's step: the `reaches` form.
pub proof fn lemma_reaches_plain_then(
    pre: Seq<isa::Instr>,
    last: isa::Instr,
    m: isa::State,
    m1: isa::State,
    m2: isa::State,
)
    requires
        no_jumps(pre),
        m.pc as int + code_len(pre) + 4 < isa::p2(64),
        run_seq(m, pre) == Some(m1),
        isa::step(m1, last) == Some(m2),
    ensures
        m1.pc as int == m.pc as int + code_len(pre),
        reaches(pre + seq![last], m.pc as int, m, m2),
{
    let f = stepper();
    lemma_stepper_pc_plain();
    lemma_run_seq_is_gen(m, pre);
    assert(f(m1, last) == Some(m2));
    lemma_steps_plain_then_g(f, pre, last, m, m1, m2);
    lemma_steps_is_gen(pre + seq![last], m.pc as int, m, pre.len() + 1);
}

/// **`br l` is a `b`.** The code is `b` to label `l`; the machine is then at
/// the label, related to the same LIR state.
pub proof fn lemma_br(nl: nat, h: nat, offs: Seq<int>, l: usize)
    requires
        l < offs.len(),
        offs[l as int] % 4 == 0,
        -0x800_0000 <= offs[l as int] < 0x800_0000,
    ensures
        cf_refines(Node::Br(l)@, nl, h, offs, seq![b_i(offs[l as int])]),
{
    let rel = offs[l as int];
    let code = seq![b_i(rel)];
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, m, lir::eval(lay, Node::Br(l)@, a, fuel))]
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
        lir::eval(lay, Node::Br(l)@, a, fuel),
    ) by {
        if fuel > 0 {
            lemma_rel_base_unfold(lay, base, a, m, nl);
            super::memlemmas::lemma_p2_consts();
            assert(code_len(code) == 4);
            assert(cf_canon(m.pc as int, offs, code));
            assert(0 <= m.pc as int + offs[l as int]);
            assert(0 <= m.pc as int + rel < 0x1_0000_0000_0000_0000);
            lemma_step_b(m, rel);
            let m2 = isa::State { pc: (m.pc as int + rel) as u64, ..m };
            assert(m2.pc as int == m.pc as int + offs[l as int]);
            assert(fetch(code, m.pc as int - m.pc as int) == Some(b_i(rel)));
            lemma_steps_one(code, m.pc as int, m, b_i(rel), m2);
            assert(reaches(code, m.pc as int, m, m2));
            assert(base + Seq::<lir::Val>::empty() =~= base);
            lemma_rel_base_same(lay, base, a, m, m2, nl);
            lemma_preserved_same(lay, m, m2);
            assert(rel_base(lay, base + Seq::<lir::Val>::empty(), a, m2, nl));
            assert(rel_ext(lay, base, a, m2, nl));
        }
    }
}

/// **`br_if l`**: `ldr x0, [cond]; cbnz w0` to label `l`.
#[verifier::rlimit(400)]
pub proof fn lemma_brif(nl: nat, h: nat, offs: Seq<int>, l: usize)
    requires
        l < offs.len(),
        1 <= h,
        nl + h <= max_slots(),
        offs[l as int] % 4 == 0,
        -0x10_0000 <= offs[l as int] - 4 < 0x10_0000,
    ensures
        cf_refines(
            Node::BrIf(l)@,
            nl,
            h,
            offs,
            cond_pre(nl, h, false, offs[l as int] - 4),
        ),
{
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    let rel = offs[l as int] - 4;
    let code = cond_pre(nl, h, false, rel);
    let j = (nl + h - 1) as nat;
    let i1 = load_slot(x0(), j);
    let i2 = cb_i(false, rel);
    assert(code == seq![i1, i2]);
    assert(code_len(code) == 8);
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, code, m, lir::eval(lay, Node::BrIf(l)@, a, fuel))]
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
                        assert(slot_val(ac, nl, j) == lir::Val::I32(c));
                        assert(j < nl + ac.stack.len());
                        assert(m.pc as int + 4 < 0x1_0000_0000_0000_0000);
                        super::rel::lemma_load_rel(lay, ac, m, x0(), j, nl);
                        let m1 = isa::step(m, i1).unwrap();
                        assert(m1.r[0] == c as u64);
                        assert(m1.pc as int == m.pc as int + 4);
                        assert(0 <= m1.pc as int + rel < 0x1_0000_0000_0000_0000);
                        assert(m1.pc as int + 4 < 0x1_0000_0000_0000_0000);
                        assert(isa::trunc(32, c as int) == c) by {
                            vstd::arithmetic::div_mod::lemma_small_mod(c as nat, 0x1_0000_0000nat);
                        }
                        lemma_step_cb(m1, false, rel);
                        let m2 = isa::step(m1, i2).unwrap();
                        super::runseq::run1(m, i1, m1);
                        assert(no_jumps(seq![i1]));
                        lemma_reaches_plain_then(seq![i1], i2, m, m1, m2);
                        assert(code == seq![i1] + seq![i2]);
                        assert(m2.r == m1.r && m2.mem == m1.mem && m2.vreg == m1.vreg);
                        super::rel::lemma_rel_regs(lay, ac, m1, m2, nl);
                        let s1 = a.with_stack(lir::below(a.stack, 1));
                        assert((base + a.stack).take((base + lir::below(a.stack, 1)).len() as int)
                            =~= base + lir::below(a.stack, 1));
                        lemma_rel_prefix(
                            lay,
                            a,
                            base + a.stack,
                            base + lir::below(a.stack, 1),
                            m2,
                            nl,
                        );
                        lemma_preserved_same(lay, m, m2);
                        lemma_table_pres(lay, m, m2);
                        assert(s1.with_stack(base + s1.stack) == a.with_stack(
                            base + lir::below(a.stack, 1),
                        ));
                        reveal(rel_base);
                        assert(rel_base(lay, base, s1, m2, nl));
                        assert(base + Seq::<lir::Val>::empty() =~= base);
                        assert(rel_ext(lay, base, s1, m2, nl));
                        assert(reaches(code, m.pc as int, m, m2));
                        if c != 0 {
                            assert(m2.pc as int == m.pc as int + offs[l as int]);
                        } else {
                            assert(m2.pc as int == m.pc as int + code_len(code));
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}

} // verus!
