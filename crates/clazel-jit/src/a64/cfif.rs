//! `if`: the condition test, a `je` over the first arm, the arms, and a `jmp`
//! over the second. LIR evaluates `if` as a void `block` around the arm the
//! condition picks, run with the condition popped, so the arm's label 0 is the
//! end of the whole `if`.

#[cfg(verus_only)]
use super::cfalg::*;
#[cfg(verus_only)]
use super::cfblock::*;
#[cfg(verus_only)]
use super::cfcompose::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cfleaf::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::contract::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[cfg(verus_only)]
use crate::cfheight::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The length of the condition test.
pub open spec fn if_p(nl: nat, h: nat) -> int {
    cond_len(nl, h) as int
}

/// The code of an `if` whose arms have the code `ct` and `ce`.
pub open spec fn if_code(nl: nat, h: nat, ct: Seq<isa::Instr>, ce: Seq<isa::Instr>) -> Seq<
    isa::Instr,
> {
    cond_pre(nl, h, true, code_len(ct) as int + 8) + ct + seq![b_i(code_len(ce) as int + 4)] + ce
}

/// The labels in scope in the first arm: its own (the end of the `if`), then
/// the outer ones.
pub open spec fn if_offs_t(
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
) -> Seq<int> {
    seq![code_len(ct) as int + 4 + code_len(ce) as int] + shift(offs, if_p(nl, h))
}

/// The labels in scope in the second arm.
pub open spec fn if_offs_e(
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
) -> Seq<int> {
    seq![code_len(ce) as int] + shift(offs, if_p(nl, h) + code_len(ct) as int + 4)
}

/// A `b` in the middle of `pre + [b] + post`, reached at the end of `pre`, is
/// one step.
pub proof fn lemma_reach_b(
    pre: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    m: isa::State,
    m4: isa::State,
    rel: int,
)
    requires
        m4.pc as int == m.pc as int + code_len(pre),
        rel % 4 == 0,
        -0x800_0000 <= rel < 0x800_0000,
        0 <= m4.pc as int + rel < isa::p2(64),
    ensures
        reaches(
            pre + seq![b_i(rel)] + post,
            m.pc as int,
            m4,
            isa::State { pc: (m4.pc as int + rel) as u64, ..m4 },
        ),
{
    super::memlemmas::lemma_p2_consts();
    let whole = pre + seq![b_i(rel)] + post;
    let m5 = isa::State { pc: (m4.pc as int + rel) as u64, ..m4 };
    assert(whole =~= pre + (seq![b_i(rel)] + post));
    lemma_fetch_append_r(pre, seq![b_i(rel)] + post, code_len(pre) as int);
    assert(code_len(pre) as int - code_len(pre) == 0);
    assert(fetch(seq![b_i(rel)] + post, 0) == Some(b_i(rel)));
    assert(m4.pc as int - m.pc as int == code_len(pre));
    lemma_step_b(m4, rel);
    lemma_steps_one(whole, m.pc as int, m4, b_i(rel), m5);
}

/// The length of the condition test.
pub proof fn lemma_cond_pre_len(nl: nat, h: nat, iszero: bool, rel: int)
    ensures
        code_len(cond_pre(nl, h, iszero, rel)) == 8,
{
}

/// Where the arm starts, from the `if`'s first byte.
pub open spec fn if_q(is_then: bool, nl: nat, h: nat, ct: Seq<isa::Instr>) -> int {
    if is_then {
        if_p(nl, h)
    } else {
        if_p(nl, h) + code_len(ct) as int + 4
    }
}

/// The arm's code.
pub open spec fn if_cx(is_then: bool, ct: Seq<isa::Instr>, ce: Seq<isa::Instr>) -> Seq<isa::Instr> {
    if is_then {
        ct
    } else {
        ce
    }
}

/// The labels in scope in the arm.
pub open spec fn if_offs_x(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
) -> Seq<int> {
    if is_then {
        if_offs_t(nl, h, offs, ct, ce)
    } else {
        if_offs_e(nl, h, offs, ct, ce)
    }
}

/// The code before the arm.
pub open spec fn if_pre(
    is_then: bool,
    nl: nat,
    h: nat,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
) -> Seq<isa::Instr> {
    let cp = cond_pre(nl, h, true, code_len(ct) as int + 8);
    if is_then {
        cp
    } else {
        cp + ct + seq![b_i(code_len(ce) as int + 4)]
    }
}

/// The code after the arm.
pub open spec fn if_post(
    is_then: bool,
    nl: nat,
    h: nat,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
) -> Seq<isa::Instr> {
    if is_then {
        seq![b_i(code_len(ce) as int + 4)] + ce
    } else {
        Seq::empty()
    }
}

/// The whole code is the code before the arm, the arm, and the code after.
pub proof fn lemma_if_split(is_then: bool, nl: nat, h: nat, ct: Seq<isa::Instr>, ce: Seq<isa::Instr>)
    ensures
        if_pre(is_then, nl, h, ct, ce) + if_cx(is_then, ct, ce) + if_post(is_then, nl, h, ct, ce)
            == if_code(nl, h, ct, ce),
        code_len(if_pre(is_then, nl, h, ct, ce)) == if_q(is_then, nl, h, ct),
        code_len(if_code(nl, h, ct, ce)) == if_p(nl, h) + code_len(ct) + 4 + code_len(ce),
        if_code(nl, h, ct, ce) == cond_pre(nl, h, true, code_len(ct) as int + 8) + (ct + seq![b_i(
            code_len(ce) as int + 4,
        )] + ce),
        is_then ==> if_pre(is_then, nl, h, ct, ce) + if_cx(is_then, ct, ce) == cond_pre(
            nl,
            h,
            true,
            code_len(ct) as int + 8,
        ) + ct,
        !is_then ==> if_pre(is_then, nl, h, ct, ce) + if_cx(is_then, ct, ce) == if_code(
            nl,
            h,
            ct,
            ce,
        ),
{
    let cp = cond_pre(nl, h, true, code_len(ct) as int + 8);
    let jm = b_i(code_len(ce) as int + 4);
    lemma_cond_pre_len(nl, h, true, code_len(ct) as int + 8);
    super::runseq::lemma_code_len_append(cp, ct);
    super::runseq::lemma_code_len_append(cp + ct, seq![jm]);
    super::runseq::lemma_code_len_append(cp + ct + seq![jm], ce);
    assert(Seq::<isa::Instr>::empty() + ce =~= ce);
    assert(cp + ct + seq![jm] + ce =~= cp + (ct + seq![jm] + ce));
    if is_then {
        assert(cp + ct + (seq![jm] + ce) =~= cp + ct + seq![jm] + ce);
    } else {
        assert(cp + ct + seq![jm] + ce + Seq::<isa::Instr>::empty() =~= cp + ct + seq![jm] + ce);
    }
}

/// **What running the condition test and the `je` does**, for `if`: the machine
/// is at the start of the arm the condition picks, related to the `if`'s state
/// with the condition popped, and the arm's statement can be used there.
pub open spec fn if_head(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m3: isa::State,
) -> bool {
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let cx = if_cx(is_then, ct, ce);
    let q = if_q(is_then, nl, h, ct);
    &&& m3.pc as int == m.pc as int + q
    &&& reaches(cond_pre(nl, h, true, code_len(ct) as int + 8), m.pc as int, m, m3)
    &&& rel_base(lay, base + a0.stack, fresh(a0), m3, nl)
    &&& preserved_r(lay, m, m3)
    &&& cf_canon(m3.pc as int, if_offs_x(is_then, nl, h, offs, ct, ce), cx)
}

/// **The head of an `if`**: the condition test and the `cbz` take the machine
/// to the start of the arm ([`if_head`]).
#[verifier::rlimit(400)]
pub proof fn lemma_if_head(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    c: u32,
)
    requires
        1 <= h,
        nl + h <= max_slots(),
        code_len(ct) < 0x8_0000,
        code_len(ce) < 0x8_0000,
        base.len() + a.stack.len() == h,
        a.stack.len() >= 1,
        a.stack[(a.stack.len() - 1) as int] == lir::Val::I32(c),
        (c != 0) == is_then,
        rel_base(lay, base, a, m, nl),
        cf_canon(m.pc as int, offs, if_code(nl, h, ct, ce)),
    ensures
        exists|m3: isa::State| if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3),
{
    super::steps::lemma_abi_consts();
    super::memlemmas::lemma_p2_consts();
    lemma_if_split(is_then, nl, h, ct, ce);
    let p = if_p(nl, h);
    let st = code_len(ct) as int;
    let se = code_len(ce) as int;
    let cp = cond_pre(nl, h, true, st + 8);
    let whole = if_code(nl, h, ct, ce);
    let ee = p + st + 4 + se;
    let j = (nl + h - 1) as nat;
    let i1 = load_slot(x0(), j);
    let i3 = cb_i(true, st + 8);
    assert(p == 8);
    assert(cp == seq![i1, i3]);
    assert(code_len(whole) == ee);
    assert(cf_canon(m.pc as int, offs, whole));
    assert(m.pc as int + ee < isa::p2(64));
    lemma_rel_base_unfold(lay, base, a, m, nl);
    let ac = a.with_stack(base + a.stack);
    assert(ac.stack[(h - 1) as int] == lir::Val::I32(c));
    assert(slot_val(ac, nl, j) == lir::Val::I32(c));
    assert(j < nl + ac.stack.len());
    super::rel::lemma_load_rel(lay, ac, m, x0(), j, nl);
    let m1 = isa::step(m, i1).unwrap();
    assert(m1.r[0] == c as u64);
    assert(m1.pc as int == m.pc as int + 4);
    assert(isa::trunc(32, c as int) == c) by {
        vstd::arithmetic::div_mod::lemma_small_mod(c as nat, 0x1_0000_0000nat);
    }
    lemma_step_cb(m1, true, st + 8);
    let m3 = isa::step(m1, i3).unwrap();
    super::runseq::run1(m, i1, m1);
    assert(no_jumps(seq![i1]));
    lemma_reaches_plain_then(seq![i1], i3, m, m1, m3);
    assert(cp == seq![i1] + seq![i3]);
    let q = if_q(is_then, nl, h, ct);
    assert(m3.pc as int == m.pc as int + q);
    assert(reaches(cp, m.pc as int, m, m3));
    // relation at m3
    assert(m3.r == m1.r && m3.mem == m1.mem && m3.vreg == m1.vreg);
    super::rel::lemma_rel_regs(lay, ac, m1, m3, nl);
    let a0 = a.with_stack(lir::below(a.stack, 1));
    assert((base + a.stack).take((base + a0.stack).len() as int) =~= base + a0.stack);
    lemma_rel_prefix(lay, a, base + a.stack, base + a0.stack, m3, nl);
    lemma_preserved_same(lay, m, m3);
    lemma_table_pres(lay, m, m3);
    assert(a0.with_stack(base + a0.stack) == a.with_stack(base + a0.stack));
    reveal(rel_base);
    assert(rel_base(lay, base, a0, m3, nl));
    lemma_rel_base_enter(lay, base, a0, m3, nl);
    // the arm's labels are canonical
    let cx = if_cx(is_then, ct, ce);
    let offs_x = if_offs_x(is_then, nl, h, offs, ct, ce);
    assert(code_len(cx) <= (if is_then { st } else { se }));
    assert forall|l: int| 0 <= l < offs_x.len() implies 0 <= m3.pc as int + #[trigger] offs_x[l]
        && m3.pc as int + offs_x[l] < isa::p2(64) && offs_x[l] % 4 == 0 by {
        if l == 0 {
            assert(offs_x[0] == ee - q);
        } else {
            lemma_shift_index(offs, q, l - 1);
            assert(offs_x[l] == offs[l - 1] - q);
            assert(0 <= m.pc as int + offs[l - 1]);
        }
    }
    assert(cf_canon(m3.pc as int, offs_x, cx));
    assert(if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3));
}


/// The condition test's run, in the whole `if`'s code.
pub proof fn lemma_head_reach_whole(
    nl: nat,
    h: nat,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    m: isa::State,
    m3: isa::State,
)
    requires
        reaches(cond_pre(nl, h, true, code_len(ct) as int + 8), m.pc as int, m, m3),
    ensures
        reaches(if_code(nl, h, ct, ce), m.pc as int, m, m3),
{
    lemma_if_split(true, nl, h, ct, ce);
    lemma_reaches_post(
        cond_pre(nl, h, true, code_len(ct) as int + 8),
        ct + seq![b_i(code_len(ce) as int + 4)] + ce,
        m.pc as int,
        m,
        m3,
    );
}

/// The arm's reach, embedded in the whole `if`'s code, from the `if`'s start.
pub proof fn lemma_if_arm_reach(
    is_then: bool,
    nl: nat,
    h: nat,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    m: isa::State,
    m3: isa::State,
    m4: isa::State,
)
    requires
        m3.pc as int == m.pc as int + if_q(is_then, nl, h, ct),
        reaches(if_cx(is_then, ct, ce), m3.pc as int, m3, m4),
    ensures
        reaches(if_code(nl, h, ct, ce), m.pc as int, m3, m4),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    let pre = if_pre(is_then, nl, h, ct, ce);
    let post = if_post(is_then, nl, h, ct, ce);
    let cx = if_cx(is_then, ct, ce);
    lemma_reaches_embed(pre, cx, post, m3.pc as int, m3, m4);
    assert(m3.pc as int - code_len(pre) == m.pc as int);
}

/// **The arm's run to its end**: from the start of the arm, its code reaches
/// the end of the arm, related to the arm's final state on top of the `if`'s
/// own stack.
#[verifier::rlimit(100)]
pub proof fn lemma_if_arm_end(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m3: isa::State,
    s: lir::St,
)
    requires
        if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3),
        cf_post(
            lay,
            base + a.with_stack(lir::below(a.stack, 1)).stack,
            nl,
            if_offs_x(is_then, nl, h, offs, ct, ce),
            if_cx(is_then, ct, ce),
            m3,
            lir::Outcome::Normal(s),
        ),
    ensures
        exists|m4: isa::State|
            #![trigger reaches(if_code(nl, h, ct, ce), m.pc as int, m, m4)]
            reaches(if_code(nl, h, ct, ce), m.pc as int, m, m4) && m4.pc as int == m.pc as int + if_q(
                is_then,
                nl,
                h,
                ct,
            ) + code_len(if_cx(is_then, ct, ce)) && rel_base(
                lay,
                base,
                s.with_stack(a.with_stack(lir::below(a.stack, 1)).stack + s.stack),
                m4,
                nl,
            ) && preserved_r(lay, m, m4),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let cx = if_cx(is_then, ct, ce);
    let m4 = choose|m4: isa::State|
        reaches(cx, m3.pc as int, m3, m4) && m4.pc as int == m3.pc as int + code_len(cx) && rel_base(
            lay,
            base + a0.stack,
            s,
            m4,
            nl,
        ) && preserved_r(lay, m3, m4);
    lemma_head_reach_whole(nl, h, ct, ce, m, m3);
    lemma_if_arm_reach(is_then, nl, h, ct, ce, m, m3, m4);
    lemma_reaches_trans(if_code(nl, h, ct, ce), m.pc as int, m, m3, m4);
    lemma_pr_trans(lay, m, m3, m4);
    lemma_rel_base_cat(lay, base, a0.stack, s, m4, nl);
}

/// **Running a `b` that follows code already run**: the machine at the end of
/// `pre`, in `pre + [b] + post`, takes the `b`, and stays related.
#[verifier::rlimit(100)]
pub proof fn lemma_b_finish(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    nl: nat,
    pre: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    m: isa::State,
    m4: isa::State,
    sn: lir::St,
    se: int,
)
    requires
        reaches(pre + seq![b_i(se + 4)] + post, m.pc as int, m, m4),
        m4.pc as int == m.pc as int + code_len(pre),
        se % 4 == 0,
        0 <= se < 0x8_0000,
        0 <= m4.pc as int + se + 4 < isa::p2(64),
        rel_base(lay, base, sn, m4, nl),
        preserved_r(lay, m, m4),
    ensures
        exists|m5: isa::State|
            #![trigger reaches(pre + seq![b_i(se + 4)] + post, m.pc as int, m, m5)]
            reaches(pre + seq![b_i(se + 4)] + post, m.pc as int, m, m5) && m5.pc as int
                == m4.pc as int + se + 4 && rel_base(lay, base, sn, m5, nl) && preserved_r(
                lay,
                m,
                m5,
            ),
{
    super::memlemmas::lemma_p2_consts();
    lemma_rel_base_unfold(lay, base, sn, m4, nl);
    lemma_reach_b(pre, post, m, m4, se + 4);
    let m5 = isa::State { pc: (m4.pc as int + se + 4) as u64, ..m4 };
    assert(m5.pc as int == m4.pc as int + se + 4);
    lemma_reaches_trans(pre + seq![b_i(se + 4)] + post, m.pc as int, m, m4, m5);
    lemma_rel_base_same(lay, base, sn, m4, m5, nl);
    lemma_preserved_same(lay, m4, m5);
    lemma_pr_trans(lay, m, m4, m5);
}

/// **The arm falls through.** For the first arm there is the `jmp` over the
/// second still to run.
#[verifier::rlimit(100)]
pub proof fn lemma_if_normal(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m3: isa::State,
    s: lir::St,
)
    requires
        code_len(ct) < 0x8_0000,
        code_len(ce) < 0x8_0000,
        cf_canon(m.pc as int, offs, if_code(nl, h, ct, ce)),
        if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3),
        cf_post(
            lay,
            base + a.with_stack(lir::below(a.stack, 1)).stack,
            nl,
            if_offs_x(is_then, nl, h, offs, ct, ce),
            if_cx(is_then, ct, ce),
            m3,
            lir::Outcome::Normal(s),
        ),
    ensures
        cf_post(
            lay,
            base,
            nl,
            offs,
            if_code(nl, h, ct, ce),
            m,
            lir::Outcome::Normal(
                s.with_stack(a.with_stack(lir::below(a.stack, 1)).stack + s.stack),
            ),
        ),
{
    super::memlemmas::lemma_p2_consts();
    lemma_if_split(is_then, nl, h, ct, ce);
    lemma_if_arm_end(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3, s);
    let p = if_p(nl, h);
    let st = code_len(ct) as int;
    let se = code_len(ce) as int;
    let whole = if_code(nl, h, ct, ce);
    let ee = p + st + 4 + se;
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let sn = s.with_stack(a0.stack + s.stack);
    let m4 = choose|m4: isa::State|
        reaches(whole, m.pc as int, m, m4) && m4.pc as int == m.pc as int + if_q(is_then, nl, h, ct) + code_len(
            if_cx(is_then, ct, ce),
        ) && rel_base(lay, base, sn, m4, nl) && preserved_r(lay, m, m4);
    if is_then {
        let cp = cond_pre(nl, h, true, st + 8);
        assert(m4.pc as int == m.pc as int + p + st);
        assert(cf_canon(m.pc as int, offs, whole));
        assert(code_len(whole) == ee);
        assert(m.pc as int + ee < isa::p2(64));
        assert(st % 4 == 0 && se % 4 == 0);
        assert(code_len(cp + ct) == p + st) by {
            lemma_cond_pre_len(nl, h, true, st + 8);
            super::runseq::lemma_code_len_append(cp, ct);
        }
        assert(whole == (cp + ct) + seq![b_i(se + 4)] + ce);
        lemma_b_finish(lay, base, nl, cp + ct, ce, m, m4, sn, se);
    } else {
        assert(m4.pc as int == m.pc as int + ee);
    }
}

/// **A branch to the arm's own label** is the `if` ending.
pub proof fn lemma_if_br0(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m3: isa::State,
    s: lir::St,
)
    requires
        code_len(ct) < 0x8_0000,
        code_len(ce) < 0x8_0000,
        if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3),
        cf_post(
            lay,
            base + a.with_stack(lir::below(a.stack, 1)).stack,
            nl,
            if_offs_x(is_then, nl, h, offs, ct, ce),
            if_cx(is_then, ct, ce),
            m3,
            lir::Outcome::Branch(0, s),
        ),
    ensures
        cf_post(
            lay,
            base,
            nl,
            offs,
            if_code(nl, h, ct, ce),
            m,
            lir::Outcome::Normal(s.with_stack(a.with_stack(lir::below(a.stack, 1)).stack)),
        ),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let cx = if_cx(is_then, ct, ce);
    let offs_x = if_offs_x(is_then, nl, h, offs, ct, ce);
    let q = if_q(is_then, nl, h, ct);
    let ee = if_p(nl, h) + code_len(ct) as int + 4 + code_len(ce) as int;
    let m4 = choose|m4: isa::State|
        reaches(cx, m3.pc as int, m3, m4) && m4.pc as int == m3.pc as int + offs_x[0] && rel_ext(
            lay,
            base + a0.stack,
            s,
            m4,
            nl,
        ) && preserved_r(lay, m3, m4);
    lemma_head_reach_whole(nl, h, ct, ce, m, m3);
    lemma_if_arm_reach(is_then, nl, h, ct, ce, m, m3, m4);
    lemma_reaches_trans(if_code(nl, h, ct, ce), m.pc as int, m, m3, m4);
    lemma_pr_trans(lay, m, m3, m4);
    lemma_br0_rel(lay, base, a0.stack, s, m4, nl);
    assert(offs_x[0] == ee - q);
    assert(m4.pc as int == m.pc as int + ee);
}

/// **The arm branches past the `if`, or exits**: the outcome is the `if`'s,
/// seen from the start of the code.
pub proof fn lemma_if_out(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: isa::State,
    m3: isa::State,
    o: lir::Outcome,
    o2: lir::Outcome,
)
    requires
        code_len(ct) < 0x8_0000,
        code_len(ce) < 0x8_0000,
        !(o2 is Normal),
        if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3),
        cf_post(
            lay,
            base,
            nl,
            shift(offs, if_q(is_then, nl, h, ct)),
            if_cx(is_then, ct, ce),
            m3,
            o2,
        ),
    ensures
        cf_post(lay, base, nl, offs, if_code(nl, h, ct, ce), m, o2),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    let cx = if_cx(is_then, ct, ce);
    let q = if_q(is_then, nl, h, ct);
    let pre = if_pre(is_then, nl, h, ct, ce);
    let post = if_post(is_then, nl, h, ct, ce);
    let whole = if_code(nl, h, ct, ce);
    assert forall|l: int| 0 <= l < offs.len() implies #[trigger] shift(offs, q)[l] + code_len(pre)
        == offs[l] by {
        lemma_shift_index(offs, q, l);
    }
    // the run from m to m3, inside pre + cx
    let cp = cond_pre(nl, h, true, code_len(ct) as int + 8);
    assert(reaches(cp, m.pc as int, m, m3));
    if is_then {
        lemma_reaches_post(cp, ct, m.pc as int, m, m3);
        assert(pre + cx == cp + ct);
    } else {
        lemma_reaches_post(cp, ct + seq![b_i(code_len(ce) as int + 4)] + ce, m.pc as int, m, m3);
        assert(pre + cx == whole);
        assert(whole == cp + (ct + seq![b_i(code_len(ce) as int + 4)] + ce));
    }
    assert(reaches(pre + cx, m.pc as int, m, m3));
    lemma_lift_pre(lay, base, nl, offs, shift(offs, q), pre, cx, m, m3, o2);
    lemma_lift_post(lay, base, nl, offs, pre + cx, post, m, o2);
}

/// **`if`.** If the arms' code refines the arms, with the labels as the `if`
/// puts them (the `if`'s own label, at its end, in front), the `if`'s code
/// refines the `if`.
#[verifier::rlimit(150)]
pub proof fn lemma_if(
    t: Node,
    e: Node,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<isa::Instr>,
    ce: Seq<isa::Instr>,
)
    requires
        1 <= h,
        nl + h <= max_slots(),
        code_len(ct) < 0x8_0000,
        code_len(ce) < 0x8_0000,
        cf_refines(t@, nl, (h - 1) as nat, if_offs_t(nl, h, offs, ct, ce), ct),
        cf_refines(e@, nl, (h - 1) as nat, if_offs_e(nl, h, offs, ct, ce), ce),
    ensures
        cf_refines(
            Node::If(Box::new(t), Box::new(e))@,
            nl,
            h,
            offs,
            if_code(nl, h, ct, ce),
        ),
{
    let node = Node::If(Box::new(t), Box::new(e));
    let whole = if_code(nl, h, ct, ce);
    assert forall|
        lay: lir::Layout,
        base: Seq<lir::Val>,
        a: lir::St,
        m: isa::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, whole, m, lir::eval(lay, node@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl)
            && cf_canon(m.pc as int, offs, whole) implies cf_post(
        lay,
        base,
        nl,
        offs,
        whole,
        m,
        lir::eval(lay, node@, a, fuel),
    ) by {
        if fuel > 0 {
            let f = (fuel - 1) as nat;
            let n = a.stack.len();
            if n >= 1 {
                match a.stack[(n - 1) as int] {
                    lir::Val::I32(c) => {
                        let is_then = c != 0;
                        let arm = if is_then {
                            t
                        } else {
                            e
                        };
                        let a0 = a.with_stack(lir::below(a.stack, 1));
                        assert(f > 0 || lir::eval(lay, lir::Instr::Block(void_bt(), Box::new(arm@)), a0, f)
                            == lir::Outcome::OutOfFuel);
                        if f > 0 {
                            lemma_rel_base_unfold(lay, base, a, m, nl);
                            lemma_if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, c);
                            let m3 = choose|m3: isa::State|
                                if_head(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3);
                            lemma_eval_block(lay, arm, a0, f);
                            let g = (f - 1) as nat;
                            let cx = if_cx(is_then, ct, ce);
                            let offs_x = if_offs_x(is_then, nl, h, offs, ct, ce);
                            let q = if_q(is_then, nl, h, ct);
                            assert((base + a0.stack).len() + fresh(a0).stack.len() == (h - 1) as nat);
                            lemma_use_cf(
                                arm@,
                                nl,
                                (h - 1) as nat,
                                offs_x,
                                cx,
                                lay,
                                base + a0.stack,
                                fresh(a0),
                                m3,
                                g,
                            );
                            let o = lir::eval(lay, arm@, fresh(a0), g);
                            match o {
                                lir::Outcome::Normal(s) => {
                                    lemma_if_normal(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3, s);
                                },
                                lir::Outcome::Branch(k, s) => {
                                    if k == 0 {
                                        assert(lir::top(s.stack, 0) =~= Seq::<lir::Val>::empty());
                                        assert(a0.stack + lir::top(s.stack, 0) =~= a0.stack);
                                        lemma_if_br0(is_then, nl, h, offs, ct, ce, lay, base, a, m, m3, s);
                                    } else {
                                        assert(k < offs_x.len());
                                        assert(((k - 1) as nat) < shift(offs, q).len());
                                        assert(offs_x[k as int] == shift(offs, q)[((k - 1) as nat) as int]);
                                        lemma_blk_brn(
                                            lay,
                                            base,
                                            a0.stack,
                                            nl,
                                            shift(offs, q),
                                            cx,
                                            m3,
                                            k,
                                            s,
                                            offs_x,
                                        );
                                        lemma_if_out(
                                            is_then,
                                            nl,
                                            h,
                                            offs,
                                            ct,
                                            ce,
                                            lay,
                                            base,
                                            a,
                                            m,
                                            m3,
                                            o,
                                            lir::Outcome::Branch((k - 1) as nat, s),
                                        );
                                    }
                                },
                                lir::Outcome::Exit(code, vals, s) => {
                                    lemma_blk_exit(
                                        lay,
                                        base,
                                        a0.stack,
                                        nl,
                                        shift(offs, q),
                                        cx,
                                        m3,
                                        code,
                                        vals,
                                        s,
                                        offs_x,
                                    );
                                    lemma_if_out(
                                        is_then,
                                        nl,
                                        h,
                                        offs,
                                        ct,
                                        ce,
                                        lay,
                                        base,
                                        a,
                                        m,
                                        m3,
                                        o,
                                        lir::Outcome::Exit(code, vals, s),
                                    );
                                },
                                _ => {},
                            }
                        }
                    },
                    _ => {},
                }
            }
        }
    }
}

} // verus!
