//! `if`: the condition test, a `je` over the first arm, the arms, and a `jmp`
//! over the second. LIR evaluates `if` as a void `block` around the arm the
//! condition picks, run with the condition popped, so the arm's label 0 is the
//! end of the whole `if`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfblock::*;
#[cfg(verus_only)]
use crate::cfcompose::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfheight::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::contract::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The length of the condition test.
pub open spec fn if_p(nl: nat, h: nat) -> int {
    cond_len(nl, h) as int
}

/// The code of an `if` whose arms have the code `ct` and `ce`.
pub open spec fn if_code(nl: nat, h: nat, ct: Seq<x64::Instr>, ce: Seq<x64::Instr>) -> Seq<
    x64::Instr,
> {
    cond_pre(nl, h, 4, code_len(ct) as int + 5) + ct + seq![jmp_i(code_len(ce) as int)] + ce
}

/// The labels in scope in the first arm: its own (the end of the `if`), then
/// the outer ones.
pub open spec fn if_offs_t(
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
) -> Seq<int> {
    seq![code_len(ct) as int + 5 + code_len(ce) as int] + shift(offs, if_p(nl, h))
}

/// The labels in scope in the second arm.
pub open spec fn if_offs_e(
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
) -> Seq<int> {
    seq![code_len(ce) as int] + shift(offs, if_p(nl, h) + code_len(ct) as int + 5)
}

/// A `jmp` in the middle of `pre + [jmp] + post`, reached at the end of `pre`,
/// is one step.
pub proof fn lemma_reach_jmp(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    m: x64::State,
    m4: x64::State,
    rel: int,
)
    requires
        m4.rip == m.rip + code_len(pre),
        x64::canonical(m4.rip + 5),
        x64::canonical(m4.rip + 5 + (rel as i32) as int),
    ensures
        reaches(
            cu,
            pre + seq![jmp_i(rel)] + post,
            m.rip,
            m4,
            x64::State { rip: m4.rip + 5 + (rel as i32) as int, ..m4 },
        ),
{
    let whole = pre + seq![jmp_i(rel)] + post;
    let m5 = x64::State { rip: m4.rip + 5 + (rel as i32) as int, ..m4 };
    assert(whole =~= pre + (seq![jmp_i(rel)] + post));
    lemma_fetch_append_r(pre, seq![jmp_i(rel)] + post, code_len(pre) as int);
    assert(code_len(pre) as int - code_len(pre) == 0);
    assert(fetch(seq![jmp_i(rel)] + post, 0) == Some(jmp_i(rel)));
    assert(m4.rip - m.rip == code_len(pre));
    lemma_step_jmp(cu, m4, rel);
    reveal_with_fuel(steps, 2);
    assert(steps(cu, whole, m.rip, m4, 1) == Some(m5));
}

/// `rel` survives a step that changes only `rip` and flags.
pub proof fn lemma_rel_regs_c2(
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


/// Where the arm starts, from the `if`'s first byte.
pub open spec fn if_q(is_then: bool, nl: nat, h: nat, ct: Seq<x64::Instr>) -> int {
    if is_then {
        if_p(nl, h)
    } else {
        if_p(nl, h) + code_len(ct) as int + 5
    }
}

/// The arm's code.
pub open spec fn if_cx(is_then: bool, ct: Seq<x64::Instr>, ce: Seq<x64::Instr>) -> Seq<x64::Instr> {
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
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
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
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
) -> Seq<x64::Instr> {
    let cp = cond_pre(nl, h, 4, code_len(ct) as int + 5);
    if is_then {
        cp
    } else {
        cp + ct + seq![jmp_i(code_len(ce) as int)]
    }
}

/// The code after the arm.
pub open spec fn if_post(
    is_then: bool,
    nl: nat,
    h: nat,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
) -> Seq<x64::Instr> {
    if is_then {
        seq![jmp_i(code_len(ce) as int)] + ce
    } else {
        Seq::empty()
    }
}

/// The whole code is the code before the arm, the arm, and the code after.
pub proof fn lemma_if_split(is_then: bool, nl: nat, h: nat, ct: Seq<x64::Instr>, ce: Seq<x64::Instr>)
    ensures
        if_pre(is_then, nl, h, ct, ce) + if_cx(is_then, ct, ce) + if_post(is_then, nl, h, ct, ce)
            == if_code(nl, h, ct, ce),
        code_len(if_pre(is_then, nl, h, ct, ce)) == if_q(is_then, nl, h, ct),
        code_len(if_code(nl, h, ct, ce)) == if_p(nl, h) + code_len(ct) + 5 + code_len(ce),
        if_code(nl, h, ct, ce) == cond_pre(nl, h, 4, code_len(ct) as int + 5) + (ct + seq![jmp_i(
            code_len(ce) as int,
        )] + ce),
        is_then ==> if_pre(is_then, nl, h, ct, ce) + if_cx(is_then, ct, ce) == cond_pre(
            nl,
            h,
            4,
            code_len(ct) as int + 5,
        ) + ct,
        !is_then ==> if_pre(is_then, nl, h, ct, ce) + if_cx(is_then, ct, ce) == if_code(
            nl,
            h,
            ct,
            ce,
        ),
{
    let cp = cond_pre(nl, h, 4, code_len(ct) as int + 5);
    let jm = jmp_i(code_len(ce) as int);
    lemma_cond_pre_len(nl, h, 4, code_len(ct) as int + 5);
    lemma_jmp_len(code_len(ce) as int);
    super::runseq::lemma_code_len_one(jm);
    super::runseq::lemma_code_len_append(cp, ct);
    super::runseq::lemma_code_len_append(cp + ct, seq![jm]);
    super::runseq::lemma_code_len_append(cp + ct + seq![jm], ce);
    assert(Seq::<x64::Instr>::empty() + ce =~= ce);
    assert(cp + ct + seq![jm] + ce =~= cp + (ct + seq![jm] + ce));
    if is_then {
        assert(cp + ct + (seq![jm] + ce) =~= cp + ct + seq![jm] + ce);
    } else {
        assert(cp + ct + seq![jm] + ce + Seq::<x64::Instr>::empty() =~= cp + ct + seq![jm] + ce);
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
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
) -> bool {
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let cx = if_cx(is_then, ct, ce);
    let q = if_q(is_then, nl, h, ct);
    &&& m3.rip == m.rip + q
    &&& reaches(cu, cond_pre(nl, h, 4, code_len(ct) as int + 5), m.rip, m, m3)
    &&& rel_base(lay, base + a0.stack, fresh(a0), m3, nl)
    &&& preserved_r(lay, m, m3)
    &&& stack_ok_r(lay, m3)
    &&& cf_canon(m3.rip, if_offs_x(is_then, nl, h, offs, ct, ce), cx)
}

/// **The head of an `if`**: the condition test and the `je` take the machine to
/// the start of the arm ([`if_head`]).
#[verifier::rlimit(400)]
pub proof fn lemma_if_head(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    c: u32,
)
    requires
        1 <= h,
        nl + h <= max_slots(),
        code_len(ct) < 0x4000_0000,
        code_len(ce) < 0x4000_0000,
        base.len() + a.stack.len() == h,
        a.stack.len() >= 1,
        a.stack[(a.stack.len() - 1) as int] == lir::Val::I32(c),
        (c != 0) == is_then,
        rel_base(lay, base, a, m, nl),
        stack_ok_r(lay, m),
        cf_canon(m.rip, offs, if_code(nl, h, ct, ce)),
    ensures
        exists|m3: x64::State| if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3),
{
    super::steps::lemma_abi_consts();
    lemma_if_split(is_then, nl, h, ct, ce);
    let p = if_p(nl, h);
    let st = code_len(ct) as int;
    let se = code_len(ce) as int;
    let cp = cond_pre(nl, h, 4, st + 5);
    let whole = if_code(nl, h, ct, ce);
    let ee = p + st + 5 + se;
    let j = (nl + h - 1) as nat;
    let i1 = load_slot(rax(), j);
    let i2 = x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() };
    let i3 = jcc_i(4, st + 5);
    let pre = seq![i1, i2];
    lemma_cond_pre_len(nl, h, 4, st + 5);
    lemma_jcc_len(4, st + 5);
    super::runseq::lemma_len3(i1, i2, i3);
    super::runseq::lemma_len2(i1, i2);
    assert(cp == pre + seq![i3]);
    assert(code_len(cp) == p);
    assert(code_len(pre) + 6 == p);
    lemma_rel_base_unfold(lay, base, a, m, nl);
    let ac = a.with_stack(base + a.stack);
    assert(ac.stack[(h - 1) as int] == lir::Val::I32(c));
    assert(x64::canonical(m.rip + ee));
    lemma_cond_test(cu, lay, ac, m, nl, h, c, ee as nat);
    let m2 = run_seq(cu, m, pre).unwrap();
    assert(m2.rip == m.rip + code_len(pre));
    assert(x64::canonical(m2.rip + 6)) by {
        super::runseq::lemma_canonical_between(m.rip, m.rip + p, m.rip + ee);
    }
    assert(x64::canonical(m2.rip + 6 + (st + 5))) by {
        super::runseq::lemma_canonical_between(m.rip, m.rip + p + st + 5, m.rip + ee);
    }
    lemma_step_jcc(cu, m2, 4, st + 5);
    let m3 = x64::step(cu, m2, i3).unwrap();
    assert(no_jumps(pre));
    lemma_reaches_plain_then(cu, pre, i3, m, m2, m3);
    let q = if_q(is_then, nl, h, ct);
    assert(m3.rip == m.rip + q);
    assert(reaches(cu, cp, m.rip, m, m3));
    // relation at m3
    lemma_rel_regs_c2(lay, ac, m2, m3, nl);
    let a0 = a.with_stack(lir::below(a.stack, 1));
    assert((base + a.stack).take((base + a0.stack).len() as int) =~= base + a0.stack);
    lemma_rel_prefix(lay, a, base + a.stack, base + a0.stack, m3, nl);
    lemma_preserved_same(lay, m, m3);
    lemma_table_pres(lay, m, m3);
    lemma_stack_pres(lay, m, m3);
    assert(a0.with_stack(base + a0.stack) == a.with_stack(base + a0.stack));
    reveal(rel_base);
    assert(rel_base(lay, base, a0, m3, nl));
    lemma_rel_base_enter(lay, base, a0, m3, nl);
    // the arm's labels are canonical
    let cx = if_cx(is_then, ct, ce);
    let offs_x = if_offs_x(is_then, nl, h, offs, ct, ce);
    assert(x64::canonical(m.rip));
    assert(code_len(cx) <= (if is_then { st } else { se }));
    super::runseq::lemma_canonical_between(m.rip, m3.rip + code_len(cx), m.rip + ee);
    assert forall|l: int| 0 <= l < offs_x.len() implies x64::canonical(
        m3.rip + #[trigger] offs_x[l],
    ) by {
        if l == 0 {
            assert(offs_x[0] == ee - q);
        } else {
            lemma_shift_index(offs, q, l - 1);
            assert(offs_x[l] == offs[l - 1] - q);
            assert(x64::canonical(m.rip + offs[l - 1]));
        }
    }
    assert(cf_canon(m3.rip, offs_x, cx));
    assert(if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3));
}


/// The condition test's run, in the whole `if`'s code.
pub proof fn lemma_head_reach_whole(
    nl: nat,
    h: nat,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    m3: x64::State,
)
    requires
        reaches(cu, cond_pre(nl, h, 4, code_len(ct) as int + 5), m.rip, m, m3),
    ensures
        reaches(cu, if_code(nl, h, ct, ce), m.rip, m, m3),
{
    lemma_if_split(true, nl, h, ct, ce);
    lemma_reaches_post(
        cu,
        cond_pre(nl, h, 4, code_len(ct) as int + 5),
        ct + seq![jmp_i(code_len(ce) as int)] + ce,
        m.rip,
        m,
        m3,
    );
}

/// The arm's reach, embedded in the whole `if`'s code, from the `if`'s start.
pub proof fn lemma_if_arm_reach(
    is_then: bool,
    nl: nat,
    h: nat,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    m3: x64::State,
    m4: x64::State,
)
    requires
        m3.rip == m.rip + if_q(is_then, nl, h, ct),
        reaches(cu, if_cx(is_then, ct, ce), m3.rip, m3, m4),
    ensures
        reaches(cu, if_code(nl, h, ct, ce), m.rip, m3, m4),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    let pre = if_pre(is_then, nl, h, ct, ce);
    let post = if_post(is_then, nl, h, ct, ce);
    let cx = if_cx(is_then, ct, ce);
    lemma_reaches_embed(cu, pre, cx, post, m3.rip, m3, m4);
    assert(m3.rip - code_len(pre) == m.rip);
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
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
    s: lir::St,
)
    requires
        if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3),
        cf_post(
            lay,
            base + a.with_stack(lir::below(a.stack, 1)).stack,
            nl,
            if_offs_x(is_then, nl, h, offs, ct, ce),
            if_cx(is_then, ct, ce),
            cu,
            m3,
            lir::Outcome::Normal(s),
        ),
    ensures
        exists|m4: x64::State|
            #![trigger reaches(cu, if_code(nl, h, ct, ce), m.rip, m, m4)]
            reaches(cu, if_code(nl, h, ct, ce), m.rip, m, m4) && m4.rip == m.rip + if_q(
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
    let m4 = choose|m4: x64::State|
        reaches(cu, cx, m3.rip, m3, m4) && m4.rip == m3.rip + code_len(cx) && rel_base(
            lay,
            base + a0.stack,
            s,
            m4,
            nl,
        ) && preserved_r(lay, m3, m4);
    lemma_head_reach_whole(nl, h, ct, ce, cu, m, m3);
    lemma_if_arm_reach(is_then, nl, h, ct, ce, cu, m, m3, m4);
    lemma_reaches_trans(cu, if_code(nl, h, ct, ce), m.rip, m, m3, m4);
    lemma_pr_trans(lay, m, m3, m4);
    lemma_rel_base_cat(lay, base, a0.stack, s, m4, nl);
}

/// **Running a `jmp` that follows code already run**: the machine at the end of
/// `pre`, in `pre + [jmp] + post`, takes the `jmp`, and stays related.
#[verifier::rlimit(100)]
pub proof fn lemma_jmp_finish(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    nl: nat,
    pre: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    m4: x64::State,
    sn: lir::St,
    se: int,
)
    requires
        reaches(cu, pre + seq![jmp_i(se)] + post, m.rip, m, m4),
        m4.rip == m.rip + code_len(pre),
        x64::canonical(m4.rip + 5),
        x64::canonical(m4.rip + 5 + (se as i32) as int),
        rel_base(lay, base, sn, m4, nl),
        preserved_r(lay, m, m4),
    ensures
        exists|m5: x64::State|
            #![trigger reaches(cu, pre + seq![jmp_i(se)] + post, m.rip, m, m5)]
            reaches(cu, pre + seq![jmp_i(se)] + post, m.rip, m, m5) && m5.rip == m4.rip + 5
                + (se as i32) as int && rel_base(lay, base, sn, m5, nl) && preserved_r(lay, m, m5),
{
    lemma_rel_base_unfold(lay, base, sn, m4, nl);
    lemma_reach_jmp(cu, pre, post, m, m4, se);
    let m5 = x64::State { rip: m4.rip + 5 + (se as i32) as int, ..m4 };
    lemma_reaches_trans(cu, pre + seq![jmp_i(se)] + post, m.rip, m, m4, m5);
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
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
    s: lir::St,
)
    requires
        code_len(ct) < 0x4000_0000,
        code_len(ce) < 0x4000_0000,
        x64::canonical(m.rip),
        cf_canon(m.rip, offs, if_code(nl, h, ct, ce)),
        if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3),
        cf_post(
            lay,
            base + a.with_stack(lir::below(a.stack, 1)).stack,
            nl,
            if_offs_x(is_then, nl, h, offs, ct, ce),
            if_cx(is_then, ct, ce),
            cu,
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
            cu,
            m,
            lir::Outcome::Normal(
                s.with_stack(a.with_stack(lir::below(a.stack, 1)).stack + s.stack),
            ),
        ),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    lemma_if_arm_end(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3, s);
    let p = if_p(nl, h);
    let st = code_len(ct) as int;
    let se = code_len(ce) as int;
    let whole = if_code(nl, h, ct, ce);
    let ee = p + st + 5 + se;
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let sn = s.with_stack(a0.stack + s.stack);
    let m4 = choose|m4: x64::State|
        reaches(cu, whole, m.rip, m, m4) && m4.rip == m.rip + if_q(is_then, nl, h, ct) + code_len(
            if_cx(is_then, ct, ce),
        ) && rel_base(lay, base, sn, m4, nl) && preserved_r(lay, m, m4);
    if is_then {
        let cp = cond_pre(nl, h, 4, st + 5);
        assert(m4.rip == m.rip + p + st);
        assert(x64::canonical(m4.rip + 5)) by {
            super::runseq::lemma_canonical_between(m.rip, m4.rip + 5, m.rip + ee);
        }
        assert(x64::canonical(m4.rip + 5 + (se as i32) as int)) by {
            super::runseq::lemma_canonical_between(m.rip, m4.rip + 5 + se, m.rip + ee);
        }
        assert(code_len(cp + ct) == p + st) by {
            lemma_cond_pre_len(nl, h, 4, st + 5);
            super::runseq::lemma_code_len_append(cp, ct);
        }
        assert(whole == (cp + ct) + seq![jmp_i(se)] + ce);
        lemma_jmp_finish(lay, base, nl, cp + ct, ce, cu, m, m4, sn, se);
    } else {
        assert(m4.rip == m.rip + ee);
    }
}

/// **A branch to the arm's own label** is the `if` ending.
pub proof fn lemma_if_br0(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
    s: lir::St,
)
    requires
        code_len(ct) < 0x4000_0000,
        code_len(ce) < 0x4000_0000,
        if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3),
        cf_post(
            lay,
            base + a.with_stack(lir::below(a.stack, 1)).stack,
            nl,
            if_offs_x(is_then, nl, h, offs, ct, ce),
            if_cx(is_then, ct, ce),
            cu,
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
            cu,
            m,
            lir::Outcome::Normal(s.with_stack(a.with_stack(lir::below(a.stack, 1)).stack)),
        ),
{
    lemma_if_split(is_then, nl, h, ct, ce);
    let a0 = a.with_stack(lir::below(a.stack, 1));
    let cx = if_cx(is_then, ct, ce);
    let offs_x = if_offs_x(is_then, nl, h, offs, ct, ce);
    let q = if_q(is_then, nl, h, ct);
    let ee = if_p(nl, h) + code_len(ct) as int + 5 + code_len(ce) as int;
    let m4 = choose|m4: x64::State|
        reaches(cu, cx, m3.rip, m3, m4) && m4.rip == m3.rip + offs_x[0] && rel_ext(
            lay,
            base + a0.stack,
            s,
            m4,
            nl,
        ) && preserved_r(lay, m3, m4);
    lemma_head_reach_whole(nl, h, ct, ce, cu, m, m3);
    lemma_if_arm_reach(is_then, nl, h, ct, ce, cu, m, m3, m4);
    lemma_reaches_trans(cu, if_code(nl, h, ct, ce), m.rip, m, m3, m4);
    lemma_pr_trans(lay, m, m3, m4);
    lemma_br0_rel(lay, base, a0.stack, s, m4, nl);
    assert(offs_x[0] == ee - q);
    assert(m4.rip == m.rip + ee);
}

/// **The arm branches past the `if`, or exits**: the outcome is the `if`'s,
/// seen from the start of the code.
pub proof fn lemma_if_out(
    is_then: bool,
    nl: nat,
    h: nat,
    offs: Seq<int>,
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
    lay: lir::Layout,
    cu: spec_fn(nat) -> nat,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    m3: x64::State,
    o: lir::Outcome,
    o2: lir::Outcome,
)
    requires
        code_len(ct) < 0x4000_0000,
        code_len(ce) < 0x4000_0000,
        !(o2 is Normal),
        if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3),
        stack_ok_r(lay, m),
        cf_post(
            lay,
            base,
            nl,
            shift(offs, if_q(is_then, nl, h, ct)),
            if_cx(is_then, ct, ce),
            cu,
            m3,
            o2,
        ),
    ensures
        cf_post(lay, base, nl, offs, if_code(nl, h, ct, ce), cu, m, o2),
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
    let cp = cond_pre(nl, h, 4, code_len(ct) as int + 5);
    assert(reaches(cu, cp, m.rip, m, m3));
    if is_then {
        lemma_reaches_post(cu, cp, ct, m.rip, m, m3);
        assert(pre + cx == cp + ct);
    } else {
        lemma_reaches_post(cu, cp, ct + seq![jmp_i(code_len(ce) as int)] + ce, m.rip, m, m3);
        assert(pre + cx == whole);
        assert(whole == cp + (ct + seq![jmp_i(code_len(ce) as int)] + ce));
    }
    assert(reaches(cu, pre + cx, m.rip, m, m3));
    lemma_lift_pre(lay, base, nl, offs, shift(offs, q), pre, cx, cu, m, m3, o2);
    lemma_lift_post(lay, base, nl, offs, pre + cx, post, cu, m, o2);
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
    ct: Seq<x64::Instr>,
    ce: Seq<x64::Instr>,
)
    requires
        1 <= h,
        nl + h <= max_slots(),
        code_len(ct) < 0x4000_0000,
        code_len(ce) < 0x4000_0000,
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
        cu: spec_fn(nat) -> nat,
        base: Seq<lir::Val>,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger cf_post(lay, base, nl, offs, whole, cu, m, lir::eval(lay, node@, a, fuel))]
        base.len() + a.stack.len() == h && rel_base(lay, base, a, m, nl) && stack_ok_r(lay, m)
            && cf_canon(m.rip, offs, whole) implies cf_post(
        lay,
        base,
        nl,
        offs,
        whole,
        cu,
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
                            lemma_if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, c);
                            let m3 = choose|m3: x64::State|
                                if_head(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3);
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
                                cu,
                                base + a0.stack,
                                fresh(a0),
                                m3,
                                g,
                            );
                            let o = lir::eval(lay, arm@, fresh(a0), g);
                            match o {
                                lir::Outcome::Normal(s) => {
                                    lemma_if_normal(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3, s);
                                },
                                lir::Outcome::Branch(k, s) => {
                                    if k == 0 {
                                        assert(lir::top(s.stack, 0) =~= Seq::<lir::Val>::empty());
                                        assert(a0.stack + lir::top(s.stack, 0) =~= a0.stack);
                                        lemma_if_br0(is_then, nl, h, offs, ct, ce, lay, cu, base, a, m, m3, s);
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
                                            cu,
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
                                            cu,
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
                                        cu,
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
                                        cu,
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
