//! The shape of a memory instruction's run: operands, check, access, a `jmp`
//! over the stub, the stub. [`lemma_flow_pass`] says what a run that passes
//! the check does; [`lemma_flow_fail`] a run that leaves by an exit to the stub.

#[allow(unused_imports)]
use super::spec::*;
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
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The code of a memory instruction, from its five parts.
pub open spec fn flow_code(
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
) -> Seq<x64::Instr> {
    pre + cs + tail + seq![jmp_i(code_len(stub) as int)] + stub
}

/// A run in a piece is a run in the whole, when the piece is where the whole
/// puts it.
pub proof fn lemma_embed_mid(
    cu: spec_fn(nat) -> nat,
    pre_all: Seq<x64::Instr>,
    seg: Seq<x64::Instr>,
    post_all: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
)
    requires
        reaches(cu, seg, s.rip, s, s2),
        s.rip == base + code_len(pre_all),
    ensures
        reaches(cu, pre_all + seg + post_all, base, s, s2),
{
    lemma_reaches_embed(cu, pre_all, seg, post_all, s.rip, s, s2);
    assert(s.rip - code_len(pre_all) == base);
}

/// Jump-free code run by [`run_seq`] is a [`reaches`] of itself, placed at
/// the state's `rip`.
pub proof fn lemma_plain_reaches(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    s: x64::State,
    s2: x64::State,
)
    requires
        no_jumps(code),
        run_seq(cu, s, code) == Some(s2),
    ensures
        reaches(cu, code, s.rip, s, s2),
        s2.rip == s.rip + code_len(code),
{
    assert(Seq::<x64::Instr>::empty() + code + Seq::<x64::Instr>::empty() =~= code);
    assert(code_len(Seq::<x64::Instr>::empty()) == 0);
    lemma_run_seq_steps(cu, Seq::empty(), code, Seq::empty(), s.rip, s, s2);
}

/// The associativity facts the segments need: the whole code split at each
/// segment.
pub proof fn lemma_flow_assoc(
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    jm: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
)
    ensures
        pre + cs + tail + jm + stub == pre + cs + (tail + jm + stub),
        pre + cs + tail + jm + stub == pre + cs + tail + (jm + stub),
{
    vstd::seq_lib::lemma_concat_associative(pre + cs + tail, jm, stub);
    vstd::seq_lib::lemma_concat_associative(pre + cs, tail, jm + stub);
    vstd::seq_lib::lemma_concat_associative(tail, jm, stub);
    assert(tail + jm + stub == tail + (jm + stub));
    assert(pre + cs + tail + (jm + stub) == pre + cs + (tail + (jm + stub)));
}

/// A run in the operands is a run in the whole code.
pub proof fn lemma_flow_a(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    ma: x64::State,
)
    requires
        no_jumps(pre),
        run_seq(cu, m, pre) == Some(ma),
    ensures
        ma.rip == m.rip + code_len(pre),
        reaches(cu, flow_code(pre, cs, tail, stub), m.rip, m, ma),
{
    let jm = seq![jmp_i(code_len(stub) as int)];
    lemma_plain_reaches(cu, pre, m, ma);
    lemma_reaches_post(cu, pre, cs + tail + jm + stub, m.rip, m, ma);
    assert(pre + (cs + tail + jm + stub) =~= flow_code(pre, cs, tail, stub));
}

/// A run in the check is a run in the whole code.
pub proof fn lemma_flow_b(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    ma: x64::State,
    mb: x64::State,
)
    requires
        ma.rip == m.rip + code_len(pre),
        reaches(cu, cs, ma.rip, ma, mb),
    ensures
        reaches(cu, flow_code(pre, cs, tail, stub), m.rip, ma, mb),
{
    let jm = seq![jmp_i(code_len(stub) as int)];
    lemma_flow_assoc(pre, cs, tail, jm, stub);
    lemma_embed_mid(cu, pre, cs, tail + jm + stub, m.rip, ma, mb);
}

/// A run in the tail is a run in the whole code.
pub proof fn lemma_flow_c(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    mb: x64::State,
    mu: x64::State,
)
    requires
        no_jumps(tail),
        mb.rip == m.rip + code_len(pre) + code_len(cs),
        run_seq(cu, mb, tail) == Some(mu),
    ensures
        mu.rip == m.rip + code_len(pre) + code_len(cs) + code_len(tail),
        reaches(cu, flow_code(pre, cs, tail, stub), m.rip, mb, mu),
{
    let jm = seq![jmp_i(code_len(stub) as int)];
    super::runseq::lemma_code_len_append(pre, cs);
    lemma_plain_reaches(cu, tail, mb, mu);
    lemma_flow_assoc(pre, cs, tail, jm, stub);
    lemma_embed_mid(cu, pre + cs, tail, jm + stub, m.rip, mb, mu);
}

/// The operands, the check and the tail, run: the whole code reaches the
/// state the tail left, still before the `jmp`.
pub proof fn lemma_flow_upto(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    ma: x64::State,
    mb: x64::State,
    mu: x64::State,
)
    requires
        no_jumps(pre),
        no_jumps(tail),
        run_seq(cu, m, pre) == Some(ma),
        reaches(cu, cs, ma.rip, ma, mb),
        mb.rip == ma.rip + code_len(cs),
        run_seq(cu, mb, tail) == Some(mu),
    ensures
        mu.rip == m.rip + code_len(pre) + code_len(cs) + code_len(tail),
        reaches(cu, flow_code(pre, cs, tail, stub), m.rip, m, mu),
{
    let whole = flow_code(pre, cs, tail, stub);
    lemma_flow_a(cu, pre, cs, tail, stub, m, ma);
    lemma_flow_b(cu, pre, cs, tail, stub, m, ma, mb);
    lemma_reaches_trans(cu, whole, m.rip, m, ma, mb);
    lemma_flow_c(cu, pre, cs, tail, stub, m, mb, mu);
    lemma_reaches_trans(cu, whole, m.rip, m, mb, mu);
}

/// The `jmp` over the stub, from the state the tail left.
#[verifier::rlimit(500)]
pub proof fn lemma_flow_jmp(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    mu: x64::State,
)
    requires
        reaches(cu, flow_code(pre, cs, tail, stub), m.rip, m, mu),
        mu.rip == m.rip + code_len(pre) + code_len(cs) + code_len(tail),
        x64::canonical(m.rip + code_len(flow_code(pre, cs, tail, stub))),
        x64::canonical(m.rip),
        code_len(stub) < 0x8000_0000,
    ensures
        reaches(
            cu,
            flow_code(pre, cs, tail, stub),
            m.rip,
            m,
            x64::State { rip: m.rip + code_len(flow_code(pre, cs, tail, stub)), ..mu },
        ),
{
    let jm = seq![jmp_i(code_len(stub) as int)];
    let whole = flow_code(pre, cs, tail, stub);
    lemma_stub_start(pre, cs, tail, stub);
    let rel = code_len(stub) as int;
    let end = m.rip + code_len(whole);
    assert(mu.rip + 5 + rel == end);
    super::runseq::lemma_canonical_between(m.rip, mu.rip + 5, end);
    super::runseq::lemma_canonical_between(m.rip, mu.rip, end);
    assert((rel as i32) as int == rel);
    lemma_step_jmp(cu, mu, rel);
    let me = x64::State { rip: end, ..mu };
    assert(x64::step(cu, mu, jmp_i(rel)) == Some(me));
    assert(fetch(jm, 0) == Some(jmp_i(rel)));
    reveal_with_fuel(steps, 2);
    assert(steps(cu, jm, mu.rip, mu, 1) == Some(me));
    assert(reaches(cu, jm, mu.rip, mu, me));
    assert(pre + cs + tail + jm + stub =~= whole);
    super::runseq::lemma_code_len_append(pre, cs);
    super::runseq::lemma_code_len_append(pre + cs, tail);
    lemma_embed_mid(cu, pre + cs + tail, jm, stub, m.rip, mu, me);
    lemma_reaches_trans(cu, whole, m.rip, m, mu, me);
}

/// **A run that passes the check.** The operands run (`pre`, jump-free), the
/// check falls through, the tail runs (jump-free), and the `jmp` skips the
/// stub: the whole code reaches the state at its end that the tail left, with
/// only `rip` moved.
pub proof fn lemma_flow_pass(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    ma: x64::State,
    mb: x64::State,
    mu: x64::State,
)
    requires
        no_jumps(pre),
        no_jumps(tail),
        run_seq(cu, m, pre) == Some(ma),
        reaches(cu, cs, ma.rip, ma, mb),
        mb.rip == ma.rip + code_len(cs),
        run_seq(cu, mb, tail) == Some(mu),
        x64::canonical(m.rip + code_len(flow_code(pre, cs, tail, stub))),
        x64::canonical(m.rip),
        code_len(stub) < 0x8000_0000,
    ensures
        mu.rip == m.rip + code_len(pre) + code_len(cs) + code_len(tail),
        reaches(
            cu,
            flow_code(pre, cs, tail, stub),
            m.rip,
            m,
            x64::State { rip: m.rip + code_len(flow_code(pre, cs, tail, stub)), ..mu },
        ),
{
    lemma_flow_upto(cu, pre, cs, tail, stub, m, ma, mb, mu);
    lemma_flow_jmp(cu, pre, cs, tail, stub, m, mu);
}

/// **A run that leaves the check by an exit**: the whole code reaches the
/// state `ms` at the start of the stub, when the operands ran and the check
/// reached `ms` there.
pub proof fn lemma_flow_fail(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
    m: x64::State,
    ma: x64::State,
    ms: x64::State,
)
    requires
        no_jumps(pre),
        run_seq(cu, m, pre) == Some(ma),
        reaches(cu, cs, ma.rip, ma, ms),
    ensures
        reaches(cu, flow_code(pre, cs, tail, stub), m.rip, m, ms),
{
    let whole = flow_code(pre, cs, tail, stub);
    lemma_flow_a(cu, pre, cs, tail, stub, m, ma);
    lemma_flow_b(cu, pre, cs, tail, stub, m, ma, ms);
    lemma_reaches_trans(cu, whole, m.rip, m, ma, ms);
}

/// The stub starts after everything else.
pub proof fn lemma_stub_start(
    pre: Seq<x64::Instr>,
    cs: Seq<x64::Instr>,
    tail: Seq<x64::Instr>,
    stub: Seq<x64::Instr>,
)
    ensures
        code_len(flow_code(pre, cs, tail, stub)) == code_len(pre) + code_len(cs) + code_len(tail)
            + 5 + code_len(stub),
{
    let jm = seq![jmp_i(code_len(stub) as int)];
    super::runseq::lemma_code_len_append(pre, cs);
    super::runseq::lemma_code_len_append(pre + cs, tail);
    super::runseq::lemma_code_len_append(pre + cs + tail, jm);
    super::runseq::lemma_code_len_append(pre + cs + tail + jm, stub);
    super::runseq::lemma_code_len_one(jmp_i(code_len(stub) as int));
    lemma_jmp_len(code_len(stub) as int);
}

} // verus!
