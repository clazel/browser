//! Running a list of instructions ([`run_seq`]): how it behaves on a list
//! built from pieces. The A64 counterpart of [`crate::runseq`]; with no
//! `create_undef` and fixed-size instructions, [`run1`]`..`[`run5`] are the
//! lemmas the middles chain, and [`code_len`] is just `4 * len`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The length of the encodings of two lists is the sum of their lengths.
pub proof fn lemma_code_len_append(a: Seq<isa::Instr>, b: Seq<isa::Instr>)
    ensures
        code_len(a + b) == code_len(a) + code_len(b),
{
}

/// Running `a` then `b` is running `a`, then `b` from the state it reaches.
pub proof fn lemma_run_seq_append(s: isa::State, a: Seq<isa::Instr>, b: Seq<isa::Instr>)
    ensures
        run_seq(s, a + b) == match run_seq(s, a) {
            Some(s1) => run_seq(s1, b),
            None => None,
        },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        match isa::step(s, a[0]) {
            Some(s1) => {
                lemma_run_seq_append(s1, a.skip(1), b);
            },
            None => {},
        }
    }
}

/// Running a list that starts with `i` is a step by `i`, then the rest.
pub proof fn lemma_run_seq_cons(s: isa::State, i: isa::Instr, rest: Seq<isa::Instr>)
    ensures
        run_seq(s, seq![i] + rest) == match isa::step(s, i) {
            Some(s1) => run_seq(s1, rest),
            None => None,
        },
{
    let code = seq![i] + rest;
    assert(code.len() > 0);
    assert(code[0] == i);
    assert(code.skip(1) =~= rest);
}

/// Running one instruction is its step.
pub proof fn lemma_run_seq_one(s: isa::State, i: isa::Instr)
    ensures
        run_seq(s, seq![i]) == isa::step(s, i),
{
    let e = Seq::<isa::Instr>::empty();
    assert(seq![i] + e =~= seq![i]);
    lemma_run_seq_cons(s, i, e);
    match isa::step(s, i) {
        Some(s1) => {
            assert(run_seq(s1, e) == Some(s1));
        },
        None => {},
    }
}

/// A list of one instruction whose step is `s1`.
pub proof fn run1(s: isa::State, a: isa::Instr, s1: isa::State)
    requires
        isa::step(s, a) == Some(s1),
    ensures
        run_seq(s, seq![a]) == Some(s1),
{
    lemma_run_seq_one(s, a);
}

/// A list of two instructions whose steps are `s1` and `s2`.
pub proof fn run2(s: isa::State, a: isa::Instr, b: isa::Instr, s1: isa::State, s2: isa::State)
    requires
        isa::step(s, a) == Some(s1),
        isa::step(s1, b) == Some(s2),
    ensures
        run_seq(s, seq![a, b]) == Some(s2),
{
    run1(s1, b, s2);
    assert(seq![a, b] =~= seq![a] + seq![b]);
    lemma_run_seq_cons(s, a, seq![b]);
}

/// A list of three instructions whose steps are `s1`, `s2`, `s3`.
pub proof fn run3(
    s: isa::State,
    a: isa::Instr,
    b: isa::Instr,
    c: isa::Instr,
    s1: isa::State,
    s2: isa::State,
    s3: isa::State,
)
    requires
        isa::step(s, a) == Some(s1),
        isa::step(s1, b) == Some(s2),
        isa::step(s2, c) == Some(s3),
    ensures
        run_seq(s, seq![a, b, c]) == Some(s3),
{
    run2(s1, b, c, s2, s3);
    assert(seq![a, b, c] =~= seq![a] + seq![b, c]);
    lemma_run_seq_cons(s, a, seq![b, c]);
}

/// A list of four instructions whose steps are `s1` .. `s4`.
pub proof fn run4(
    s: isa::State,
    a: isa::Instr,
    b: isa::Instr,
    c: isa::Instr,
    d: isa::Instr,
    s1: isa::State,
    s2: isa::State,
    s3: isa::State,
    s4: isa::State,
)
    requires
        isa::step(s, a) == Some(s1),
        isa::step(s1, b) == Some(s2),
        isa::step(s2, c) == Some(s3),
        isa::step(s3, d) == Some(s4),
    ensures
        run_seq(s, seq![a, b, c, d]) == Some(s4),
{
    run3(s1, b, c, d, s2, s3, s4);
    assert(seq![a, b, c, d] =~= seq![a] + seq![b, c, d]);
    lemma_run_seq_cons(s, a, seq![b, c, d]);
}

} // verus!
