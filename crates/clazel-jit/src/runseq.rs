//! Facts about [`run_seq`], [`code_len`] and the machine states a run passes
//! through: running a concatenation is running one list and then the other,
//! lengths add, and `rip` stays canonical along the way.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `code_len` of a concatenation.
pub proof fn lemma_code_len_append(a: Seq<x64::Instr>, b: Seq<x64::Instr>)
    ensures
        code_len(a + b) == code_len(a) + code_len(b),
    decreases a.len(),
{
    if a.len() > 0 {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        lemma_code_len_append(a.skip(1), b);
    } else {
        assert(a + b =~= b);
    }
}

/// Running `a + b` is running `a`, then `b` from where `a` ended (and a
/// fault in `a` is a fault).
pub proof fn lemma_run_seq_append(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    a: Seq<x64::Instr>,
    b: Seq<x64::Instr>,
)
    ensures
        run_seq(cu, s, a + b) == match run_seq(cu, s, a) {
            Some(s1) => run_seq(cu, s1, b),
            None => None,
        },
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        match x64::step(cu, s, a[0]) {
            Some(s1) => {
                lemma_run_seq_append(cu, s1, a.skip(1), b);
            },
            None => {},
        }
    }
}

/// A one-instruction run is the step.
pub proof fn lemma_run_seq_one(cu: spec_fn(nat) -> nat, s: x64::State, i: x64::Instr)
    ensures
        run_seq(cu, s, seq![i]) == x64::step(cu, s, i),
{
    let e = Seq::<x64::Instr>::empty();
    assert(seq![i].len() == 1);
    assert(seq![i][0] == i);
    assert(seq![i].skip(1) =~= e);
    match x64::step(cu, s, i) {
        Some(s1) => {
            assert(run_seq(cu, s1, e) == Some(s1));
        },
        None => {},
    }
}

/// The code length of a one-instruction list.
pub proof fn lemma_code_len_one(i: x64::Instr)
    ensures
        code_len(seq![i]) == x64::instr_len(i),
{
    let e = Seq::<x64::Instr>::empty();
    assert(seq![i].len() == 1);
    assert(seq![i][0] == i);
    assert(seq![i].skip(1) =~= e);
    assert(code_len(e) == 0);
}

/// An address between two canonical addresses is canonical.
pub proof fn lemma_canonical_between(lo: int, mid: int, hi: int)
    requires
        x64::canonical(lo),
        x64::canonical(hi),
        lo <= mid <= hi,
    ensures
        x64::canonical(mid),
{
}

/// Running an instruction followed by more: the step, then the rest.
pub proof fn lemma_run_seq_cons(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    i: x64::Instr,
    rest: Seq<x64::Instr>,
)
    ensures
        run_seq(cu, s, seq![i] + rest) == match x64::step(cu, s, i) {
            Some(s1) => run_seq(cu, s1, rest),
            None => None,
        },
        code_len(seq![i] + rest) == x64::instr_len(i) + code_len(rest),
{
    let code = seq![i] + rest;
    assert(code.len() > 0);
    assert(code[0] == i);
    assert(code.skip(1) =~= rest);
}

/// [`run_seq`] with the step function abstracted: the lemmas about long
/// instruction lists are proven for an arbitrary `f`, so the solver does not
/// unfold `x64::step` on instructions it knows nothing about.
pub open spec fn run_gen(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    s: x64::State,
    code: Seq<x64::Instr>,
) -> Option<x64::State>
    decreases code.len(),
{
    if code.len() == 0 {
        Some(s)
    } else {
        match f(s, code[0]) {
            Some(s1) => run_gen(f, s1, code.skip(1)),
            None => None,
        }
    }
}

/// The machine's step as a function value.
pub open spec fn stepper(cu: spec_fn(nat) -> nat) -> spec_fn(x64::State, x64::Instr) -> Option<
    x64::State,
> {
    |s1: x64::State, i: x64::Instr| x64::step(cu, s1, i)
}

/// `run_seq` is `run_gen` for the machine's step.
pub proof fn lemma_run_seq_is_gen(cu: spec_fn(nat) -> nat, s: x64::State, code: Seq<x64::Instr>)
    ensures
        run_seq(cu, s, code) == run_gen(stepper(cu), s, code),
    decreases code.len(),
{
    if code.len() > 0 {
        match x64::step(cu, s, code[0]) {
            Some(s1) => {
                lemma_run_seq_is_gen(cu, s1, code.skip(1));
            },
            None => {},
        }
    }
}

/// A list is its head consed on its tail. Generic in the element type, so the
/// solver does not unfold `Instr`.
pub proof fn lemma_seq_cons<A>(whole: Seq<A>, x: A, rest: Seq<A>)
    requires
        whole.len() == rest.len() + 1,
        whole[0] == x,
        forall|k: int| 0 <= k < rest.len() ==> #[trigger] whole[k + 1] == rest[k],
    ensures
        whole =~= seq![x] + rest,
{
    assert forall|k: int| 0 <= k < whole.len() implies whole[k] == (seq![x] + rest)[k] by {
        if k > 0 {
            assert(whole[(k - 1) + 1] == rest[k - 1]);
        }
    }
}

/// The code length of a list is its head's length and its tail's.
pub proof fn lemma_code_len_cons(i: x64::Instr, rest: Seq<x64::Instr>)
    ensures
        code_len(seq![i] + rest) == x64::instr_len(i) + code_len(rest),
{
    let code = seq![i] + rest;
    assert(code.len() > 0);
    assert(code[0] == i);
    assert(code.skip(1) =~= rest);
}

/// `run_gen` of a list is the head's step, then the tail.
pub proof fn lemma_run_gen_cons(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    s: x64::State,
    i: x64::Instr,
    rest: Seq<x64::Instr>,
)
    ensures
        run_gen(f, s, seq![i] + rest) == match f(s, i) {
            Some(s1) => run_gen(f, s1, rest),
            None => None,
        },
{
    let code = seq![i] + rest;
    assert(code.len() > 0);
    assert(code[0] == i);
    assert(code.skip(1) =~= rest);
}

/// `run_gen` of a list of 1 instruction whose steps are known.
pub proof fn lemma_gen1(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>, s: x64::State, a: x64::Instr, s1: x64::State)
    requires
        f(s, a) == Some(s1),
    ensures
        run_gen(f, s, seq![a]) == Some(s1),
{
    let e = Seq::<x64::Instr>::empty();
    lemma_seq_cons(seq![a], a, e);
    lemma_run_gen_cons(f, s, a, e);
}

/// The code length of a list of 1 instruction.
pub proof fn lemma_len1(a: x64::Instr)
    ensures
        code_len(seq![a]) == x64::instr_len(a),
{
    let e = Seq::<x64::Instr>::empty();
    lemma_seq_cons(seq![a], a, e);
    lemma_code_len_cons(a, e);
}

/// `run_gen` of a list of 2 instructions whose steps are known.
pub proof fn lemma_gen2(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>, s: x64::State, a: x64::Instr, b: x64::Instr, s1: x64::State, s2: x64::State)
    requires
        f(s, a) == Some(s1),
        f(s1, b) == Some(s2),
    ensures
        run_gen(f, s, seq![a, b]) == Some(s2),
{
    lemma_gen1(f, s1, b, s2);
    lemma_seq_cons(seq![a, b], a, seq![b]);
    lemma_run_gen_cons(f, s, a, seq![b]);
}

/// The code length of a list of 2 instructions.
pub proof fn lemma_len2(a: x64::Instr, b: x64::Instr)
    ensures
        code_len(seq![a, b]) == x64::instr_len(a) + x64::instr_len(b),
{
    lemma_len1(b);
    lemma_seq_cons(seq![a, b], a, seq![b]);
    lemma_code_len_cons(a, seq![b]);
}

/// `run_gen` of a list of 3 instructions whose steps are known.
pub proof fn lemma_gen3(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>, s: x64::State, a: x64::Instr, b: x64::Instr, c: x64::Instr, s1: x64::State, s2: x64::State, s3: x64::State)
    requires
        f(s, a) == Some(s1),
        f(s1, b) == Some(s2),
        f(s2, c) == Some(s3),
    ensures
        run_gen(f, s, seq![a, b, c]) == Some(s3),
{
    lemma_gen2(f, s1, b, c, s2, s3);
    lemma_seq_cons(seq![a, b, c], a, seq![b, c]);
    lemma_run_gen_cons(f, s, a, seq![b, c]);
}

/// The code length of a list of 3 instructions.
pub proof fn lemma_len3(a: x64::Instr, b: x64::Instr, c: x64::Instr)
    ensures
        code_len(seq![a, b, c]) == x64::instr_len(a) + x64::instr_len(b) + x64::instr_len(c),
{
    lemma_len2(b, c);
    lemma_seq_cons(seq![a, b, c], a, seq![b, c]);
    lemma_code_len_cons(a, seq![b, c]);
}

/// `run_gen` of a list of 4 instructions whose steps are known.
pub proof fn lemma_gen4(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>, s: x64::State, a: x64::Instr, b: x64::Instr, c: x64::Instr, d: x64::Instr, s1: x64::State, s2: x64::State, s3: x64::State, s4: x64::State)
    requires
        f(s, a) == Some(s1),
        f(s1, b) == Some(s2),
        f(s2, c) == Some(s3),
        f(s3, d) == Some(s4),
    ensures
        run_gen(f, s, seq![a, b, c, d]) == Some(s4),
{
    lemma_gen3(f, s1, b, c, d, s2, s3, s4);
    lemma_seq_cons(seq![a, b, c, d], a, seq![b, c, d]);
    lemma_run_gen_cons(f, s, a, seq![b, c, d]);
}

/// The code length of a list of 4 instructions.
pub proof fn lemma_len4(a: x64::Instr, b: x64::Instr, c: x64::Instr, d: x64::Instr)
    ensures
        code_len(seq![a, b, c, d]) == x64::instr_len(a) + x64::instr_len(b) + x64::instr_len(c) + x64::instr_len(d),
{
    lemma_len3(b, c, d);
    lemma_seq_cons(seq![a, b, c, d], a, seq![b, c, d]);
    lemma_code_len_cons(a, seq![b, c, d]);
}

/// `run_gen` of a list of 5 instructions whose steps are known.
pub proof fn lemma_gen5(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>, s: x64::State, a: x64::Instr, b: x64::Instr, c: x64::Instr, d: x64::Instr, e: x64::Instr, s1: x64::State, s2: x64::State, s3: x64::State, s4: x64::State, s5: x64::State)
    requires
        f(s, a) == Some(s1),
        f(s1, b) == Some(s2),
        f(s2, c) == Some(s3),
        f(s3, d) == Some(s4),
        f(s4, e) == Some(s5),
    ensures
        run_gen(f, s, seq![a, b, c, d, e]) == Some(s5),
{
    lemma_gen4(f, s1, b, c, d, e, s2, s3, s4, s5);
    lemma_seq_cons(seq![a, b, c, d, e], a, seq![b, c, d, e]);
    lemma_run_gen_cons(f, s, a, seq![b, c, d, e]);
}

/// The code length of a list of 5 instructions.
pub proof fn lemma_len5(a: x64::Instr, b: x64::Instr, c: x64::Instr, d: x64::Instr, e: x64::Instr)
    ensures
        code_len(seq![a, b, c, d, e]) == x64::instr_len(a) + x64::instr_len(b) + x64::instr_len(c) + x64::instr_len(d) + x64::instr_len(e),
{
    lemma_len4(b, c, d, e);
    lemma_seq_cons(seq![a, b, c, d, e], a, seq![b, c, d, e]);
    lemma_code_len_cons(a, seq![b, c, d, e]);
}

/// `run_gen` of a list of 6 instructions whose steps are known.
pub proof fn lemma_gen6(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>, s: x64::State, a: x64::Instr, b: x64::Instr, c: x64::Instr, d: x64::Instr, e: x64::Instr, g: x64::Instr, s1: x64::State, s2: x64::State, s3: x64::State, s4: x64::State, s5: x64::State, s6: x64::State)
    requires
        f(s, a) == Some(s1),
        f(s1, b) == Some(s2),
        f(s2, c) == Some(s3),
        f(s3, d) == Some(s4),
        f(s4, e) == Some(s5),
        f(s5, g) == Some(s6),
    ensures
        run_gen(f, s, seq![a, b, c, d, e, g]) == Some(s6),
{
    lemma_gen5(f, s1, b, c, d, e, g, s2, s3, s4, s5, s6);
    lemma_seq_cons(seq![a, b, c, d, e, g], a, seq![b, c, d, e, g]);
    lemma_run_gen_cons(f, s, a, seq![b, c, d, e, g]);
}

/// The code length of a list of 6 instructions.
pub proof fn lemma_len6(a: x64::Instr, b: x64::Instr, c: x64::Instr, d: x64::Instr, e: x64::Instr, g: x64::Instr)
    ensures
        code_len(seq![a, b, c, d, e, g]) == x64::instr_len(a) + x64::instr_len(b) + x64::instr_len(c) + x64::instr_len(d) + x64::instr_len(e) + x64::instr_len(g),
{
    lemma_len5(b, c, d, e, g);
    lemma_seq_cons(seq![a, b, c, d, e, g], a, seq![b, c, d, e, g]);
    lemma_code_len_cons(a, seq![b, c, d, e, g]);
}

} // verus!
