//! Facts about [`fetch`], [`steps`] and [`reaches`]: a run in a piece of code
//! is a run in any list that contains it, runs compose, and a run of
//! jump-free code by [`run_seq`] is a run by [`steps`].

use crate::cfspec::*;
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `code` has no instruction that changes `rip` other than by its length:
/// no jump, no `ret`.
pub open spec fn no_jumps(code: Seq<x64::Instr>) -> bool {
    forall|j: int|
        0 <= j < code.len() ==> !(#[trigger] code[j] is Jcc || code[j] is Jmp || code[j] is Ret)
}

/// A step of an instruction that is not a jump or `ret` advances `rip` by
/// the instruction's length.
pub proof fn lemma_step_rip_plain(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    i: x64::Instr,
    s1: x64::State,
)
    requires
        x64::step(cu, s, i) == Some(s1),
        !(i is Jcc || i is Jmp || i is Ret),
    ensures
        s1.rip == s.rip + x64::instr_len(i),
{
}

/// `fetch` in a list sees the same instruction in the list followed by more.
pub proof fn lemma_fetch_append_l(a: Seq<x64::Instr>, b: Seq<x64::Instr>, off: int)
    requires
        fetch(a, off) is Some,
    ensures
        fetch(a + b, off) == fetch(a, off),
    decreases a.len(),
{
    if a.len() > 0 && off > 0 && off >= x64::instr_len(a[0]) as int {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        lemma_fetch_append_l(a.skip(1), b, off - x64::instr_len(a[0]) as int);
    }
}

/// `fetch` at or past the end of `a` is `fetch` in `b`.
pub proof fn lemma_fetch_append_r(a: Seq<x64::Instr>, b: Seq<x64::Instr>, off: int)
    requires
        off >= code_len(a),
    ensures
        fetch(a + b, off) == fetch(b, off - code_len(a)),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b).skip(1) =~= a.skip(1) + b);
        assert((a + b)[0] == a[0]);
        let l0 = x64::instr_len(a[0]) as int;
        assert(code_len(a) == l0 + code_len(a.skip(1)));
        assert(x64::instr_len(a[0]) > 0) by {
            lemma_instr_len_pos(a[0]);
        }
        lemma_fetch_append_r(a.skip(1), b, off - l0);
    }
}

/// An instruction is at least one byte.
#[verifier::rlimit(50)]
pub proof fn lemma_instr_len_pos(i: x64::Instr)
    ensures
        x64::instr_len(i) > 0,
{
    assert(x64::encode(i).len() > 0);
}


/// [`steps`] with the machine's step function abstracted, so that the
/// lemmas below, which are about fetching and counting, do not make the
/// solver unfold `x64::step` on an instruction it knows nothing about (the
/// device of [`crate::runseq::run_gen`]).
pub open spec fn steps_g(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    n: nat,
) -> Option<x64::State>
    decreases n,
{
    if n == 0 {
        Some(s)
    } else {
        match fetch(code, s.rip - base) {
            Some(i) => match f(s, i) {
                Some(s1) => steps_g(f, code, base, s1, (n - 1) as nat),
                None => None,
            },
            None => None,
        }
    }
}

/// [`steps`] is [`steps_g`] of the machine's step.
pub proof fn lemma_steps_is_gen(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    n: nat,
)
    ensures
        steps(cu, code, base, s, n) == steps_g(super::runseq::stepper(cu), code, base, s, n),
    decreases n,
{
    if n > 0 {
        match fetch(code, s.rip - base) {
            Some(i) => match x64::step(cu, s, i) {
                Some(s1) => {
                    lemma_steps_is_gen(cu, code, base, s1, (n - 1) as nat);
                },
                None => {},
            },
            None => {},
        }
    }
}

/// Generic [`lemma_steps_trans`].
pub proof fn lemma_steps_g_trans(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s1: x64::State,
    s2: x64::State,
    n1: nat,
    n2: nat,
)
    requires
        steps_g(f, code, base, s, n1) == Some(s1),
        steps_g(f, code, base, s1, n2) == Some(s2),
    ensures
        steps_g(f, code, base, s, n1 + n2) == Some(s2),
    decreases n1,
{
    if n1 > 0 {
        match fetch(code, s.rip - base) {
            Some(i) => match f(s, i) {
                Some(t) => {
                    lemma_steps_g_trans(f, code, base, t, s1, s2, (n1 - 1) as nat, n2);
                },
                None => {},
            },
            None => {},
        }
    }
}

/// Runs compose: `n1` steps, then `n2` more.
pub proof fn lemma_steps_trans(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s1: x64::State,
    s2: x64::State,
    n1: nat,
    n2: nat,
)
    requires
        steps(cu, code, base, s, n1) == Some(s1),
        steps(cu, code, base, s1, n2) == Some(s2),
    ensures
        steps(cu, code, base, s, n1 + n2) == Some(s2),
{
    let f = super::runseq::stepper(cu);
    lemma_steps_is_gen(cu, code, base, s, n1);
    lemma_steps_is_gen(cu, code, base, s1, n2);
    lemma_steps_is_gen(cu, code, base, s, n1 + n2);
    lemma_steps_g_trans(f, code, base, s, s1, s2, n1, n2);
}

/// [`reaches`] is transitive.
pub proof fn lemma_reaches_trans(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s1: x64::State,
    s2: x64::State,
)
    requires
        reaches(cu, code, base, s, s1),
        reaches(cu, code, base, s1, s2),
    ensures
        reaches(cu, code, base, s, s2),
{
    let n1 = choose|n: nat| steps(cu, code, base, s, n) == Some(s1);
    let n2 = choose|n: nat| steps(cu, code, base, s1, n) == Some(s2);
    lemma_steps_trans(cu, code, base, s, s1, s2, n1, n2);
}

/// Generic [`lemma_steps_embed`].
pub proof fn lemma_steps_g_embed(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    pre: Seq<x64::Instr>,
    c: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
    n: nat,
)
    requires
        steps_g(f, c, base, s, n) == Some(s2),
    ensures
        steps_g(f, pre + c + post, base - code_len(pre), s, n) == Some(s2),
    decreases n,
{
    if n > 0 {
        let off = s.rip - base;
        match fetch(c, off) {
            Some(i) => {
                lemma_fetch_append_l(c, post, off);
                assert(off >= 0);
                lemma_fetch_append_r(pre, c + post, off + code_len(pre));
                assert(pre + c + post =~= pre + (c + post));
                assert(off + code_len(pre) - code_len(pre) == off);
                assert(s.rip - (base - code_len(pre)) == off + code_len(pre));
                match f(s, i) {
                    Some(t) => {
                        lemma_steps_g_embed(f, pre, c, post, base, t, s2, (n - 1) as nat);
                    },
                    None => {},
                }
            },
            None => {},
        }
    }
}

/// **A run in a piece is a run in the whole.** If `c` placed at `base` runs
/// from `s` to `s2` in `n` steps, then `pre + c + post`, placed so that `c`
/// is where it was, does too.
pub proof fn lemma_steps_embed(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    c: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
    n: nat,
)
    requires
        steps(cu, c, base, s, n) == Some(s2),
    ensures
        steps(cu, pre + c + post, base - code_len(pre), s, n) == Some(s2),
{
    let f = super::runseq::stepper(cu);
    lemma_steps_is_gen(cu, c, base, s, n);
    lemma_steps_is_gen(cu, pre + c + post, base - code_len(pre), s, n);
    lemma_steps_g_embed(f, pre, c, post, base, s, s2, n);
}

/// [`reaches`] in a piece is [`reaches`] in the whole.
pub proof fn lemma_reaches_embed(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    c: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
)
    requires
        reaches(cu, c, base, s, s2),
    ensures
        reaches(cu, pre + c + post, base - code_len(pre), s, s2),
{
    let n = choose|n: nat| steps(cu, c, base, s, n) == Some(s2);
    lemma_steps_embed(cu, pre, c, post, base, s, s2, n);
}

/// The step function advances `rip` by the instruction's length for every
/// instruction that is not a jump or `ret`.
pub open spec fn rip_plain(f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>) -> bool {
    forall|s: x64::State, i: x64::Instr|
        !(i is Jcc || i is Jmp || i is Ret) ==> match #[trigger] f(s, i) {
            Some(s1) => s1.rip == s.rip + x64::instr_len(i),
            None => true,
        }
}

/// The machine's step is [`rip_plain`].
pub proof fn lemma_stepper_rip_plain(cu: spec_fn(nat) -> nat)
    ensures
        rip_plain(super::runseq::stepper(cu)),
{
    let f = super::runseq::stepper(cu);
    assert forall|s: x64::State, i: x64::Instr|
        !(i is Jcc || i is Jmp || i is Ret) implies match #[trigger] f(s, i) {
        Some(s1) => s1.rip == s.rip + x64::instr_len(i),
        None => true,
    } by {
        match x64::step(cu, s, i) {
            Some(s1) => {
                lemma_step_rip_plain(cu, s, i, s1);
            },
            None => {},
        }
    }
}

/// Generic [`lemma_run_seq_steps`].
pub proof fn lemma_run_gen_steps(
    f: spec_fn(x64::State, x64::Instr) -> Option<x64::State>,
    pre: Seq<x64::Instr>,
    code: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    b: int,
    s: x64::State,
    s2: x64::State,
)
    requires
        rip_plain(f),
        no_jumps(code),
        s.rip == b + code_len(pre),
        super::runseq::run_gen(f, s, code) == Some(s2),
    ensures
        steps_g(f, pre + code + post, b, s, code.len()) == Some(s2),
        s2.rip == s.rip + code_len(code),
    decreases code.len(),
{
    if code.len() == 0 {
    } else {
        let whole = pre + code + post;
        let i = code[0];
        assert(!(i is Jcc || i is Jmp || i is Ret));
        lemma_instr_len_pos(i);
        let off: int = code_len(pre) as int;
        assert(whole =~= pre + (code + post));
        lemma_fetch_append_r(pre, code + post, off);
        assert(code + post == seq![i] + (code.skip(1) + post)) by {
            assert((code + post).skip(1) =~= code.skip(1) + post);
        }
        assert(fetch(code + post, 0) == Some(i));
        assert(s.rip - b == off);
        match f(s, i) {
            Some(s1) => {
                assert(s1.rip == s.rip + x64::instr_len(i));
                let pre1 = pre + seq![i];
                let rest = code.skip(1);
                assert(code_len(pre1) == code_len(pre) + x64::instr_len(i)) by {
                    super::runseq::lemma_code_len_append(pre, seq![i]);
                    super::runseq::lemma_code_len_one(i);
                }
                assert(pre1 + rest + post =~= whole);
                assert(no_jumps(rest)) by {
                    assert forall|j: int| 0 <= j < rest.len() implies !(#[trigger] rest[j] is Jcc
                        || rest[j] is Jmp || rest[j] is Ret) by {
                        assert(rest[j] == code[j + 1]);
                    }
                }
                lemma_run_gen_steps(f, pre1, rest, post, b, s1, s2);
                assert(code_len(code) == x64::instr_len(i) + code_len(rest));
            },
            None => {},
        }
    }
}

/// **Jump-free code run by [`run_seq`] is run by [`steps`].** `whole` is
/// `pre + code + post` placed at `b`; the state is at the first byte of
/// `code`; the run of `code` by [`run_seq`] reaches `s2`.
pub proof fn lemma_run_seq_steps(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    code: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    b: int,
    s: x64::State,
    s2: x64::State,
)
    requires
        no_jumps(code),
        s.rip == b + code_len(pre),
        run_seq(cu, s, code) == Some(s2),
    ensures
        steps(cu, pre + code + post, b, s, code.len()) == Some(s2),
        s2.rip == s.rip + code_len(code),
{
    let f = super::runseq::stepper(cu);
    lemma_stepper_rip_plain(cu);
    super::runseq::lemma_run_seq_is_gen(cu, s, code);
    lemma_run_gen_steps(f, pre, code, post, b, s, s2);
    lemma_steps_is_gen(cu, pre + code + post, b, s, code.len());
}

/// [`reaches`] in code followed by more.
pub proof fn lemma_reaches_post(
    cu: spec_fn(nat) -> nat,
    c: Seq<x64::Instr>,
    post: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
)
    requires
        reaches(cu, c, base, s, s2),
    ensures
        reaches(cu, c + post, base, s, s2),
{
    assert(Seq::<x64::Instr>::empty() + c + post =~= c + post);
    assert(code_len(Seq::<x64::Instr>::empty()) == 0);
    lemma_reaches_embed(cu, Seq::empty(), c, post, base, s, s2);
}

/// [`reaches`] in code preceded by more (the base moves back).
pub proof fn lemma_reaches_pre(
    cu: spec_fn(nat) -> nat,
    pre: Seq<x64::Instr>,
    c: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
)
    requires
        reaches(cu, c, base, s, s2),
    ensures
        reaches(cu, pre + c, base - code_len(pre), s, s2),
{
    assert(pre + c + Seq::<x64::Instr>::empty() =~= pre + c);
    lemma_reaches_embed(cu, pre, c, Seq::empty(), base, s, s2);
}

} // verus!
