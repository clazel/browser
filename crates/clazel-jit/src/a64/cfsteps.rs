//! Facts about [`fetch`], [`steps`] and [`reaches`]: a run in a piece of code
//! is a run in any list that contains it, runs compose, and a run of
//! jump-free code by [`run_seq`] is a run by [`steps`]. The A64 counterpart of
//! [`crate::cfsteps`]; every instruction is 4 bytes, so `fetch` is an index.

#[cfg(verus_only)]
use super::cfspec::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `code` has no instruction that changes `pc` other than by 4: no branch, no
/// `ret`.
pub open spec fn no_jumps(code: Seq<isa::Instr>) -> bool {
    forall|j: int| 0 <= j < code.len() ==> !is_jump(#[trigger] code[j])
}

/// A branch or `ret`.
pub open spec fn is_jump(i: isa::Instr) -> bool {
    i is B || i is BCond || i is CompareBranch || i is Ret
}

/// A step of an instruction that is not a jump advances `pc` by 4 (when that
/// does not wrap).
pub proof fn lemma_step_pc_plain(s: isa::State, i: isa::Instr, s1: isa::State)
    requires
        isa::step(s, i) == Some(s1),
        !is_jump(i),
        s.pc as int + 4 < isa::p2(64),
    ensures
        s1.pc as int == s.pc as int + 4,
{
    super::memlemmas::lemma_p2_consts();
    super::memlemmas::lemma_trunc64(s.pc as int + 4);
}

/// `fetch` in a list sees the same instruction in the list followed by more.
pub proof fn lemma_fetch_append_l(a: Seq<isa::Instr>, b: Seq<isa::Instr>, off: int)
    requires
        fetch(a, off) is Some,
    ensures
        fetch(a + b, off) == fetch(a, off),
{
}

/// `fetch` at or past the end of `a` is `fetch` in `b`.
pub proof fn lemma_fetch_append_r(a: Seq<isa::Instr>, b: Seq<isa::Instr>, off: int)
    requires
        off >= code_len(a),
    ensures
        fetch(a + b, off) == fetch(b, off - code_len(a)),
{
    assert(code_len(a) == 4 * a.len());
    let off2 = off - 4 * a.len();
    assert(off % 4 == off2 % 4);
    assert(off / 4 == off2 / 4 + a.len());
    if 0 <= off2 && off2 % 4 == 0 && off2 / 4 < b.len() {
        assert((a + b)[off / 4] == b[off2 / 4]);
    }
}

/// [`steps`] with the machine's step function abstracted, so that the lemmas
/// below, which are about fetching and counting, do not make the solver unfold
/// `isa::step` on an instruction it knows nothing about.
pub open spec fn steps_g(
    f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>,
    code: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    n: nat,
) -> Option<isa::State>
    decreases n,
{
    if n == 0 {
        Some(s)
    } else {
        match fetch(code, s.pc as int - base) {
            Some(i) => match f(s, i) {
                Some(s1) => steps_g(f, code, base, s1, (n - 1) as nat),
                None => None,
            },
            None => None,
        }
    }
}

/// The machine's step as a function value.
pub open spec fn stepper() -> spec_fn(isa::State, isa::Instr) -> Option<isa::State> {
    |s: isa::State, i: isa::Instr| isa::step(s, i)
}

/// Running a list by an abstract step function (as [`run_seq`]).
pub open spec fn run_gen(
    f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>,
    s: isa::State,
    code: Seq<isa::Instr>,
) -> Option<isa::State>
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

/// [`run_seq`] is [`run_gen`] of the machine's step.
pub proof fn lemma_run_seq_is_gen(s: isa::State, code: Seq<isa::Instr>)
    ensures
        run_seq(s, code) == run_gen(stepper(), s, code),
    decreases code.len(),
{
    if code.len() > 0 {
        match isa::step(s, code[0]) {
            Some(s1) => {
                lemma_run_seq_is_gen(s1, code.skip(1));
            },
            None => {},
        }
    }
}

/// [`steps`] is [`steps_g`] of the machine's step.
pub proof fn lemma_steps_is_gen(code: Seq<isa::Instr>, base: int, s: isa::State, n: nat)
    ensures
        steps(code, base, s, n) == steps_g(stepper(), code, base, s, n),
    decreases n,
{
    if n > 0 {
        match fetch(code, s.pc as int - base) {
            Some(i) => match isa::step(s, i) {
                Some(s1) => {
                    lemma_steps_is_gen(code, base, s1, (n - 1) as nat);
                },
                None => {},
            },
            None => {},
        }
    }
}

/// Generic [`lemma_steps_trans`].
pub proof fn lemma_steps_g_trans(
    f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>,
    code: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s1: isa::State,
    s2: isa::State,
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
        match fetch(code, s.pc as int - base) {
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
    code: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s1: isa::State,
    s2: isa::State,
    n1: nat,
    n2: nat,
)
    requires
        steps(code, base, s, n1) == Some(s1),
        steps(code, base, s1, n2) == Some(s2),
    ensures
        steps(code, base, s, n1 + n2) == Some(s2),
{
    let f = stepper();
    lemma_steps_is_gen(code, base, s, n1);
    lemma_steps_is_gen(code, base, s1, n2);
    lemma_steps_is_gen(code, base, s, n1 + n2);
    lemma_steps_g_trans(f, code, base, s, s1, s2, n1, n2);
}

/// [`reaches`] is transitive.
pub proof fn lemma_reaches_trans(
    code: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s1: isa::State,
    s2: isa::State,
)
    requires
        reaches(code, base, s, s1),
        reaches(code, base, s1, s2),
    ensures
        reaches(code, base, s, s2),
{
    let n1 = choose|n: nat| steps(code, base, s, n) == Some(s1);
    let n2 = choose|n: nat| steps(code, base, s1, n) == Some(s2);
    lemma_steps_trans(code, base, s, s1, s2, n1, n2);
}

/// Generic [`lemma_steps_embed`].
pub proof fn lemma_steps_g_embed(
    f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>,
    pre: Seq<isa::Instr>,
    c: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s2: isa::State,
    n: nat,
)
    requires
        steps_g(f, c, base, s, n) == Some(s2),
    ensures
        steps_g(f, pre + c + post, base - code_len(pre), s, n) == Some(s2),
    decreases n,
{
    if n > 0 {
        let off = s.pc as int - base;
        match fetch(c, off) {
            Some(i) => {
                lemma_fetch_append_l(c, post, off);
                assert(off >= 0);
                lemma_fetch_append_r(pre, c + post, off + code_len(pre));
                assert(pre + c + post =~= pre + (c + post));
                assert(off + code_len(pre) - code_len(pre) == off);
                assert(s.pc as int - (base - code_len(pre)) == off + code_len(pre));
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
    pre: Seq<isa::Instr>,
    c: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s2: isa::State,
    n: nat,
)
    requires
        steps(c, base, s, n) == Some(s2),
    ensures
        steps(pre + c + post, base - code_len(pre), s, n) == Some(s2),
{
    let f = stepper();
    lemma_steps_is_gen(c, base, s, n);
    lemma_steps_is_gen(pre + c + post, base - code_len(pre), s, n);
    lemma_steps_g_embed(f, pre, c, post, base, s, s2, n);
}

/// [`reaches`] in a piece is [`reaches`] in the whole.
pub proof fn lemma_reaches_embed(
    pre: Seq<isa::Instr>,
    c: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s2: isa::State,
)
    requires
        reaches(c, base, s, s2),
    ensures
        reaches(pre + c + post, base - code_len(pre), s, s2),
{
    let n = choose|n: nat| steps(c, base, s, n) == Some(s2);
    lemma_steps_embed(pre, c, post, base, s, s2, n);
}

/// The step function advances `pc` by 4 for every instruction that is not a
/// jump, from a `pc` at which that does not wrap.
pub open spec fn pc_plain(f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>) -> bool {
    forall|s: isa::State, i: isa::Instr|
        !is_jump(i) && s.pc as int + 4 < isa::p2(64) ==> match #[trigger] f(s, i) {
            Some(s1) => s1.pc as int == s.pc as int + 4,
            None => true,
        }
}

/// The machine's step is [`pc_plain`].
pub proof fn lemma_stepper_pc_plain()
    ensures
        pc_plain(stepper()),
{
    let f = stepper();
    assert forall|s: isa::State, i: isa::Instr|
        !is_jump(i) && s.pc as int + 4 < isa::p2(64) implies match #[trigger] f(s, i) {
        Some(s1) => s1.pc as int == s.pc as int + 4,
        None => true,
    } by {
        match isa::step(s, i) {
            Some(s1) => {
                lemma_step_pc_plain(s, i, s1);
            },
            None => {},
        }
    }
}

/// Generic [`lemma_run_seq_steps`].
pub proof fn lemma_run_gen_steps(
    f: spec_fn(isa::State, isa::Instr) -> Option<isa::State>,
    pre: Seq<isa::Instr>,
    code: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    b: int,
    s: isa::State,
    s2: isa::State,
)
    requires
        pc_plain(f),
        no_jumps(code),
        s.pc as int == b + code_len(pre),
        s.pc as int + code_len(code) < isa::p2(64),
        run_gen(f, s, code) == Some(s2),
    ensures
        steps_g(f, pre + code + post, b, s, code.len()) == Some(s2),
        s2.pc as int == s.pc as int + code_len(code),
    decreases code.len(),
{
    super::memlemmas::lemma_p2_consts();
    if code.len() == 0 {
    } else {
        let whole = pre + code + post;
        let i = code[0];
        assert(!is_jump(i));
        let off: int = code_len(pre) as int;
        assert(whole =~= pre + (code + post));
        lemma_fetch_append_r(pre, code + post, off);
        assert(fetch(code + post, 0) == Some(i));
        assert(s.pc as int - b == off);
        assert(s.pc as int + 4 < isa::p2(64));
        match f(s, i) {
            Some(s1) => {
                assert(s1.pc as int == s.pc as int + 4);
                let pre1 = pre + seq![i];
                let rest = code.skip(1);
                assert(code_len(pre1) == code_len(pre) + 4);
                assert(pre1 + rest + post =~= whole);
                assert(no_jumps(rest)) by {
                    assert forall|j: int| 0 <= j < rest.len() implies !is_jump(
                        #[trigger] rest[j],
                    ) by {
                        assert(rest[j] == code[j + 1]);
                    }
                }
                assert(code_len(code) == 4 + code_len(rest));
                lemma_run_gen_steps(f, pre1, rest, post, b, s1, s2);
            },
            None => {},
        }
    }
}

/// **Jump-free code run by [`run_seq`] is run by [`steps`].** `whole` is
/// `pre + code + post` placed at `b`; the state is at the first byte of
/// `code`; the run of `code` by [`run_seq`] reaches `s2`.
pub proof fn lemma_run_seq_steps(
    pre: Seq<isa::Instr>,
    code: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    b: int,
    s: isa::State,
    s2: isa::State,
)
    requires
        no_jumps(code),
        s.pc as int == b + code_len(pre),
        s.pc as int + code_len(code) < isa::p2(64),
        run_seq(s, code) == Some(s2),
    ensures
        steps(pre + code + post, b, s, code.len()) == Some(s2),
        s2.pc as int == s.pc as int + code_len(code),
{
    let f = stepper();
    lemma_stepper_pc_plain();
    lemma_run_seq_is_gen(s, code);
    lemma_run_gen_steps(f, pre, code, post, b, s, s2);
    lemma_steps_is_gen(pre + code + post, b, s, code.len());
}

/// [`reaches`] in code followed by more.
pub proof fn lemma_reaches_post(
    c: Seq<isa::Instr>,
    post: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s2: isa::State,
)
    requires
        reaches(c, base, s, s2),
    ensures
        reaches(c + post, base, s, s2),
{
    assert(Seq::<isa::Instr>::empty() + c + post =~= c + post);
    assert(code_len(Seq::<isa::Instr>::empty()) == 0);
    lemma_reaches_embed(Seq::empty(), c, post, base, s, s2);
}

/// [`reaches`] in code preceded by more (the base moves back).
pub proof fn lemma_reaches_pre(
    pre: Seq<isa::Instr>,
    c: Seq<isa::Instr>,
    base: int,
    s: isa::State,
    s2: isa::State,
)
    requires
        reaches(c, base, s, s2),
    ensures
        reaches(pre + c, base - code_len(pre), s, s2),
{
    assert(pre + c + Seq::<isa::Instr>::empty() =~= pre + c);
    lemma_reaches_embed(pre, c, Seq::empty(), base, s, s2);
}

} // verus!
