//! An independent transcription of two string algorithms of the form
//! encodings (docs/VERIFICATION.md, "Trust without reviewers", item 2),
//! proven equal to [`super::spec`]'s. **Scope: only these two.** The
//! serializers, "picking an encoding" and the submission algorithm have no
//! independent transcription yet. As for [`crate::independent`], the file
//! was written beside `spec.rs`, so it is independent in formulation, not
//! in author.
//!
//! - HTML §4.10.22.6 step 1.1 and §4.10.22.8 step 1, "replace every
//!   occurrence of CR not followed by LF, and every occurrence of LF not
//!   preceded by CR, by CR LF", restated as two steps: Infra's "normalize
//!   newlines" (so every line break is one LF), then every LF becomes
//!   CR LF ([`ind_crlf_newlines`]).
//! - Infra "split a string on ASCII whitespace", with the standard's
//!   position variable: "skip ASCII whitespace; while position is not past
//!   the end, collect a sequence of code points that are not ASCII
//!   whitespace, append it to tokens, skip ASCII whitespace"
//!   ([`ind_split_on_whitespace`]).

#[cfg(verus_only)]
use super::spec::*;
#[cfg(verus_only)]
use crate::independent::*;
#[cfg(verus_only)]
use crate::spec::{is_ascii_whitespace, normalize_newlines};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// CR LF newlines, as normalize then expand

/// Every LF becomes CR LF; everything else stays.
pub open spec fn ind_lf_to_crlf(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 0x0A {
        seq![0x0Du32, 0x0Au32] + ind_lf_to_crlf(s.drop_first())
    } else {
        seq![s[0]] + ind_lf_to_crlf(s.drop_first())
    }
}

/// The replacement of §4.10.22.6 step 1.1: normalize newlines, then expand
/// each LF to CR LF.
pub open spec fn ind_crlf_newlines(s: Seq<u32>) -> Seq<u32> {
    ind_lf_to_crlf(ind_normalize_newlines(s))
}

/// `ind_lf_to_crlf` after one code point in front.
proof fn lemma_lf_to_crlf_cons(c: u32, t: Seq<u32>)
    ensures
        ind_lf_to_crlf(seq![c] + t) =~= (if c == 0x0A {
            seq![0x0Du32, 0x0Au32]
        } else {
            seq![c]
        }) + ind_lf_to_crlf(t),
{
    let s = seq![c] + t;
    assert(s.drop_first() =~= t);
    assert(s[0] == c);
}

/// Normalizing then expanding is the one-pass replacement.
proof fn lemma_crlf_via_normalize(s: Seq<u32>)
    ensures
        ind_lf_to_crlf(normalize_newlines(s)) =~= crlf_newlines(s),
    decreases s.len(),
{
    if s.len() > 0 {
        if s[0] == 0x0D {
            if s.len() > 1 && s[1] == 0x0A {
                lemma_crlf_via_normalize(s.skip(2));
            } else {
                lemma_crlf_via_normalize(s.drop_first());
            }
            lemma_lf_to_crlf_cons(0x0A, normalize_newlines(if s.len() > 1 && s[1] == 0x0A {
                s.skip(2)
            } else {
                s.drop_first()
            }));
        } else {
            lemma_crlf_via_normalize(s.drop_first());
            lemma_lf_to_crlf_cons(s[0], normalize_newlines(s.drop_first()));
        }
    }
}

/// `crlf_newlines` is the two steps of the standard.
pub proof fn lemma_crlf_newlines_equal(s: Seq<u32>)
    ensures
        crlf_newlines(s) =~= ind_crlf_newlines(s),
{
    lemma_normalize_newlines_equal(s);
    lemma_crlf_via_normalize(s);
}

// ---------------------------------------------------------------------
// Split a string on ASCII whitespace, with a position

/// The first position at or after `from` whose code point is ASCII
/// whitespace, or the end of `s`: where "collect a sequence of code points
/// that are not ASCII whitespace" stops.
pub open spec fn ind_run_end(s: Seq<u32>, from: int) -> int
    decreases s.len() - from,
    when 0 <= from
{
    if from >= s.len() || ind_white(s[from]) {
        from
    } else {
        ind_run_end(s, from + 1)
    }
}

/// Steps 3 and 4 of the standard from position `p`: skip whitespace; if
/// not past the end, collect a token and continue from where it ended.
/// `fuel` bounds the number of tokens (each takes a code point, so
/// `s.len()` is enough).
pub open spec fn ind_tokens(s: Seq<u32>, p: int, fuel: nat) -> Seq<Seq<u32>>
    decreases fuel,
{
    let p1 = ind_first_kept(s, p);
    if fuel == 0 || p1 >= s.len() {
        Seq::empty()
    } else {
        let q = ind_run_end(s, p1);
        seq![s.subrange(p1, q)] + ind_tokens(s, q, (fuel - 1) as nat)
    }
}

/// Infra "split a string on ASCII whitespace".
pub open spec fn ind_split_on_whitespace(s: Seq<u32>) -> Seq<Seq<u32>> {
    ind_tokens(s, 0, s.len())
}

/// `ind_run_end` stays within `s`, and moves forward over a code point
/// that is not whitespace.
proof fn lemma_run_end_bounds(s: Seq<u32>, from: int)
    requires
        0 <= from <= s.len(),
    ensures
        from <= ind_run_end(s, from) <= s.len(),
        from < s.len() && !ind_white(s[from]) ==> ind_run_end(s, from) > from,
        ind_run_end(s, from) < s.len() ==> ind_white(s[ind_run_end(s, from)]),
    decreases s.len() - from,
{
    if from < s.len() && !ind_white(s[from]) {
        lemma_run_end_bounds(s, from + 1);
    }
}

/// With no token being collected, skipping whitespace first changes
/// nothing.
proof fn lemma_split_skip(s: Seq<u32>, p: int)
    requires
        0 <= p <= s.len(),
    ensures
        split_ws_acc(s.skip(p), Seq::empty()) =~= split_ws_acc(s.skip(ind_first_kept(s, p)), Seq::empty()),
    decreases s.len() - p,
{
    if p < s.len() && ind_white(s[p]) {
        lemma_split_skip(s, p + 1);
        assert(s.skip(p).drop_first() =~= s.skip(p + 1));
        assert(is_ascii_whitespace(s.skip(p)[0]));
        assert(split_ws_acc(s.skip(p), Seq::empty()) =~= split_ws_acc(s.skip(p + 1), Seq::empty()));
    }
}

/// Collecting from `from` with `cur` already collected: one token (when it
/// is not empty) of `cur` and the run, then the rest from the run's end.
proof fn lemma_split_run(s: Seq<u32>, from: int, cur: Seq<u32>)
    requires
        0 <= from <= s.len(),
    ensures
        split_ws_acc(s.skip(from), cur) =~= (if cur.len() + (ind_run_end(s, from) - from) > 0 {
            seq![cur + s.subrange(from, ind_run_end(s, from))]
        } else {
            Seq::empty()
        }) + split_ws_acc(s.skip(ind_run_end(s, from)), Seq::empty()),
    decreases s.len() - from,
{
    lemma_run_end_bounds(s, from);
    let r = ind_run_end(s, from);
    if from < s.len() && !ind_white(s[from]) {
        lemma_split_run(s, from + 1, cur.push(s[from]));
        assert(s.skip(from).drop_first() =~= s.skip(from + 1));
        assert(!is_ascii_whitespace(s.skip(from)[0]));
        assert(split_ws_acc(s.skip(from), cur) =~= split_ws_acc(s.skip(from + 1), cur.push(s[from])));
        assert(ind_run_end(s, from + 1) == r);
        assert(cur.push(s[from]) + s.subrange(from + 1, r) =~= cur + s.subrange(from, r));
    } else if from >= s.len() {
        assert(s.skip(from).len() == 0);
        assert(s.subrange(from, from) =~= Seq::<u32>::empty());
        assert(cur + s.subrange(from, from) =~= cur);
    } else {
        assert(r == from);
        assert(s.subrange(from, from) =~= Seq::<u32>::empty());
        assert(cur + s.subrange(from, from) =~= cur);
        assert(s.skip(from).drop_first() =~= s.skip(from + 1));
        assert(is_ascii_whitespace(s.skip(from)[0]));
        assert(split_ws_acc(s.skip(from), Seq::empty()) =~= split_ws_acc(s.skip(from + 1), Seq::empty()));
    }
}

/// The tokens of the standard from `p` are `split_ws_acc`'s of the rest.
proof fn lemma_tokens_equal(s: Seq<u32>, p: int, fuel: nat)
    requires
        0 <= p <= s.len(),
        fuel >= s.len() - p,
    ensures
        ind_tokens(s, p, fuel) =~= split_ws_acc(s.skip(p), Seq::empty()),
    decreases fuel,
{
    lemma_first_kept_bounds(s, p);
    let p1 = ind_first_kept(s, p);
    lemma_split_skip(s, p);
    if p1 >= s.len() {
        assert(p1 == s.len());
        assert(s.skip(p1).len() == 0);
    } else {
        assert(fuel >= 1);
        lemma_run_end_bounds(s, p1);
        let q = ind_run_end(s, p1);
        assert(q > p1 && q > p);
        lemma_split_run(s, p1, Seq::empty());
        assert(Seq::<u32>::empty() + s.subrange(p1, q) =~= s.subrange(p1, q));
        lemma_tokens_equal(s, q, (fuel - 1) as nat);
        assert(ind_tokens(s, p, fuel) =~= seq![s.subrange(p1, q)] + ind_tokens(s, q, (fuel - 1) as nat));
    }
}

/// `split_ws` is the standard's loop.
pub proof fn lemma_split_ws_equal(s: Seq<u32>)
    ensures
        split_ws(s) =~= ind_split_on_whitespace(s),
{
    lemma_tokens_equal(s, 0, s.len());
    assert(s.skip(0) =~= s);
}

} // verus!
