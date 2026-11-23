//! Facts proven about the spec: evidence that the transcription is
//! well-behaved, not part of what the implementation must meet.
//!
//! - The longest-element search returns what it claims to, and the trivia
//!   skip stays inside the source text: together with the contracts, these
//!   are the span-coverage property of phase-7.md 7.2 (a lexical step
//!   starts where the last one ended, goes forward, and does not leave the
//!   source text).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`longest_len_upto`] is between 0 and `m`; when it is positive some
/// alternative derives that range, and no longer range up to `m` is derived.
pub proof fn lemma_longest_len_upto(goal: Goal, html: bool, s: Src, i: int, m: int)
    requires
        0 <= i <= s.len(),
    ensures
        0 <= longest_len_upto(goal, html, s, i, m) <= (if m > 0 {
            m
        } else {
            0
        }),
        longest_len_upto(goal, html, s, i, m) > 0 ==> {
            &&& i + longest_len_upto(goal, html, s, i, m) <= s.len()
            &&& any_element_matches(
                goal,
                html,
                s,
                i,
                i + longest_len_upto(goal, html, s, i, m),
            )
        },
        forall|n: int|
            longest_len_upto(goal, html, s, i, m) < n <= m && i + n <= s.len() ==> !(
            #[trigger] any_element_matches(goal, html, s, i, i + n)),
    decreases m,
{
    if m > 0 && !(i + m <= s.len() && any_element_matches(goal, html, s, i, i + m)) {
        lemma_longest_len_upto(goal, html, s, i, m - 1);
    }
}

/// [`longest_len`] is the length of the longest input element: an element
/// of that length exists if it is positive, it fits in the source text, and
/// no longer one exists.
pub proof fn lemma_longest_len(goal: Goal, html: bool, s: Src, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        0 <= longest_len(goal, html, s, i) <= s.len() - i,
        longest_len(goal, html, s, i) > 0 ==> any_element_matches(
            goal,
            html,
            s,
            i,
            i + longest_len(goal, html, s, i),
        ),
        forall|n: int|
            longest_len(goal, html, s, i) < n <= s.len() - i ==> !(#[trigger] any_element_matches(
                goal,
                html,
                s,
                i,
                i + n,
            )),
{
    lemma_longest_len_upto(goal, html, s, i, s.len() - i);
}

/// An element of any kind that derives `s[i..j)` makes `s[i..j)` derived by
/// some alternative of the goal ([`any_element_matches`]).
pub proof fn lemma_kind_implies_any(goal: Goal, html: bool, kind: ElementKind, s: Src, i: int, j: int)
    requires
        element_matches(goal, html, kind, s, i, j),
    ensures
        any_element_matches(goal, html, s, i, j),
{
    match kind {
        ElementKind::Template(k) => {
            match k {
                TemplateKind::NoSubstitution => {},
                TemplateKind::Head => {},
                TemplateKind::Middle => {},
                TemplateKind::Tail => {},
            }
        },
        _ => {},
    }
}

/// [`skip_trivia`] goes forward and stays inside the source text.
pub proof fn lemma_skip_trivia_bounds(goal: Goal, html: bool, s: Src, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= skip_trivia(goal, html, s, i).0 <= s.len(),
    decreases s.len() - i,
{
    let n = trivia_len(goal, html, s, i);
    if 0 < n && i + n <= s.len() {
        lemma_skip_trivia_bounds(goal, html, s, i + n);
    }
}

/// [`contains_line_terminator`] of a range is that of its two halves.
pub proof fn lemma_contains_lt_split(s: Src, a: int, b: int, c: int)
    requires
        a <= b <= c,
    ensures
        contains_line_terminator(s, a, c) <==> (contains_line_terminator(s, a, b)
            || contains_line_terminator(s, b, c)),
{
    if contains_line_terminator(s, a, c) {
        let k = choose|k: int| a <= k < c && is_line_terminator(#[trigger] s[k]);
        if k < b {
            assert(contains_line_terminator(s, a, b));
        } else {
            assert(contains_line_terminator(s, b, c));
        }
    }
    if contains_line_terminator(s, a, b) {
        let k = choose|k: int| a <= k < b && is_line_terminator(#[trigger] s[k]);
        assert(a <= k < c);
    }
    if contains_line_terminator(s, b, c) {
        let k = choose|k: int| b <= k < c && is_line_terminator(#[trigger] s[k]);
        assert(a <= k < c);
    }
}

/// The line-terminator flag of [`skip_trivia`] is whether a `LineTerminator`
/// code point is in the range it skips: the trivia elements tile that range,
/// and the flag is the union of theirs. (So `newline_before` is a property of
/// where the trivia end, [`skip_trivia`]'s first component, and nothing else.)
pub proof fn lemma_skip_trivia_flag(goal: Goal, html: bool, s: Src, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        skip_trivia(goal, html, s, i).1 == contains_line_terminator(
            s,
            i,
            skip_trivia(goal, html, s, i).0,
        ),
    decreases s.len() - i,
{
    let n = trivia_len(goal, html, s, i);
    if 0 < n && i + n <= s.len() {
        lemma_skip_trivia_flag(goal, html, s, i + n);
        lemma_skip_trivia_bounds(goal, html, s, i + n);
        let end = skip_trivia(goal, html, s, i + n).0;
        lemma_contains_lt_split(s, i, i + n, end);
    } else {
        assert(!contains_line_terminator(s, i, i));
    }
}

/// Introduction rules for [`string_characters_sv`], for the single-character
/// and the character-then-characters alternatives.
pub proof fn lemma_string_characters_one(s: Src, i: int, j: int, quote: u32, v: Seq<u16>)
    requires
        nonempty(s, i, j),
        string_character_sv(s, i, j, quote, v),
    ensures
        string_characters_sv(s, i, j, quote, v),
{
}

/// See [`lemma_string_characters_one`].
pub proof fn lemma_string_characters_cons(
    s: Src,
    i: int,
    k: int,
    j: int,
    quote: u32,
    v1: Seq<u16>,
    v2: Seq<u16>,
)
    requires
        nonempty(s, i, j),
        i < k < j,
        string_character_sv(s, i, k, quote, v1),
        string_characters_sv(s, k, j, quote, v2),
    ensures
        string_characters_sv(s, i, j, quote, v1 + v2),
{
}

/// Introduction rules for [`template_characters`].
pub proof fn lemma_template_characters_one(s: Src, i: int, j: int, tv: Tv, trv: Seq<u16>)
    requires
        nonempty(s, i, j),
        template_character(s, i, j, tv, trv),
    ensures
        template_characters(s, i, j, tv, trv),
{
}

/// A step that finds no error and is not at the end of the source text
/// consumes a non-empty range inside the source text: the element starts at
/// `i` and ends after it (the span-coverage property of one step).
pub proof fn lemma_step_progress(goal: Goal, html: bool, s: Src, i: int)
    requires
        0 <= i < s.len(),
        lex_error(goal, html, s, i) is None,
    ensures
        0 < longest_len(goal, html, s, i) <= s.len() - i,
        any_element_matches(goal, html, s, i, i + longest_len(goal, html, s, i)),
{
    lemma_longest_len(goal, html, s, i);
}

} // verus!
