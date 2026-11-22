//! Lemmas for `exec::next_token`'s link to [`super::spec::skip_trivia`].
//!
//! `next_token` repeats `next_input_element` over trivia, and the contract
//! says the trivia it skipped are [`skip_trivia`]'s: [`trivia_len`] is the
//! length of the longest element if it is of a trivia kind, else 0. That the
//! two agree needs one fact beyond the longest-match contract: an element
//! that is not trivia is not derived over the same range by a trivia kind
//! too ([`lemma_trivia_disjoint`], by the first code points of the kinds and
//! the second code point of the few that share one).
//!
//! Nothing here changes [`super::spec`]; these are facts about it.

#[cfg(verus_only)]
use super::equivalence::{
    lemma_div_punctuator_equiv, lemma_hashbang_comment_equiv, lemma_multi_line_comment_equiv,
    lemma_optional_chaining_equiv, lemma_other_punctuator_equiv, lemma_single_line_comment_equiv,
};
#[cfg(verus_only)]
use super::exec::kind_proven;
#[cfg(verus_only)]
use super::html_proofs::{lemma_html_close_shape, lemma_html_comment_start};
#[cfg(verus_only)]
use super::ident_proofs::{
    lemma_ident_absent_from_class, lemma_ident_start, lemma_private_absent_from_next,
    lemma_ws_lt_not_id_start, private_absent,
};
#[cfg(verus_only)]
use super::independent::*;
#[cfg(verus_only)]
use super::longest_proofs::{lemma_first_cp, lemma_punct_lt_bang, start_ok};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A regular expression literal's body does not start with `*` or `/`.
pub proof fn lemma_regexp_second(s: Seq<u32>, i: int, j: int, b: int)
    requires
        regexp_literal(s, i, j, b),
    ensures
        i + 1 < s.len(),
        s[i + 1] != 0x2F,
        s[i + 1] != 0x2A,
{
    let k = choose|k: int| i + 1 < k <= b && regexp_first_char(s, i + 1, k) && regexp_chars(s, k, b);
}

/// A punctuator that starts with `-` is at most two code points.
pub proof fn lemma_punct_dash_short(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        s[i] == 0x2D,
        punctuator(s, i, j),
    ensures
        j <= i + 2,
{
    lemma_optional_chaining_equiv(s, i, j);
    lemma_other_punctuator_equiv(s, i, j);
}

/// What a non-trivia kind that is derived over `s[i..j)` says of the code
/// points that start it, where a trivia kind could also start.
pub proof fn lemma_nontrivia_start(goal: Goal, html: bool, kn: ElementKind, s: Seq<u32>, i: int, j: int)
    requires
        0 <= i < j <= s.len(),
        !is_trivia(kn),
        element_matches(goal, html, kn, s, i, j),
    ensures
        start_ok(kn, s, i),
        kn == ElementKind::IdentifierName ==> !(is_line_terminator(s[i]) || s[i] == 0x0009
            || s[i] == 0x000B || s[i] == 0x000C || s[i] == 0xFEFF || unicode_space_separator(
            s[i],
        )),
        kn == ElementKind::DivPunctuator ==> (j == i + 1 || (j == i + 2 && s[i + 1] == 0x3D)),
        kn == ElementKind::RegularExpressionLiteral ==> (i + 1 < s.len() && s[i + 1] != 0x2F
            && s[i + 1] != 0x2A),
        kn == ElementKind::Punctuator && s[i] == 0x2D ==> j <= i + 2,
        kn == ElementKind::Punctuator && s[i] == 0x3C && i + 1 < s.len() && s[i + 1] == 0x21
            ==> j == i + 1,
        kn == ElementKind::PrivateIdentifier ==> (i + 1 < s.len() && !(s[i + 1] == 0x21)),
{
    assert(kind_proven(kn, html));
    lemma_first_cp(goal, html, kn, s, i, j);
    if kn == ElementKind::IdentifierName {
        if is_line_terminator(s[i]) || s[i] == 0x0009 || s[i] == 0x000B || s[i] == 0x000C || s[i]
            == 0xFEFF || unicode_space_separator(s[i]) {
            lemma_ws_lt_not_id_start(s[i]);
        }
    }
    if kn == ElementKind::DivPunctuator {
        lemma_div_punctuator_equiv(s, i, j);
    }
    if kn == ElementKind::RegularExpressionLiteral {
        let b = choose|b: int| regexp_literal(s, i, j, b);
        lemma_regexp_second(s, i, j, b);
    }
    if kn == ElementKind::Punctuator && s[i] == 0x2D {
        lemma_punct_dash_short(s, i, j);
    }
    if kn == ElementKind::Punctuator && s[i] == 0x3C && i + 1 < s.len() && s[i + 1] == 0x21 {
        lemma_punct_lt_bang(s, i, j);
    }
    if kn == ElementKind::PrivateIdentifier {
        assert(identifier_name(s, i + 1, j));
        lemma_ident_start(s, i + 1, j);
    }
}

/// A trivia kind and a kind that is not trivia are not derived over the
/// same range.
pub proof fn lemma_trivia_disjoint(
    goal: Goal,
    html: bool,
    s: Seq<u32>,
    i: int,
    j: int,
    kn: ElementKind,
    kt: ElementKind,
)
    requires
        0 <= i < j <= s.len(),
        !is_trivia(kn),
        is_trivia(kt),
        element_matches(goal, html, kn, s, i, j),
        element_matches(goal, html, kt, s, i, j),
    ensures
        false,
{
    lemma_nontrivia_start(goal, html, kn, s, i, j);
    match kt {
        ElementKind::HashbangComment => {
            lemma_hashbang_comment_equiv(s, i, j);
            if kn == ElementKind::PrivateIdentifier {
                lemma_ident_absent_from_class(s, i + 1);
                lemma_private_absent_from_next(s, i);
                reveal(private_absent);
                assert(identifier_name(s, i + 1, j));
            }
        },
        ElementKind::Comment => {
            if comment(s, i, j, true) && html {
                lemma_html_comment_start(s, i, j);
            }
            if comment(s, i, j, false) {
                lemma_multi_line_comment_equiv(s, i, j);
                lemma_single_line_comment_equiv(s, i, j);
            }
            if html && goal == Goal::InputElementHashbangOrRegExp && i == 0 && html_close_comment(
                s,
                i,
                j,
            ) {
                lemma_html_close_shape(s, i, j);
            }
        },
        _ => {},
    }
}

/// A trivia kind that is derived over a range of the longest length makes
/// [`trivia_len`] that length.
pub proof fn lemma_trivia_len_trivia(
    goal: Goal,
    html: bool,
    s: Seq<u32>,
    i: int,
    e: int,
    kt: ElementKind,
)
    requires
        0 <= i < e <= s.len(),
        longest_len(goal, html, s, i) == e - i,
        is_trivia(kt),
        element_matches(goal, html, kt, s, i, e),
    ensures
        trivia_len(goal, html, s, i) == e - i,
{
}

/// A longest element that is not trivia makes [`trivia_len`] 0.
pub proof fn lemma_trivia_len_nontrivia(
    goal: Goal,
    html: bool,
    s: Seq<u32>,
    i: int,
    e: int,
    kn: ElementKind,
)
    requires
        0 <= i < e <= s.len(),
        longest_len(goal, html, s, i) == e - i,
        !is_trivia(kn),
        element_matches(goal, html, kn, s, i, e),
    ensures
        trivia_len(goal, html, s, i) == 0,
{
    if element_matches(goal, html, ElementKind::WhiteSpace, s, i, e) {
        lemma_trivia_disjoint(goal, html, s, i, e, kn, ElementKind::WhiteSpace);
    }
    if element_matches(goal, html, ElementKind::LineTerminator, s, i, e) {
        lemma_trivia_disjoint(goal, html, s, i, e, kn, ElementKind::LineTerminator);
    }
    if element_matches(goal, html, ElementKind::Comment, s, i, e) {
        lemma_trivia_disjoint(goal, html, s, i, e, kn, ElementKind::Comment);
    }
    if element_matches(goal, html, ElementKind::HashbangComment, s, i, e) {
        lemma_trivia_disjoint(goal, html, s, i, e, kn, ElementKind::HashbangComment);
    }
}

/// Where [`lex_error`] finds an error, [`trivia_len`] is 0: no longest element
/// (so no trivia) or the one that has the error is not trivia.
pub proof fn lemma_trivia_len_error(goal: Goal, html: bool, s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        lex_error(goal, html, s, i) is Some,
    ensures
        trivia_len(goal, html, s, i) == 0,
{
    super::lemmas::lemma_longest_len(goal, html, s, i);
    let n = longest_len(goal, html, s, i);
    if n > 0 {
        if element_matches(goal, html, ElementKind::NumericLiteral, s, i, i + n) {
            lemma_trivia_len_nontrivia(goal, html, s, i, i + n, ElementKind::NumericLiteral);
        } else if element_matches(goal, html, ElementKind::IdentifierName, s, i, i + n) {
            lemma_trivia_len_nontrivia(goal, html, s, i, i + n, ElementKind::IdentifierName);
        } else {
            assert(element_matches(goal, html, ElementKind::PrivateIdentifier, s, i, i + n));
            lemma_trivia_len_nontrivia(goal, html, s, i, i + n, ElementKind::PrivateIdentifier);
        }
    }
}

} // verus!
