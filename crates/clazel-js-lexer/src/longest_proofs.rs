//! Lemmas for the longest-match property of [`super::exec`] across input
//! element kinds.
//!
//! The kinds whose agreement with the spec is proven are those of
//! [`super::exec::kind_proven`]. [`lemma_first_cp`] says each of them can
//! only start with certain code points ([`start_ok`]); the dispatch of the
//! executable lexer on the first code point then shows no other proven kind
//! derives a longer range than the one it returns ([`pk_bounded`]).
//!
//! What is not proven is that no element of an *unproven* kind (identifier,
//! private identifier, regular expression literal, template, and Annex B's
//! HTML-like comments) is longer; [`unproven_bounded`] states exactly that,
//! and [`lemma_longest_from_bounds`] shows that with it the returned end is
//! [`super::spec::longest_len`].

#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::exec::kind_proven;
#[cfg(verus_only)]
use super::ident_proofs::*;
#[cfg(verus_only)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::template_proofs::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The one-code-point starts of the punctuators: every punctuator of
/// §12.8 starts with one of these code points (and each is itself a
/// punctuator).
pub open spec fn punct_start(c: u32) -> bool {
    c == 0x7B || c == 0x28 || c == 0x29 || c == 0x5B || c == 0x5D || c == 0x2E || c == 0x3B
        || c == 0x2C || c == 0x3C || c == 0x3E || c == 0x2B || c == 0x2D || c == 0x2A
        || c == 0x25 || c == 0x26 || c == 0x7C || c == 0x5E || c == 0x21 || c == 0x7E
        || c == 0x3F || c == 0x3A || c == 0x3D
}

/// The first code point (and for a numeric literal starting with `.`, the
/// one after it) that a derivation of kind `k` needs, for the kinds of
/// [`kind_proven`]. For the other kinds nothing is said.
pub open spec fn start_ok(k: ElementKind, s: Seq<u32>, i: int) -> bool {
    match k {
        ElementKind::WhiteSpace => s[i] == 0x0009 || s[i] == 0x000B || s[i] == 0x000C || s[i]
            == 0xFEFF || unicode_space_separator(s[i]),
        ElementKind::LineTerminator => is_line_terminator(s[i]),
        ElementKind::Comment => s[i] == 0x2F,
        ElementKind::HashbangComment => s[i] == 0x23,
        ElementKind::Punctuator => punct_start(s[i]),
        ElementKind::NumericLiteral => is_decimal_digit(s[i]) || (s[i] == 0x2E && at_decimal_digit(
            s,
            i + 1,
        )),
        ElementKind::StringLiteral => s[i] == 0x22 || s[i] == 0x27,
        ElementKind::DivPunctuator => s[i] == 0x2F,
        ElementKind::RightBracePunctuator => s[i] == 0x7D,
        ElementKind::IdentifierName => s[i] == 0x5C || is_identifier_start_char(s[i]),
        ElementKind::PrivateIdentifier => s[i] == 0x23,
        ElementKind::Template(tk) => match tk {
            TemplateKind::NoSubstitution | TemplateKind::Head => s[i] == 0x60,
            TemplateKind::Middle | TemplateKind::Tail => s[i] == 0x7D,
        },
        _ => true,
    }
}

/// A numeric literal starts with a decimal digit, or `.` and one.
pub proof fn lemma_numeric_start(s: Seq<u32>, i: int, j: int)
    requires
        numeric_literal(s, i, j),
    ensures
        0 <= i < s.len(),
        is_decimal_digit(s[i]) || (s[i] == 0x2E && at_decimal_digit(s, i + 1)),
{
    lemma_numeric_literal_equiv(s, i, j);
    assert(ind_numeric_literal(s, i, j));
    if ind_decimal_literal(s, i, j) {
        if exists|a: int, b: int| #[trigger] ind_dl_alt1(s, i, j, a, b) {
            let (a, b) = choose|a: int, b: int| #[trigger] ind_dl_alt1(s, i, j, a, b);
            assert(ind_decimal_integer(s, i, a));
        } else if exists|b: int| #[trigger] ind_dl_alt2(s, i, j, b) {
            let b = choose|b: int| #[trigger] ind_dl_alt2(s, i, j, b);
            assert(ind_sep_digits(10, s, i + 1, b));
        } else {
            let a = choose|a: int| #[trigger] ind_dl_alt3(s, i, j, a);
            assert(ind_decimal_integer(s, i, a));
        }
    }
}

/// No numeric literal starts at `pos`. (Opaque: the quantifier is revealed
/// only where its body is used, so that it does not burden other proofs.)
#[verifier::opaque]
pub open spec fn numeric_absent(s: Seq<u32>, pos: int) -> bool {
    forall|j: int| !numeric_literal(s, pos, j)
}

/// A position whose code point cannot start a numeric literal has none.
pub proof fn lemma_numeric_absent_from_class(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        !start_ok(ElementKind::NumericLiteral, s, i),
    ensures
        numeric_absent(s, i),
{
    reveal(numeric_absent);
    assert forall|j: int| !numeric_literal(s, i, j) by {
        if numeric_literal(s, i, j) {
            lemma_numeric_start(s, i, j);
        }
    }
}

/// A derivation of a proven kind starts with a code point of its class.
pub proof fn lemma_first_cp(
    goal: Goal,
    html: bool,
    k: ElementKind,
    s: Seq<u32>,
    i: int,
    j: int,
)
    requires
        kind_proven(k, html),
        element_matches(goal, html, k, s, i, j),
    ensures
        0 <= i < s.len(),
        start_ok(k, s, i),
{
    match k {
        ElementKind::WhiteSpace => {},
        ElementKind::LineTerminator => {},
        ElementKind::Comment => {
            lemma_multi_line_comment_equiv(s, i, j);
            lemma_single_line_comment_equiv(s, i, j);
        },
        ElementKind::HashbangComment => {
            lemma_hashbang_comment_equiv(s, i, j);
        },
        ElementKind::Punctuator => {
            lemma_optional_chaining_equiv(s, i, j);
            lemma_other_punctuator_equiv(s, i, j);
        },
        ElementKind::NumericLiteral => {
            lemma_numeric_start(s, i, j);
        },
        ElementKind::StringLiteral => {
            let v = choose|v: Seq<u16>| string_literal_sv(s, i, j, v);
        },
        ElementKind::DivPunctuator => {
            lemma_div_punctuator_equiv(s, i, j);
        },
        ElementKind::RightBracePunctuator => {
            lemma_right_brace_equiv(s, i, j);
        },
        ElementKind::IdentifierName => {
            lemma_ident_start(s, i, j);
        },
        ElementKind::PrivateIdentifier => {},
        ElementKind::Template(tk) => {
            let (tv, trv) = choose|tv: Tv, trv: Seq<u16>| template_part(s, i, j, tk, tv, trv);
            lemma_part_shape(s, i, j, tk, tv, trv);
        },
        _ => {},
    }
}

/// No derivation, from `pos`, of a kind of [`kind_proven`] other than
/// `HashbangComment` (which only [`super::exec`]'s start-of-text lexing can
/// derive) ends after `e`.
pub open spec fn pk_bounded(goal: Goal, html: bool, s: Seq<u32>, pos: int, e: int) -> bool {
    forall|k: ElementKind, j: int|
        pos < j <= s.len() && kind_proven(k, html) && k != ElementKind::HashbangComment
            && #[trigger] element_matches(goal, html, k, s, pos, j) ==> j <= e
}

/// No `HashbangComment` derivation from `pos` ends after `e`.
pub open spec fn hb_bounded(goal: Goal, html: bool, s: Seq<u32>, pos: int, e: int) -> bool {
    forall|j: int|
        pos < j <= s.len() && #[trigger] element_matches(
            goal,
            html,
            ElementKind::HashbangComment,
            s,
            pos,
            j,
        ) ==> j <= e
}

/// No derivation of a kind of [`kind_proven`] ends after `e`.
pub open spec fn proven_bounded(goal: Goal, html: bool, s: Seq<u32>, pos: int, e: int) -> bool {
    pk_bounded(goal, html, s, pos, e) && hb_bounded(goal, html, s, pos, e)
}

/// No derivation of a kind that is not [`kind_proven`] ends at or after
/// `e`. This is what is not proven: it is the part of the longest-match
/// property that concerns identifiers, private identifiers, regular
/// expression literals, templates and (in `html` mode) comments.
pub open spec fn unproven_bounded(goal: Goal, html: bool, s: Seq<u32>, pos: int, e: int) -> bool {
    forall|k: ElementKind, j: int|
        e <= j <= s.len() && !kind_proven(k, html) && #[trigger] element_matches(
            goal,
            html,
            k,
            s,
            pos,
            j,
        ) ==> false
}

/// If the kinds `k1` and `k2` are bounded by `e` and every other proven kind
/// (not `HashbangComment`) cannot start with the code point at `pos`, all of
/// them are bounded by `e`.
pub proof fn lemma_pk_only(
    goal: Goal,
    html: bool,
    s: Seq<u32>,
    pos: int,
    e: int,
    k1: ElementKind,
    k2: ElementKind,
)
    requires
        0 <= pos < s.len(),
        forall|k: ElementKind, j: int|
            pos < j <= s.len() && kind_proven(k, html) && k != ElementKind::HashbangComment && (k
                == k1 || k == k2) && #[trigger] element_matches(goal, html, k, s, pos, j) ==> j
                <= e,
        forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && !(k == k1 || k == k2)
                ==> !start_ok(k, s, pos),
    ensures
        pk_bounded(goal, html, s, pos, e),
        (k1 != ElementKind::NumericLiteral && k2 != ElementKind::NumericLiteral) ==> numeric_absent(
            s,
            pos,
        ),
{
    assert forall|k: ElementKind, j: int|
        pos < j <= s.len() && kind_proven(k, html) && k != ElementKind::HashbangComment
            && #[trigger] element_matches(goal, html, k, s, pos, j) implies j <= e by {
        if !(k == k1 || k == k2) {
            lemma_first_cp(goal, html, k, s, pos, j);
        }
    }
    if k1 != ElementKind::NumericLiteral && k2 != ElementKind::NumericLiteral {
        assert(kind_proven(ElementKind::NumericLiteral, html));
        assert(!start_ok(ElementKind::NumericLiteral, s, pos));
        lemma_numeric_absent_from_class(s, pos);
    }
}

/// Three proven kinds `k1`, `k2` and `k3` bounded by `e` (the rest, other
/// than `HashbangComment`, cannot start with the code point at `pos`).
pub proof fn lemma_pk_three(
    goal: Goal,
    html: bool,
    s: Seq<u32>,
    pos: int,
    e: int,
    k1: ElementKind,
    k2: ElementKind,
    k3: ElementKind,
)
    requires
        0 <= pos < s.len(),
        forall|k: ElementKind, j: int|
            pos < j <= s.len() && kind_proven(k, html) && k != ElementKind::HashbangComment && (k
                == k1 || k == k2 || k == k3) && #[trigger] element_matches(goal, html, k, s, pos, j)
                ==> j <= e,
        forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && !(k == k1 || k == k2 || k
                == k3) ==> !start_ok(k, s, pos),
    ensures
        pk_bounded(goal, html, s, pos, e),
        (k1 != ElementKind::NumericLiteral && k2 != ElementKind::NumericLiteral && k3
            != ElementKind::NumericLiteral) ==> numeric_absent(s, pos),
{
    assert forall|k: ElementKind, j: int|
        pos < j <= s.len() && kind_proven(k, html) && k != ElementKind::HashbangComment
            && #[trigger] element_matches(goal, html, k, s, pos, j) implies j <= e by {
        if !(k == k1 || k == k2 || k == k3) {
            lemma_first_cp(goal, html, k, s, pos, j);
        }
    }
    if k1 != ElementKind::NumericLiteral && k2 != ElementKind::NumericLiteral && k3
        != ElementKind::NumericLiteral {
        assert(kind_proven(ElementKind::NumericLiteral, html));
        assert(!start_ok(ElementKind::NumericLiteral, s, pos));
        lemma_numeric_absent_from_class(s, pos);
    }
}

/// A punctuator that starts with `.` and a decimal digit is the `.`.
pub proof fn lemma_punct_dot_digit(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        s[i] == 0x2E,
        at_decimal_digit(s, i + 1),
        punctuator(s, i, j),
    ensures
        j == i + 1,
{
    lemma_optional_chaining_equiv(s, i, j);
    lemma_other_punctuator_equiv(s, i, j);
}

/// A punctuator that starts with `<!` is the `<`.
pub proof fn lemma_punct_lt_bang(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        s[i] == 0x3C,
        i + 1 < s.len(),
        s[i + 1] == 0x21,
        punctuator(s, i, j),
    ensures
        j == i + 1,
{
    lemma_optional_chaining_equiv(s, i, j);
    lemma_other_punctuator_equiv(s, i, j);
}

/// A numeric literal is derived at a code point that starts one: the digit,
/// or `.` and the digit after it.
pub proof fn lemma_numeric_derivable(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        is_decimal_digit(s[i]) || (s[i] == 0x2E && at_decimal_digit(s, i + 1)),
    ensures
        exists|j: int| i < j <= s.len() && numeric_literal(s, i, j),
{
    if is_decimal_digit(s[i]) {
        assert(ind_sep_digits(10, s, i, i + 1));
        assert(ind_decimal_integer(s, i, i + 1));
        assert(ind_dl_alt3(s, i, i + 1, i + 1));
        assert(ind_decimal_literal(s, i, i + 1));
        lemma_numeric_literal_equiv(s, i, i + 1);
        assert(numeric_literal(s, i, i + 1));
    } else {
        assert(ind_sep_digits(10, s, i + 1, i + 2));
        assert(ind_dl_alt2(s, i, i + 2, i + 2));
        assert(ind_decimal_literal(s, i, i + 2));
        lemma_numeric_literal_equiv(s, i, i + 2);
        assert(numeric_literal(s, i, i + 2));
    }
}

/// One proven kind `k1` bounded by `e` (the rest, other than
/// `HashbangComment`, cannot start with the code point at `pos`).
pub proof fn lemma_pk_one(goal: Goal, html: bool, s: Seq<u32>, pos: int, e: int, k1: ElementKind)
    requires
        0 <= pos < s.len(),
        forall|j: int|
            pos < j <= s.len() && #[trigger] element_matches(goal, html, k1, s, pos, j) ==> j <= e,
        forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k != k1
                ==> !start_ok(k, s, pos),
    ensures
        pk_bounded(goal, html, s, pos, e),
        k1 != ElementKind::NumericLiteral ==> numeric_absent(s, pos),
{
    lemma_pk_only(goal, html, s, pos, e, k1, k1);
}

/// No proven kind (other than `HashbangComment`) can start with the code
/// point at `pos`.
pub proof fn lemma_pk_none(goal: Goal, html: bool, s: Seq<u32>, pos: int, e: int)
    requires
        0 <= pos < s.len(),
        forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment ==> !start_ok(k, s, pos),
    ensures
        pk_bounded(goal, html, s, pos, e),
        numeric_absent(s, pos),
{
    lemma_pk_only(
        goal,
        html,
        s,
        pos,
        e,
        ElementKind::RegularExpressionLiteral,
        ElementKind::RegularExpressionLiteral,
    );
}

/// A monotone bound.
pub proof fn lemma_pk_mono(goal: Goal, html: bool, s: Seq<u32>, pos: int, e1: int, e2: int)
    requires
        pk_bounded(goal, html, s, pos, e1),
        e1 <= e2,
    ensures
        pk_bounded(goal, html, s, pos, e2),
{
}

/// A monotone bound.
pub proof fn lemma_hb_mono(goal: Goal, html: bool, s: Seq<u32>, pos: int, e1: int, e2: int)
    requires
        hb_bounded(goal, html, s, pos, e1),
        e1 <= e2,
    ensures
        hb_bounded(goal, html, s, pos, e2),
{
}

/// With both bounds, no range longer than `e` is derived by any alternative
/// of the goal.
pub proof fn lemma_no_longer(goal: Goal, html: bool, s: Seq<u32>, i: int, e: int)
    requires
        0 <= i <= e <= s.len(),
        proven_bounded(goal, html, s, i, e),
        unproven_bounded(goal, html, s, i, e + 1),
    ensures
        forall|j: int| e < j <= s.len() ==> !any_element_matches(goal, html, s, i, j),
{
    assert forall|j: int| e < j <= s.len() implies !any_element_matches(goal, html, s, i, j) by {
        if any_element_matches(goal, html, s, i, j) {
            assert(element_matches(goal, html, ElementKind::WhiteSpace, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::LineTerminator, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::Comment, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::HashbangComment, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::IdentifierName, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::PrivateIdentifier, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::Punctuator, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::NumericLiteral, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::StringLiteral, s, i, j) ==> j <= e);
            assert(element_matches(
                goal,
                html,
                ElementKind::Template(TemplateKind::NoSubstitution),
                s,
                i,
                j,
            ) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::Template(TemplateKind::Head), s, i, j)
                ==> j <= e);
            assert(element_matches(goal, html, ElementKind::Template(TemplateKind::Middle), s, i, j)
                ==> j <= e);
            assert(element_matches(goal, html, ElementKind::Template(TemplateKind::Tail), s, i, j)
                ==> j <= e);
            assert(element_matches(goal, html, ElementKind::DivPunctuator, s, i, j) ==> j <= e);
            assert(element_matches(goal, html, ElementKind::RightBracePunctuator, s, i, j) ==> j
                <= e);
            assert(element_matches(goal, html, ElementKind::RegularExpressionLiteral, s, i, j)
                ==> j <= e);
        }
    }
}

/// With both bounds, the end `e` of an element is the longest element's.
pub proof fn lemma_longest_from_bounds(goal: Goal, html: bool, s: Seq<u32>, i: int, e: int)
    requires
        0 <= i < e <= s.len(),
        any_element_matches(goal, html, s, i, e),
        proven_bounded(goal, html, s, i, e),
        unproven_bounded(goal, html, s, i, e + 1),
    ensures
        longest_len(goal, html, s, i) == e - i,
{
    super::lemmas::lemma_longest_len(goal, html, s, i);
    lemma_no_longer(goal, html, s, i, e);
    let n = longest_len(goal, html, s, i);
    assert(n >= e - i) by {
        assert(i + (e - i) == e);
    }
    assert(n <= e - i) by {
        if n > e - i {
            assert(any_element_matches(goal, html, s, i, i + n));
        }
    }
}

/// With both bounds at `i`, no element starts at `i`.
pub proof fn lemma_longest_zero(goal: Goal, html: bool, s: Seq<u32>, i: int)
    requires
        0 <= i <= s.len(),
        proven_bounded(goal, html, s, i, i),
        unproven_bounded(goal, html, s, i, i + 1),
    ensures
        longest_len(goal, html, s, i) == 0,
{
    super::lemmas::lemma_longest_len(goal, html, s, i);
    lemma_no_longer(goal, html, s, i, i);
    let n = longest_len(goal, html, s, i);
    if n > 0 {
        assert(i + n <= s.len());
        assert(any_element_matches(goal, html, s, i, i + n));
    }
}

} // verus!
