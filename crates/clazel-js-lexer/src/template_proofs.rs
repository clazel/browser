//! Lemmas about [`super::spec`]'s template relations: a `TemplateCharacter`
//! has one length, one TV and one TRV (`lemma_tchar_det`), and none starts
//! at the code points that close a template component (`` ` `` and `${`,
//! `lemma_delim_no_char`).
//!
//! These are the consumption half of what the executable lexer's template
//! scanner needs. The production half (that the scanner's range *is* derived
//! by `template_characters`, and its TV and TRV are the standard's) is open:
//! `template_characters` of the spec is a recursive relation whose
//! existential has the automatically chosen trigger
//! `template_character(s, i, k, ..) && template_characters(s, k, j, ..)`, and
//! Verus unfolds a recursive spec function to a different fuel than the one
//! its own call sites have, so the call never matches that trigger: a
//! `template_characters` of two or more characters cannot be derived from
//! its parts (the one-character case, `lemma_template_characters_one`,
//! needs no existential). Giving the existential a trigger on its other
//! terms, as `string_characters_sv` has by `#![auto]`, would let the proof
//! go through; `spec.rs` is not changed to make a proof go through
//! (CLAUDE.md), so this is left for a maintainer to decide.

#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::string_proofs::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// One TemplateCharacter has one length and one value.
// ---------------------------------------------------------------------

/// A run of hex digits `s[a..j)` that no hex digit follows ends where
/// [`ind_hex_run_end`] says.
pub proof fn lemma_hex_run_unique(s: Seq<u32>, a: int, j: int)
    requires
        0 <= a < j <= s.len(),
        forall|t: int| a <= t < j ==> is_hex_digit(#[trigger] s[t]),
        !at_hex_digit(s, j),
    ensures
        j == ind_hex_run_end(s, a),
{
    lemma_hex_run_end(s, a);
    let m = ind_hex_run_end(s, a);
    if m < j {
        assert(is_hex_digit(s[m]));
        lemma_digit_class_equiv(16, s[m]);
        assert(ind_hex(s[m]));
    }
    if m > j {
        assert(ind_hex(s[j]));
        lemma_digit_class_equiv(16, s[j]);
        assert(at_hex_digit(s, j));
    }
}

/// The shape of a `NotEscapeSequence` (§12.9.6), the range after the
/// backslash: which code point starts it, and where it ends.
pub proof fn lemma_ne_shape(s: Seq<u32>, i: int, m: int)
    requires
        not_escape_sequence(s, i, m),
    ensures
        0 <= i < s.len(),
        s[i] == 0x30 || is_non_zero_digit(s[i]) || s[i] == 0x78 || s[i] == 0x75,
        s[i] == 0x30 ==> m == i + 2 && is_decimal_digit(s[i + 1]),
        is_non_zero_digit(s[i]) ==> m == i + 1,
        s[i] == 0x78 ==> m == ind_hex_run_end(s, i + 1) && m <= i + 2,
        (s[i] == 0x75 && !at(s, i + 1, '{')) ==> m == ind_hex_run_end(s, i + 1) && m <= i + 4,
        (s[i] == 0x75 && at(s, i + 1, '{')) ==> m == ind_hex_run_end(s, i + 2) && m >= i + 2 && (m
            > i + 2 ==> (forall|t: int| i + 2 <= t < m ==> is_hex_digit(#[trigger] s[t])) && (
        hex_digits_mv(s, i + 2, m) > 0x10FFFF || !at(s, m, '}'))),
{
    reveal_with_fuel(ind_hex_run_end, 6);
    if i + 2 < m && s[i] == 0x75 && s[i + 1] == 0x7B {
        // Alternatives 10 and 11: the hex digits from i + 2 to m.
        if not_code_point(s, i + 2, m) {
            lemma_plain_digits_equiv(16, s, i + 2, m);
            assert(ind_plain_digits(16, s, i + 2, m));
            assert forall|t: int| i + 2 <= t < m implies is_hex_digit(#[trigger] s[t]) by {
                lemma_digit_class_equiv(16, s[t]);
            }
            lemma_hex_run_unique(s, i + 2, m);
        } else {
            lemma_plain_digits_equiv(16, s, i + 2, m);
            assert(ind_plain_digits(16, s, i + 2, m));
            assert forall|t: int| i + 2 <= t < m implies is_hex_digit(#[trigger] s[t]) by {
                lemma_digit_class_equiv(16, s[t]);
            }
            lemma_hex_run_unique(s, i + 2, m);
        }
    }
}

/// A `NotEscapeSequence` has one length.
pub proof fn lemma_ne_det(s: Seq<u32>, i: int, m1: int, m2: int)
    requires
        not_escape_sequence(s, i, m1),
        not_escape_sequence(s, i, m2),
    ensures
        m1 == m2,
{
    lemma_ne_shape(s, i, m1);
    lemma_ne_shape(s, i, m2);
}

/// No code point is both a `TemplateEscapeSequence` and a
/// `NotEscapeSequence`.
pub proof fn lemma_te_ne_excl(s: Seq<u32>, i: int, m1: int, m2: int, v: Seq<u16>)
    requires
        template_escape_sequence_sv(s, i, m1, v),
        not_escape_sequence(s, i, m2),
    ensures
        false,
{
    lemma_ne_shape(s, i, m2);
    lemma_unicode_escape_equiv(s, i, m1);
    reveal_with_fuel(ind_hex_run_end, 6);
    lemma_is_lit(s, i, i + 2, seq!['u', '{']);
    if unicode_escape_sequence(s, i, m1) && s[i] == 0x75 {
        if s[i + 1] == 0x7B {
            // `u{` CodePoint `}`: the hex run from i + 2 ends at the brace.
            let r = ind_hex_run_end(s, i + 2);
            assert(ind_escape_end(s, i) == m1);
            assert(r > i + 2 && ind_is(s, r, 0x7D) && ind_hex_run_value(s, i + 2, r) <= 0x10FFFF);
            assert(m2 == r);
            lemma_ne_shape(s, i, m2);
            assert(forall|t: int| i + 2 <= t < r ==> is_hex_digit(#[trigger] s[t]));
            lemma_hex_value_equiv(s, i + 2, r);
            assert(at(s, r, '}'));
        } else {
            // `u` Hex4Digits.
            assert(ind_escape_end(s, i) == i + 5);
            assert(ind_hex_run_end(s, i + 1) >= i + 5);
            assert(m2 == ind_hex_run_end(s, i + 1));
        }
    }
}

/// A `TemplateEscapeSequence` has one length (and one value).
pub proof fn lemma_te_det(s: Seq<u32>, i: int, m1: int, m2: int, v1: Seq<u16>, v2: Seq<u16>)
    requires
        template_escape_sequence_sv(s, i, m1, v1),
        template_escape_sequence_sv(s, i, m2, v2),
    ensures
        m1 == m2,
        v1 =~= v2,
{
    lemma_escape_det(s, i, m1, m2, v1, v2);
}

/// A `TemplateCharacter` has one length, one TV and one TRV.
pub proof fn lemma_tchar_det(
    s: Seq<u32>,
    i: int,
    m1: int,
    m2: int,
    tv1: Tv,
    tv2: Tv,
    trv1: Seq<u16>,
    trv2: Seq<u16>,
)
    requires
        template_character(s, i, m1, tv1, trv1),
        template_character(s, i, m2, tv2, trv2),
    ensures
        m1 == m2,
        tv1 =~= tv2,
        trv1 =~= trv2,
{
    if s[i] == 0x5C {
        // `\ TemplateEscapeSequence`, `\ NotEscapeSequence` or
        // LineContinuation (the other alternatives do not start with `\`).
        let e1 = exists|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m1, v);
        let e2 = exists|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m2, v);
        if e1 && e2 {
            let v1 = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m1, v);
            let v2 = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m2, v);
            lemma_te_det(s, i + 1, m1, m2, v1, v2);
        } else if e1 {
            if not_escape_sequence(s, i + 1, m2) {
                let v1 = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m1, v);
                lemma_te_ne_excl(s, i + 1, m1, m2, v1);
            } else {
                // LineContinuation: the code point after `\` is a
                // LineTerminator, which no escape sequence starts with.
                let v1 = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m1, v);
                lemma_escape_not_lt(s, i + 1, m1, v1);
                assert(escape_sequence_sv(s, i + 1, m1, v1));
            }
        } else if e2 {
            if not_escape_sequence(s, i + 1, m1) {
                let v2 = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m2, v);
                lemma_te_ne_excl(s, i + 1, m2, m1, v2);
            } else {
                let v2 = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, m2, v);
                lemma_escape_not_lt(s, i + 1, m2, v2);
                assert(escape_sequence_sv(s, i + 1, m2, v2));
            }
        } else {
            let n1 = not_escape_sequence(s, i + 1, m1);
            let n2 = not_escape_sequence(s, i + 1, m2);
            if n1 && n2 {
                lemma_ne_det(s, i + 1, m1, m2);
            } else if n1 {
                lemma_ne_shape(s, i + 1, m1);
            } else if n2 {
                lemma_ne_shape(s, i + 1, m2);
            } else {
                lemma_lts_det(s, i + 1, m1, m2);
            }
        }
    } else if is_line_terminator(s[i]) {
        lemma_lts_det(s, i, m1, m2);
    }
}

// ---------------------------------------------------------------------
// Closing delimiters.
// ---------------------------------------------------------------------

/// The code points that end the characters of a template component at `p`:
/// `` ` `` or `${`.
pub open spec fn delim_at(s: Seq<u32>, p: int) -> bool {
    0 <= p < s.len() && (s[p] == 0x60 || (p + 1 < s.len() && s[p] == 0x24 && s[p + 1] == 0x7B))
}

/// No `TemplateCharacter` starts at a closing delimiter.
pub proof fn lemma_delim_no_char(s: Seq<u32>, p: int)
    requires
        delim_at(s, p),
    ensures
        forall|m: int, tv: Tv, trv: Seq<u16>| !template_character(s, p, m, tv, trv),
{
    assert forall|m: int, tv: Tv, trv: Seq<u16>| !template_character(s, p, m, tv, trv) by {
        if template_character(s, p, m, tv, trv) {
            if s[p] == 0x24 {
                assert(m == p + 1 ==> at(s, m, '{'));
            }
        }
    }
}

} // verus!
