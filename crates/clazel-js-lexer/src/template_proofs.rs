//! Lemmas about [`super::spec`]'s template relations: a `TemplateCharacter`
//! has one length, one TV and one TRV (`lemma_tchar_det`), and none starts
//! at the code points that close a template component (`` ` `` and `${`,
//! `lemma_delim_no_char`).
//!
//! These are the consumption half of what the executable lexer's template
//! scanner needs. The production half is
//! [`lemma_tc_extend`]: a `template_characters` extends by one more
//! `TemplateCharacter` at its end, which `spec.rs`'s explicit trigger on the
//! existential of `template_characters` makes provable (with the automatic
//! trigger `template_character(s, i, k, ..) && template_characters(s, k, j,
//! ..)`, a `template_characters` of two or more characters could not be
//! derived from its parts), and [`lemma_tc_end_unique`]: two derivations of
//! `template_characters` from the same start, each followed by a place no
//! `TemplateCharacter` starts at, end at the same place.

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

// ---------------------------------------------------------------------
// TemplateCharacters: extension at the end, and unique end.
// ---------------------------------------------------------------------

/// `tv_concat` is associative.
pub proof fn lemma_tv_assoc(a: Tv, b: Tv, c: Tv)
    ensures
        tv_concat(tv_concat(a, b), c) =~= tv_concat(a, tv_concat(b, c)),
{
    match (a, b, c) {
        (Some(x), Some(y), Some(z)) => {
            assert((x + y) + z =~= x + (y + z));
        },
        _ => {},
    }
}

/// A `template_characters` over more than one character is one character
/// and `template_characters` of the rest.
pub proof fn lemma_tc_unfold(s: Seq<u32>, i: int, j: int, tv: Tv, trv: Seq<u16>)
    requires
        template_characters(s, i, j, tv, trv),
        !template_character(s, i, j, tv, trv),
    ensures
        exists|k: int, tv1: Tv, trv1: Seq<u16>, tv2: Tv, trv2: Seq<u16>|
            #![trigger template_character(s, i, k, tv1, trv1), tv_concat(tv1, tv2), trv1 + trv2]
            i < k < j && template_character(s, i, k, tv1, trv1) && template_characters(
                s,
                k,
                j,
                tv2,
                trv2,
            ) && tv =~= tv_concat(tv1, tv2) && trv =~= trv1 + trv2,
{
    reveal_with_fuel(template_characters, 2);
}

/// `TemplateCharacters` extends at the end by one `TemplateCharacter`.
pub proof fn lemma_tc_extend(
    s: Seq<u32>,
    i: int,
    m: int,
    j: int,
    tv1: Tv,
    trv1: Seq<u16>,
    tv2: Tv,
    trv2: Seq<u16>,
)
    requires
        i < m < j,
        template_characters(s, i, m, tv1, trv1),
        template_character(s, m, j, tv2, trv2),
    ensures
        template_characters(s, i, j, tv_concat(tv1, tv2), trv1 + trv2),
    decreases m - i,
{
    reveal(template_characters);
    if template_character(s, i, m, tv1, trv1) {
        assert(template_characters(s, m, j, tv2, trv2));
        let tvc = tv_concat(tv1, tv2);
        let trvc = trv1 + trv2;
        assert(i < m < j && template_character(s, i, m, tv1, trv1) && template_characters(
            s,
            m,
            j,
            tv2,
            trv2,
        ) && tvc =~= tv_concat(tv1, tv2) && trvc =~= trv1 + trv2);
    } else {
        lemma_tc_unfold(s, i, m, tv1, trv1);
        let (k0, tva, trva, tvb, trvb) = choose|
            k0: int,
            tva: Tv,
            trva: Seq<u16>,
            tvb: Tv,
            trvb: Seq<u16>,
        |
            #![trigger template_character(s, i, k0, tva, trva), tv_concat(tva, tvb), trva + trvb]
            i < k0 < m && template_character(s, i, k0, tva, trva) && template_characters(
                s,
                k0,
                m,
                tvb,
                trvb,
            ) && tv1 =~= tv_concat(tva, tvb) && trv1 =~= trva + trvb;
        lemma_tc_extend(s, k0, m, j, tvb, trvb, tv2, trv2);
        let tvx = tv_concat(tvb, tv2);
        let trvx = trvb + trv2;
        lemma_tv_assoc(tva, tvb, tv2);
        assert(trv1 + trv2 =~= trva + trvx);
        assert(tv_concat(tv1, tv2) =~= tv_concat(tva, tvx)) by {
            assert(tv1 =~= tv_concat(tva, tvb));
        }
        assert(i < k0 < j && template_character(s, i, k0, tva, trva) && template_characters(
            s,
            k0,
            j,
            tvx,
            trvx,
        ) && tv_concat(tv1, tv2) =~= tv_concat(tva, tvx) && (trv1 + trv2) =~= trva + trvx);
    }
}

/// No `TemplateCharacter` starts at `d`: the end of the characters of a
/// component, whether at a closing delimiter or where the scan is stuck.
pub open spec fn no_char(s: Seq<u32>, d: int) -> bool {
    forall|m: int, tv: Tv, trv: Seq<u16>| !template_character(s, d, m, tv, trv)
}

/// A closing delimiter is such a place.
pub proof fn lemma_delim_no_char_spec(s: Seq<u32>, p: int)
    requires
        delim_at(s, p),
    ensures
        no_char(s, p),
{
    lemma_delim_no_char(s, p);
}

/// `TemplateCharacters` starts with a `TemplateCharacter`.
pub proof fn lemma_tc_has_char(s: Seq<u32>, i: int, j: int, tv: Tv, trv: Seq<u16>)
    requires
        template_characters(s, i, j, tv, trv),
    ensures
        exists|m: int, tv1: Tv, trv1: Seq<u16>| template_character(s, i, m, tv1, trv1),
{
    if template_character(s, i, j, tv, trv) {
    } else {
        lemma_tc_unfold(s, i, j, tv, trv);
        let (k, tv1, trv1, tv2, trv2) = choose|
            k: int,
            tv1: Tv,
            trv1: Seq<u16>,
            tv2: Tv,
            trv2: Seq<u16>,
        |
            #![trigger template_character(s, i, k, tv1, trv1), tv_concat(tv1, tv2), trv1 + trv2]
            i < k < j && template_character(s, i, k, tv1, trv1) && template_characters(
                s,
                k,
                j,
                tv2,
                trv2,
            ) && tv =~= tv_concat(tv1, tv2) && trv =~= trv1 + trv2;
        assert(template_character(s, i, k, tv1, trv1));
    }
}

/// Two derivations of `TemplateCharacters` from the same start, each
/// followed by a place no `TemplateCharacter` starts at, end at the same
/// place.
pub proof fn lemma_tc_pair(
    s: Seq<u32>,
    a: int,
    b: int,
    d: int,
    tv1: Tv,
    trv1: Seq<u16>,
    tv2: Tv,
    trv2: Seq<u16>,
)
    requires
        template_characters(s, a, b, tv1, trv1),
        no_char(s, b),
        template_characters(s, a, d, tv2, trv2),
        no_char(s, d),
    ensures
        b == d,
    decreases b - a,
{
    if template_character(s, a, b, tv1, trv1) {
        if template_character(s, a, d, tv2, trv2) {
            lemma_tchar_det(s, a, b, d, tv1, tv2, trv1, trv2);
        } else {
            lemma_tc_unfold(s, a, d, tv2, trv2);
            let (k1, tva, trva, tvb, trvb) = choose|
                k1: int,
                tva: Tv,
                trva: Seq<u16>,
                tvb: Tv,
                trvb: Seq<u16>,
            |
                #![trigger template_character(s, a, k1, tva, trva), tv_concat(tva, tvb), trva + trvb]
                a < k1 < d && template_character(s, a, k1, tva, trva) && template_characters(
                    s,
                    k1,
                    d,
                    tvb,
                    trvb,
                ) && tv2 =~= tv_concat(tva, tvb) && trv2 =~= trva + trvb;
            lemma_tchar_det(s, a, b, k1, tv1, tva, trv1, trva);
            lemma_tc_has_char(s, k1, d, tvb, trvb);
            let (m, tvx, trvx) = choose|m: int, tvx: Tv, trvx: Seq<u16>|
                template_character(s, k1, m, tvx, trvx);
            assert(!template_character(s, b, m, tvx, trvx));
        }
    } else {
        lemma_tc_unfold(s, a, b, tv1, trv1);
        let (k0, tva, trva, tvb, trvb) = choose|
            k0: int,
            tva: Tv,
            trva: Seq<u16>,
            tvb: Tv,
            trvb: Seq<u16>,
        |
            #![trigger template_character(s, a, k0, tva, trva), tv_concat(tva, tvb), trva + trvb]
            a < k0 < b && template_character(s, a, k0, tva, trva) && template_characters(
                s,
                k0,
                b,
                tvb,
                trvb,
            ) && tv1 =~= tv_concat(tva, tvb) && trv1 =~= trva + trvb;
        if template_character(s, a, d, tv2, trv2) {
            lemma_tchar_det(s, a, k0, d, tva, tv2, trva, trv2);
            lemma_tc_has_char(s, k0, b, tvb, trvb);
            let (m, tvx, trvx) = choose|m: int, tvx: Tv, trvx: Seq<u16>|
                template_character(s, k0, m, tvx, trvx);
            assert(!template_character(s, d, m, tvx, trvx));
        } else {
            lemma_tc_unfold(s, a, d, tv2, trv2);
            let (k1, tvc, trvc, tvd, trvd) = choose|
                k1: int,
                tvc: Tv,
                trvc: Seq<u16>,
                tvd: Tv,
                trvd: Seq<u16>,
            |
                #![trigger template_character(s, a, k1, tvc, trvc), tv_concat(tvc, tvd), trvc + trvd]
                a < k1 < d && template_character(s, a, k1, tvc, trvc) && template_characters(
                    s,
                    k1,
                    d,
                    tvd,
                    trvd,
                ) && tv2 =~= tv_concat(tvc, tvd) && trv2 =~= trvc + trvd;
            lemma_tchar_det(s, a, k0, k1, tva, tvc, trva, trvc);
            lemma_tc_pair(s, k0, b, d, tvb, trvb, tvd, trvd);
        }
    }
}

/// Two derivations of a (possibly empty) run of `TemplateCharacters` from
/// `a`, each followed by a place no `TemplateCharacter` starts at, end at
/// the same place. (The run is empty when it ends where it starts.)
pub proof fn lemma_tc_end_unique(s: Seq<u32>, a: int, b: int, d: int)
    requires
        b == a || exists|tv: Tv, trv: Seq<u16>| template_characters(s, a, b, tv, trv),
        d == a || exists|tv: Tv, trv: Seq<u16>| template_characters(s, a, d, tv, trv),
        no_char(s, b),
        no_char(s, d),
    ensures
        b == d,
{
    if b != a && d != a {
        let (tv1, trv1) = choose|tv: Tv, trv: Seq<u16>| template_characters(s, a, b, tv, trv);
        let (tv2, trv2) = choose|tv: Tv, trv: Seq<u16>| template_characters(s, a, d, tv, trv);
        lemma_tc_pair(s, a, b, d, tv1, trv1, tv2, trv2);
    } else if b != a {
        let (tv1, trv1) = choose|tv: Tv, trv: Seq<u16>| template_characters(s, a, b, tv, trv);
        lemma_tc_has_char(s, a, b, tv1, trv1);
        let (m, tvx, trvx) = choose|m: int, tvx: Tv, trvx: Seq<u16>|
            template_character(s, a, m, tvx, trvx);
        assert(!template_character(s, d, m, tvx, trvx));
    } else if d != a {
        let (tv2, trv2) = choose|tv: Tv, trv: Seq<u16>| template_characters(s, a, d, tv, trv);
        lemma_tc_has_char(s, a, d, tv2, trv2);
        let (m, tvx, trvx) = choose|m: int, tvx: Tv, trvx: Seq<u16>|
            template_character(s, a, m, tvx, trvx);
        assert(!template_character(s, b, m, tvx, trvx));
    }
}

// ---------------------------------------------------------------------
// The code points of a TemplateCharacter are SourceCharacters, and the
// TRV is built by appending.
// ---------------------------------------------------------------------

/// Digits of any radix (with or without separators) are ASCII, so source
/// characters.
pub proof fn lemma_digits_src(radix: int, sep: bool, s: Seq<u32>, i: int, j: int)
    requires
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
        digits(radix, sep, s, i, j),
    ensures
        forall|t: int| i <= t < j ==> s[t] <= 0x10FFFF,
    decreases j - i,
{
    if j == i + 1 && is_radix_digit(radix, s[i]) {
        assert(s[i] <= 0x10FFFF);
    } else if i + 1 < j && is_radix_digit(radix, s[j - 1]) && digits(radix, sep, s, i, j - 1) {
        lemma_digits_src(radix, sep, s, i, j - 1);
        assert forall|t: int| i <= t < j implies s[t] <= 0x10FFFF by {
            if t < j - 1 {
                assert(s[t] <= 0x10FFFF);
            } else {
                assert(s[j - 1] <= 0x10FFFF);
            }
        }
    } else {
        lemma_digits_src(radix, true, s, i, j - 2);
        assert forall|t: int| i <= t < j implies s[t] <= 0x10FFFF by {
            if t < j - 2 {
                assert(s[t] <= 0x10FFFF);
            }
        }
    }
}

/// A `TemplateCharacter` consists of SourceCharacters.
pub proof fn lemma_tchar_src(s: Seq<u32>, i: int, j: int, tv: Tv, trv: Seq<u16>)
    requires
        template_character(s, i, j, tv, trv),
    ensures
        forall|t: int| i <= t < j ==> s[t] <= 0x10FFFF,
{
    lemma_is_lit(s, i + 1, i + 3, seq!['u', '{']);
    if s[i] == 0x5C {
        if exists|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, j, v) {
            let v = choose|v: Seq<u16>| #[trigger] template_escape_sequence_sv(s, i + 1, j, v);
            if unicode_escape_sequence(s, i + 1, j) {
                if !(s[i + 1] == 0x75 && hex4_digits(s, i + 2, j)) {
                    lemma_digits_src(16, false, s, i + 3, j - 1);
                }
            }
        } else if not_escape_sequence(s, i + 1, j) {
            if i + 3 < j && s[i + 1] == 0x75 && s[i + 2] == 0x7B {
                if not_code_point(s, i + 3, j) || code_point(s, i + 3, j) {
                    lemma_digits_src(16, false, s, i + 3, j);
                }
            }
        }
    }
}

/// The UTF-16 of a range extends by the encoding of the next code point.
pub proof fn lemma_utf16_of_push(s: Seq<u32>, i: int, k: int)
    requires
        0 <= i <= k < s.len(),
    ensures
        utf16_of(s, i, k + 1) =~= utf16_of(s, i, k) + utf16_encode_code_point(s[k] as int),
    decreases k - i,
{
    if i < k {
        lemma_utf16_of_push(s, i + 1, k);
        assert(utf16_of(s, i, k + 1) == utf16_encode_code_point(s[i] as int) + utf16_of(
            s,
            i + 1,
            k + 1,
        ));
        assert(utf16_of(s, i, k) == utf16_encode_code_point(s[i] as int) + utf16_of(s, i + 1, k));
    } else {
        assert(utf16_of(s, k, k + 1) =~= utf16_encode_code_point(s[k] as int) + utf16_of(
            s,
            k + 1,
            k + 1,
        ));
    }
}

} // verus!
