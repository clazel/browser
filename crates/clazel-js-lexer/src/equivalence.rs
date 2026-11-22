//! Proofs that [`super::independent`] and [`super::spec`] define the same
//! relation, at every source text and every range, for each production the
//! independent transcription covers (docs/VERIFICATION.md, item 2).
//!
//! The theorems, each `<==>` on all `(s, i, j)` (or on all `(s, k)`), with
//! no precondition:
//!
//! - `white_space(s,i,j) <==> ind_white_space(s,i,j)`, and the same for
//!   `line_terminator` and `line_terminator_sequence`;
//! - `single_line_comment`, `multi_line_comment`, `hashbang_comment`;
//! - `digits(r, false, ..) <==> ind_plain_digits(r, ..)` and
//!   `digits(r, true, ..) <==> ind_sep_digits(r, ..)` for `r` in 2, 8, 10,
//!   16;
//! - `numeric_literal(s,i,j) <==> ind_numeric_literal(s,i,j)`, and the
//!   productions it is built from;
//! - `unicode_escape_sequence(s,i,j) <==> ind_unicode_escape(s,i,j)`;
//! - `other_punctuator`, `optional_chaining_punctuator`, `div_punctuator`
//!   and `right_brace_punctuator` each `<==>` its independent form;
//! - `is_reserved_word(cps, false) <==> ind_is_reserved(cps)`.
//!
//! The identifier ranges are in the identifier part of this file when
//! present; see [`super::independent`] for what is not covered. The only
//! assumption shared by the two files is the uninterpreted `ID_Start` and
//! `ID_Continue` of code points above U+007F.

use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Terminal strings.
// ---------------------------------------------------------------------

/// `is_lit` says, code point by code point, that the range is the literal.
pub proof fn lemma_is_lit(s: Seq<u32>, i: int, j: int, lit: Seq<char>)
    ensures
        is_lit(s, i, j, lit) <==> (0 <= i && j <= s.len() && j - i == lit.len() && forall|k: int|
            0 <= k < lit.len() ==> s[i + k] == #[trigger] lit[k] as u32),
{
    if 0 <= i && j <= s.len() && j - i == lit.len() {
        let m = lit.map_values(|c: char| c as u32);
        if is_lit(s, i, j, lit) {
            assert forall|k: int| 0 <= k < lit.len() implies s[i + k] == #[trigger] lit[k] as u32 by {
                assert(s.subrange(i, j)[k] == m[k]);
            }
        }
        if forall|k: int| 0 <= k < lit.len() ==> s[i + k] == #[trigger] lit[k] as u32 {
            assert(s.subrange(i, j) =~= m) by {
                assert forall|k: int| 0 <= k < lit.len() implies s.subrange(i, j)[k] == m[k] by {
                    assert(s[i + k] == lit[k] as u32);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// White space and line terminators.
// ---------------------------------------------------------------------

/// `WhiteSpace` (§12.2) is Annex A's: one code point of the class.
pub proof fn lemma_white_space_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        white_space(s, i, j) <==> ind_white_space(s, i, j),
{
}

/// `LineTerminator` (§12.3).
pub proof fn lemma_line_terminator_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        line_terminator(s, i, j) <==> ind_line_terminator(s, i, j),
{
}

/// `LineTerminatorSequence` (§12.3).
pub proof fn lemma_line_terminator_sequence_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        line_terminator_sequence(s, i, j) <==> ind_line_terminator_sequence(s, i, j),
{
}

// ---------------------------------------------------------------------
// Comments.
// ---------------------------------------------------------------------

/// `SingleLineComment` (§12.4).
pub proof fn lemma_single_line_comment_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        single_line_comment(s, i, j) <==> ind_single_line_comment(s, i, j),
{
    lemma_is_lit(s, i, i + 2, seq!['/', '/']);
}

/// `HashbangComment` (§12.5).
pub proof fn lemma_hashbang_comment_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        hashbang_comment(s, i, j) <==> ind_hashbang_comment(s, i, j),
{
    lemma_is_lit(s, i, i + 2, seq!['#', '!']);
}

/// No `*/` begins inside `s[a..b)` (the pair may end at `b - 1` at most).
pub open spec fn no_star_slash(s: Seq<u32>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b - 1 ==> !(#[trigger] s[k] == 0x2A && s[k + 1] == 0x2F)
}

/// Every code point of `s[a..b)` is a `SourceCharacter`.
pub open spec fn all_source(s: Seq<u32>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b ==> #[trigger] s[k] <= 0x10FFFF
}

/// `MultiLineCommentChars` is "no `*/` inside", and `PostAsteriskCommentChars`
/// is the same after a `*`: the first code point is not `/`. Both on a
/// non-empty range, by induction on its length.
pub proof fn lemma_comment_chars(s: Seq<u32>, a: int, b: int)
    ensures
        multi_line_comment_chars(s, a, b) <==> (0 <= a && a < b && b <= s.len() && all_source(
            s,
            a,
            b,
        ) && no_star_slash(s, a, b)),
        post_asterisk_comment_chars(s, a, b) <==> (0 <= a && a < b && b <= s.len() && all_source(
            s,
            a,
            b,
        ) && s[a] != 0x2F && no_star_slash(s, a, b)),
    decreases b - a,
{
    if 0 <= a && a + 1 < b && b <= s.len() {
        lemma_comment_chars(s, a + 1, b);
        assert(no_star_slash(s, a, b) <==> (no_star_slash(s, a + 1, b) && !(s[a] == 0x2A && s[a
            + 1] == 0x2F))) by {
            if no_star_slash(s, a, b) {
                assert forall|k: int| a + 1 <= k < b - 1 implies !(#[trigger] s[k] == 0x2A && s[k
                    + 1] == 0x2F) by {
                    assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                }
            }
            if no_star_slash(s, a + 1, b) && !(s[a] == 0x2A && s[a + 1] == 0x2F) {
                assert forall|k: int| a <= k < b - 1 implies !(#[trigger] s[k] == 0x2A && s[k
                    + 1] == 0x2F) by {
                    if k > a {
                        assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                    }
                }
            }
        }
        assert(all_source(s, a, b) <==> (s[a] <= 0x10FFFF && all_source(s, a + 1, b))) by {
            if all_source(s, a + 1, b) && s[a] <= 0x10FFFF {
                assert forall|k: int| a <= k < b implies #[trigger] s[k] <= 0x10FFFF by {
                    if k > a {
                        assert(s[k] <= 0x10FFFF);
                    }
                }
            }
        }
    }
    if 0 <= a && a + 1 == b && b <= s.len() {
        assert(no_star_slash(s, a, b));
        assert(all_source(s, a, b) <==> s[a] <= 0x10FFFF);
    }
}

/// `MultiLineComment` (§12.4).
pub proof fn lemma_multi_line_comment_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        multi_line_comment(s, i, j) <==> ind_multi_line_comment(s, i, j),
{
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_is_lit(s, j - 2, j, seq!['*', '/']);
    if 0 <= i && i + 4 <= j && j <= s.len() {
        if i + 2 < j - 2 {
            lemma_comment_chars(s, i + 2, j - 2);
        }
        // The range of the content ends with the closing `*` at j - 2, so
        // the pair that would start at j - 3 is `?*`, never `*/`.
        if multi_line_comment(s, i, j) {
            assert forall|k: int| i + 2 <= k < j - 2 implies !(#[trigger] s[k] == 0x2A && s[k
                + 1] == 0x2F) by {
                if k < j - 3 {
                    assert(no_star_slash(s, i + 2, j - 2));
                }
            }
            assert forall|k: int| i + 2 <= k < j - 2 implies ind_src_cp(#[trigger] s[k]) by {
                assert(all_source(s, i + 2, j - 2) || i + 2 == j - 2);
            }
        }
        if ind_multi_line_comment(s, i, j) {
            if i + 2 < j - 2 {
                assert(no_star_slash(s, i + 2, j - 2)) by {
                    assert forall|k: int| i + 2 <= k < j - 3 implies !(#[trigger] s[k] == 0x2A
                        && s[k + 1] == 0x2F) by {
                        assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                    }
                }
                assert(all_source(s, i + 2, j - 2));
            }
        }
    }
}

// ---------------------------------------------------------------------
// Digit classes and digit runs.
// ---------------------------------------------------------------------

/// The digit classes of the two files agree for the four radices.
pub proof fn lemma_digit_class_equiv(radix: int, c: u32)
    requires
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        is_radix_digit(radix, c) <==> ind_radix_digit(radix, c),
{
}

/// `Digits[~Sep]` is a run of one or more digits.
pub proof fn lemma_plain_digits_equiv(radix: int, s: Seq<u32>, i: int, j: int)
    requires
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        digits(radix, false, s, i, j) <==> ind_plain_digits(radix, s, i, j),
    decreases j - i,
{
    if 0 <= i && i + 1 < j && j <= s.len() {
        lemma_plain_digits_equiv(radix, s, i, j - 1);
        if digits(radix, false, s, i, j) {
            assert forall|k: int| i <= k < j implies ind_radix_digit(radix, #[trigger] s[k]) by {
                if k < j - 1 {
                    assert(ind_plain_digits(radix, s, i, j - 1));
                }
            }
        }
        if ind_plain_digits(radix, s, i, j) {
            assert(ind_plain_digits(radix, s, i, j - 1)) by {
                assert forall|k: int| i <= k < j - 1 implies ind_radix_digit(radix, #[trigger] s[k]) by {
                    assert(ind_radix_digit(radix, s[k]));
                }
            }
        }
    }
}

/// `Digits[+Sep]` is the closed form: digits and single `_`, ending and
/// starting with a digit.
pub proof fn lemma_sep_digits_equiv(radix: int, s: Seq<u32>, i: int, j: int)
    requires
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        digits(radix, true, s, i, j) <==> ind_sep_digits(radix, s, i, j),
    decreases j - i,
{
    if 0 <= i && i + 1 < j && j <= s.len() {
        if i + 2 < j {
            lemma_sep_digits_equiv(radix, s, i, j - 2);
        }
        lemma_sep_digits_equiv(radix, s, i, j - 1);
        // (spec ==> independent)
        if digits(radix, true, s, i, j) {
            if i + 1 < j && ind_radix_digit(radix, s[j - 1]) && digits(radix, true, s, i, j - 1) {
                assert(ind_sep_digits(radix, s, i, j - 1));
                assert forall|k: int| i <= k < j - 1 implies !(#[trigger] s[k] == 0x5F && s[k
                    + 1] == 0x5F) by {
                    if k < j - 2 {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
                assert forall|k: int| i <= k < j implies (ind_radix_digit(radix, #[trigger] s[k])
                    || s[k] == 0x5F) by {
                    if k < j - 1 {
                        assert(ind_radix_digit(radix, s[k]) || s[k] == 0x5F);
                    }
                }
            }
            if i + 2 < j && s[j - 2] == 0x5F && ind_radix_digit(radix, s[j - 1]) && digits(
                radix,
                true,
                s,
                i,
                j - 2,
            ) {
                assert(ind_sep_digits(radix, s, i, j - 2));
                assert forall|k: int| i <= k < j - 1 implies !(#[trigger] s[k] == 0x5F && s[k
                    + 1] == 0x5F) by {
                    if k < j - 3 {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
                assert forall|k: int| i <= k < j implies (ind_radix_digit(radix, #[trigger] s[k])
                    || s[k] == 0x5F) by {
                    if k < j - 2 {
                        assert(ind_radix_digit(radix, s[k]) || s[k] == 0x5F);
                    }
                }
            }
        }
        // (independent ==> spec)
        if ind_sep_digits(radix, s, i, j) {
            assert(ind_radix_digit(radix, s[j - 1]));
            assert(ind_radix_digit(radix, s[j - 2]) || s[j - 2] == 0x5F);
            if ind_radix_digit(radix, s[j - 2]) {
                assert(ind_sep_digits(radix, s, i, j - 1)) by {
                    assert forall|k: int| i <= k < j - 1 implies (ind_radix_digit(
                        radix,
                        #[trigger] s[k],
                    ) || s[k] == 0x5F) by {
                        assert(ind_radix_digit(radix, s[k]) || s[k] == 0x5F);
                    }
                    assert forall|k: int| i <= k < j - 2 implies !(#[trigger] s[k] == 0x5F && s[k
                        + 1] == 0x5F) by {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
            } else {
                // s[j-2] is `_`, so it is not s[i] (a digit): i + 2 < j.
                assert(i + 2 < j);
                assert(ind_radix_digit(radix, s[j - 3]) || s[j - 3] == 0x5F);
                assert(!(s[j - 3] == 0x5F && s[j - 2] == 0x5F));
                assert(ind_sep_digits(radix, s, i, j - 2)) by {
                    assert forall|k: int| i <= k < j - 2 implies (ind_radix_digit(
                        radix,
                        #[trigger] s[k],
                    ) || s[k] == 0x5F) by {
                        assert(ind_radix_digit(radix, s[k]) || s[k] == 0x5F);
                    }
                    assert forall|k: int| i <= k < j - 3 implies !(#[trigger] s[k] == 0x5F && s[k
                        + 1] == 0x5F) by {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
            }
        }
    }
}

/// The value of a run of hex digits is the same fold.
pub proof fn lemma_hex_value_equiv(s: Seq<u32>, a: int, b: int)
    requires
        0 <= a,
        b <= s.len(),
        forall|k: int| a <= k < b ==> is_hex_digit(#[trigger] s[k]),
    ensures
        hex_digits_mv(s, a, b) == ind_hex_run_value(s, a, b),
    decreases b - a,
{
    if a < b {
        assert(is_hex_digit(s[b - 1]));
        lemma_hex_value_equiv(s, a, b - 1);
    }
}

// ---------------------------------------------------------------------
// Numeric literals.
// ---------------------------------------------------------------------

/// `LegacyOctalLikeDecimalIntegerLiteral` is `0` and one or more octal
/// digits.
pub proof fn lemma_legacy_octal_like_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        legacy_octal_like_decimal_integer_literal(s, i, j) <==> ind_legacy_octal(s, i, j),
    decreases j - i,
{
    if 0 <= i && i + 2 < j && j <= s.len() {
        lemma_legacy_octal_like_equiv(s, i, j - 1);
        lemma_plain_digits_equiv(8, s, i + 1, j);
        lemma_plain_digits_equiv(8, s, i + 1, j - 1);
    }
    if 0 <= i && i + 2 == j && j <= s.len() {
        lemma_plain_digits_equiv(8, s, i + 1, j);
    }
}

/// `LegacyOctalIntegerLiteral` is the same language.
pub proof fn lemma_legacy_octal_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        legacy_octal_integer_literal(s, i, j) <==> ind_legacy_octal(s, i, j),
    decreases j - i,
{
    if 0 <= i && i + 2 < j && j <= s.len() {
        lemma_legacy_octal_equiv(s, i, j - 1);
        lemma_plain_digits_equiv(8, s, i + 1, j);
        lemma_plain_digits_equiv(8, s, i + 1, j - 1);
    }
    if 0 <= i && i + 2 == j && j <= s.len() {
        lemma_plain_digits_equiv(8, s, i + 1, j);
    }
}

/// `NonOctalDecimalIntegerLiteral` is `0`, decimal digits, one of them 8
/// or 9.
pub proof fn lemma_non_octal_decimal_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        non_octal_decimal_integer_literal(s, i, j) <==> ind_non_octal_decimal_integer(s, i, j),
    decreases j - i,
{
    if 0 <= i && i + 2 < j && j <= s.len() {
        lemma_non_octal_decimal_equiv(s, i, j - 1);
        lemma_legacy_octal_like_equiv(s, i, j - 1);
        lemma_plain_digits_equiv(10, s, i + 1, j);
        lemma_plain_digits_equiv(10, s, i + 1, j - 1);
        lemma_plain_digits_equiv(8, s, i + 1, j - 1);
        // (spec ==> independent)
        if non_octal_decimal_integer_literal(s, i, j) {
            if is_non_octal_digit(s[j - 1]) && legacy_octal_like_decimal_integer_literal(
                s,
                i,
                j - 1,
            ) {
                assert(s[j - 1] == 0x38 || s[j - 1] == 0x39);
            }
        }
        // (independent ==> spec)
        if ind_non_octal_decimal_integer(s, i, j) {
            let k = choose|k: int| i < k < j && (s[k] == 0x38 || s[k] == 0x39);
            if exists|k2: int| i < k2 < j - 1 && (#[trigger] s[k2] == 0x38 || s[k2] == 0x39) {
                let k2 = choose|k2: int| i < k2 < j - 1 && (s[k2] == 0x38 || s[k2] == 0x39);
                assert(ind_non_octal_decimal_integer(s, i, j - 1));
            } else {
                assert(k == j - 1);
                assert(ind_legacy_octal(s, i, j - 1)) by {
                    assert forall|t: int| i + 1 <= t < j - 1 implies ind_oct(#[trigger] s[t]) by {
                        assert(ind_dec(s[t]));
                        assert(!(s[t] == 0x38 || s[t] == 0x39));
                    }
                }
            }
        }
    }
    if 0 <= i && i + 2 == j && j <= s.len() {
        lemma_plain_digits_equiv(10, s, i + 1, j);
        if ind_non_octal_decimal_integer(s, i, j) {
            assert(s[i + 1] == 0x38 || s[i + 1] == 0x39);
        }
    }
}

/// A separated digit run that does not start with `0` is exactly the
/// non-zero-led shapes of §12.9.3: a single `NonZeroDigit`, or one followed
/// by `DecimalDigits[+Sep]` with or without a separator.
pub proof fn lemma_nonzero_led_equiv(s: Seq<u32>, i: int, e: int)
    requires
        0 <= i < e <= s.len(),
    ensures
        (ind_sep_digits(10, s, i, e) && s[i] != 0x30) <==> ((e == i + 1 && is_non_zero_digit(s[i]))
            || (i + 1 < e && is_non_zero_digit(s[i]) && (decimal_digits(true, s, i + 1, e) || (s[i + 1]
            == 0x5F && decimal_digits(true, s, i + 2, e))))),
{
    lemma_sep_digits_equiv(10, s, i + 1, e);
    lemma_sep_digits_equiv(10, s, i + 2, e);
    if ind_sep_digits(10, s, i, e) && s[i] != 0x30 {
        assert(ind_dec(s[i]));
        if e > i + 1 {
            assert(ind_dec(s[i + 1]) || s[i + 1] == 0x5F);
            if ind_dec(s[i + 1]) {
                assert(ind_sep_digits(10, s, i + 1, e)) by {
                    assert forall|k: int| i + 1 <= k < e implies (ind_dec(#[trigger] s[k]) || s[k]
                        == 0x5F) by {
                        assert(ind_dec(s[k]) || s[k] == 0x5F);
                    }
                    assert forall|k: int| i + 1 <= k < e - 1 implies !(#[trigger] s[k] == 0x5F
                        && s[k + 1] == 0x5F) by {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
            } else {
                assert(ind_dec(s[e - 1]));
                assert(i + 2 < e);
                assert(ind_dec(s[i + 2]) || s[i + 2] == 0x5F);
                assert(!(s[i + 1] == 0x5F && s[i + 2] == 0x5F));
                assert(ind_sep_digits(10, s, i + 2, e)) by {
                    assert forall|k: int| i + 2 <= k < e implies (ind_dec(#[trigger] s[k]) || s[k]
                        == 0x5F) by {
                        assert(ind_dec(s[k]) || s[k] == 0x5F);
                    }
                    assert forall|k: int| i + 2 <= k < e - 1 implies !(#[trigger] s[k] == 0x5F
                        && s[k + 1] == 0x5F) by {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
            }
        }
    }
    if e == i + 1 && is_non_zero_digit(s[i]) {
        assert(ind_sep_digits(10, s, i, e));
    }
    if i + 1 < e && is_non_zero_digit(s[i]) {
        if decimal_digits(true, s, i + 1, e) {
            assert(ind_sep_digits(10, s, i + 1, e));
            assert(ind_sep_digits(10, s, i, e)) by {
                assert forall|k: int| i <= k < e implies (ind_dec(#[trigger] s[k]) || s[k]
                    == 0x5F) by {
                    if k > i {
                        assert(ind_dec(s[k]) || s[k] == 0x5F);
                    }
                }
                assert forall|k: int| i <= k < e - 1 implies !(#[trigger] s[k] == 0x5F && s[k + 1]
                    == 0x5F) by {
                    if k > i {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
            }
        }
        if s[i + 1] == 0x5F && decimal_digits(true, s, i + 2, e) {
            assert(ind_sep_digits(10, s, i + 2, e));
            assert(ind_sep_digits(10, s, i, e)) by {
                assert forall|k: int| i <= k < e implies (ind_dec(#[trigger] s[k]) || s[k]
                    == 0x5F) by {
                    if k > i + 1 {
                        assert(ind_dec(s[k]) || s[k] == 0x5F);
                    }
                }
                assert forall|k: int| i <= k < e - 1 implies !(#[trigger] s[k] == 0x5F && s[k + 1]
                    == 0x5F) by {
                    if k > i + 1 {
                        assert(!(s[k] == 0x5F && s[k + 1] == 0x5F));
                    }
                }
            }
        }
    }
}

/// `DecimalIntegerLiteral` (§12.9.3).
pub proof fn lemma_decimal_integer_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        decimal_integer_literal(s, i, j) <==> ind_decimal_integer(s, i, j),
{
    lemma_non_octal_decimal_equiv(s, i, j);
    if 0 <= i && i < j && j <= s.len() {
        lemma_nonzero_led_equiv(s, i, j);
    }
}

/// `ExponentPart[+Sep]` (§12.9.3).
pub proof fn lemma_exponent_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        exponent_part(true, s, i, j) <==> ind_exponent(s, i, j),
{
    lemma_sep_digits_equiv(10, s, i + 1, j);
    lemma_sep_digits_equiv(10, s, i + 2, j);
}

/// The first alternative's body is the independent one, at every split.
pub proof fn lemma_alt1_pointwise(s: Seq<u32>, i: int, j: int, a: int, b: int)
    ensures
        decimal_literal_1(s, i, a, b, j) <==> ind_dl_alt1(s, i, j, a, b),
{
    lemma_sep_digits_equiv(10, s, a + 1, b);
    lemma_decimal_integer_equiv(s, i, a);
    lemma_exponent_equiv(s, b, j);
    if ind_dl_alt1(s, i, j, a, b) {
        assert(j <= s.len()) by {
            if b == j {
                if b != a + 1 {
                    assert(ind_sep_digits(10, s, a + 1, b));
                }
            } else {
                assert(ind_exponent(s, b, j));
                assert(ind_sep_digits(10, s, b + 1, j) || ind_sep_digits(10, s, b + 2, j));
            }
        }
    }
}

/// The body of the second alternative of `DecimalLiteral`, at the end `b`
/// of the digits.
pub open spec fn sp_alt2(s: Seq<u32>, i: int, j: int, b: int) -> bool {
    i + 1 < b && b <= j && decimal_digits(true, s, i + 1, b) && opt(
        b,
        j,
        exponent_part(true, s, b, j),
    )
}

/// The body of the third alternative, at the end `a` of the integer.
pub open spec fn sp_alt3(s: Seq<u32>, i: int, j: int, a: int) -> bool {
    i < a && a <= j && decimal_integer_literal(s, i, a) && opt(a, j, exponent_part(true, s, a, j))
}

/// The second and third alternatives' bodies are the independent ones.
pub proof fn lemma_alt23_pointwise(s: Seq<u32>, i: int, j: int, k: int)
    ensures
        (ind_is(s, i, 0x2E) && sp_alt2(s, i, j, k)) <==> ind_dl_alt2(s, i, j, k),
        sp_alt3(s, i, j, k) <==> ind_dl_alt3(s, i, j, k),
{
    lemma_sep_digits_equiv(10, s, i + 1, k);
    lemma_exponent_equiv(s, k, j);
    lemma_decimal_integer_equiv(s, i, k);
}

/// `DecimalLiteral` (§12.9.3).
pub proof fn lemma_decimal_literal_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        decimal_literal(s, i, j) <==> ind_decimal_literal(s, i, j),
{
    // spec ==> independent
    if decimal_literal(s, i, j) {
        if exists|a: int, b: int| decimal_literal_1(s, i, a, b, j) {
            let (a, b) = choose|a: int, b: int| decimal_literal_1(s, i, a, b, j);
            lemma_alt1_pointwise(s, i, j, a, b);
            assert(ind_dl_alt1(s, i, j, a, b));
        } else if s[i] == 0x2E && exists|b: int| #![auto]
            i + 1 < b && b <= j && decimal_digits(true, s, i + 1, b) && opt(
                b,
                j,
                exponent_part(true, s, b, j),
            ) {
            let b = choose|b: int| #![auto]
                i + 1 < b && b <= j && decimal_digits(true, s, i + 1, b) && opt(
                    b,
                    j,
                    exponent_part(true, s, b, j),
                );
            assert(sp_alt2(s, i, j, b));
            lemma_alt23_pointwise(s, i, j, b);
            assert(ind_dl_alt2(s, i, j, b));
        } else if exists|a: int| #![auto]
            i < a && a <= j && decimal_integer_literal(s, i, a) && opt(
                a,
                j,
                exponent_part(true, s, a, j),
            ) {
            let a = choose|a: int| #![auto]
                i < a && a <= j && decimal_integer_literal(s, i, a) && opt(
                    a,
                    j,
                    exponent_part(true, s, a, j),
                );
            assert(sp_alt3(s, i, j, a));
            lemma_alt23_pointwise(s, i, j, a);
            assert(ind_dl_alt3(s, i, j, a));
        }
    }
    // independent ==> spec
    if ind_decimal_literal(s, i, j) {
        if exists|a: int, b: int| ind_dl_alt1(s, i, j, a, b) {
            let (a, b) = choose|a: int, b: int| ind_dl_alt1(s, i, j, a, b);
            lemma_alt1_pointwise(s, i, j, a, b);
            assert(decimal_literal_1(s, i, a, b, j));
            assert(decimal_literal(s, i, j));
        } else if exists|b: int| ind_dl_alt2(s, i, j, b) {
            let b = choose|b: int| ind_dl_alt2(s, i, j, b);
            lemma_alt23_pointwise(s, i, j, b);
            assert(sp_alt2(s, i, j, b));
            assert(decimal_literal(s, i, j));
        } else if exists|a: int| ind_dl_alt3(s, i, j, a) {
            let a = choose|a: int| ind_dl_alt3(s, i, j, a);
            lemma_alt23_pointwise(s, i, j, a);
            assert(sp_alt3(s, i, j, a));
            assert(decimal_literal(s, i, j));
        }
    }
}

/// `DecimalBigIntegerLiteral` (§12.9.3).
pub proof fn lemma_decimal_bigint_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        decimal_big_integer_literal(s, i, j) <==> ind_decimal_bigint(s, i, j),
{
    if 0 <= i && i + 1 < j && j <= s.len() && s[j - 1] == 0x6E {
        lemma_nonzero_led_equiv(s, i, j - 1);
        lemma_sep_digits_equiv(10, s, i + 1, j - 1);
    }
}

/// `NonDecimalIntegerLiteral[+Sep]` (§12.9.3).
pub proof fn lemma_non_decimal_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        non_decimal_integer_literal(true, s, i, j) <==> ind_non_decimal_integer(s, i, j),
{
    lemma_sep_digits_equiv(2, s, i + 2, j);
    lemma_sep_digits_equiv(8, s, i + 2, j);
    lemma_sep_digits_equiv(16, s, i + 2, j);
}

/// `NumericLiteral` (§12.9.3): equal as relations on every range.
pub proof fn lemma_numeric_literal_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        numeric_literal(s, i, j) <==> ind_numeric_literal(s, i, j),
{
    lemma_decimal_literal_equiv(s, i, j);
    lemma_decimal_bigint_equiv(s, i, j);
    lemma_non_decimal_equiv(s, i, j);
    lemma_non_decimal_equiv(s, i, j - 1);
    lemma_legacy_octal_equiv(s, i, j);
}

// ---------------------------------------------------------------------
// Unicode escape sequences.
// ---------------------------------------------------------------------

/// `ind_hex_run_end` is the first index at or after `k` that is not a hex
/// digit: everything before it is a hex digit, and it is not one (or is the
/// end).
pub proof fn lemma_hex_run_end(s: Seq<u32>, k: int)
    requires
        0 <= k <= s.len(),
    ensures
        k <= ind_hex_run_end(s, k) <= s.len(),
        forall|t: int| k <= t < ind_hex_run_end(s, k) ==> ind_hex(#[trigger] s[t]),
        ind_hex_run_end(s, k) == s.len() || !ind_hex(s[ind_hex_run_end(s, k)]),
    decreases s.len() - k,
{
    if k < s.len() && ind_hex(s[k]) {
        lemma_hex_run_end(s, k + 1);
        let m = ind_hex_run_end(s, k + 1);
        assert forall|t: int| k <= t < m implies ind_hex(#[trigger] s[t]) by {
            if t > k {
                assert(ind_hex(s[t]));
            }
        }
    }
}

/// `UnicodeEscapeSequence` (§12.9.4): the deterministic reading ends at `j`
/// exactly when the grammar derives `s[i..j)`.
pub proof fn lemma_unicode_escape_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        unicode_escape_sequence(s, i, j) <==> ind_unicode_escape(s, i, j),
{
    lemma_is_lit(s, i, i + 2, seq!['u', '{']);
    if 0 <= i && i + 2 <= s.len() {
        lemma_hex_run_end(s, i + 1);
        lemma_hex_run_end(s, i + 2);
        let m1 = ind_hex_run_end(s, i + 1);
        let m = ind_hex_run_end(s, i + 2);
        // (grammar ==> deterministic reading)
        if unicode_escape_sequence(s, i, j) {
            if s[i + 1] == 0x7B {
                // u{ CodePoint }
                lemma_plain_digits_equiv(16, s, i + 2, j - 1);
                assert(ind_plain_digits(16, s, i + 2, j - 1));
                assert(forall|t: int| i + 2 <= t < j - 1 ==> is_hex_digit(s[t]));
                lemma_hex_value_equiv(s, i + 2, j - 1);
                assert(m == j - 1) by {
                    if m < j - 1 {
                        assert(ind_hex(s[m]));
                    }
                    if m > j - 1 {
                        assert(ind_hex(s[j - 1]));
                    }
                }
            } else {
                // u Hex4Digits
                assert(j == i + 5);
                assert(m1 >= i + 5) by {
                    if m1 < i + 5 {
                        assert(ind_hex(s[m1]));
                    }
                }
            }
        }
        // (deterministic reading ==> grammar)
        if ind_unicode_escape(s, i, j) {
            if s[i + 1] == 0x7B {
                assert(m > i + 2 && s[m] == 0x7D && j == m + 1);
                lemma_hex_value_equiv(s, i + 2, m);
                lemma_plain_digits_equiv(16, s, i + 2, m);
                assert(ind_plain_digits(16, s, i + 2, m));
            } else {
                assert(j == i + 5);
                lemma_plain_digits_equiv(16, s, i + 1, i + 5);
                assert(forall|t: int| i + 1 <= t < i + 5 ==> ind_hex(s[t]));
            }
        }
    }
}

// ---------------------------------------------------------------------
// Punctuators and reserved words.
// ---------------------------------------------------------------------

/// The list of `OtherPunctuator` has 53 entries.
pub proof fn lemma_other_punctuators_len()
    ensures
        other_punctuators().len() == 53,
{
}

/// `OtherPunctuator` (§12.8) is the independent one-to-four-code-point
/// classification, at every range. The proof walks the 53 entries of the
/// standard's list one by one in each direction.
pub proof fn lemma_other_punctuator_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        other_punctuator(s, i, j) <==> ind_other_punctuator(s, i, j),
{
    lemma_other_punctuators_len();
    // (spec ==> independent): every entry of the list has one of the forms.
    if other_punctuator(s, i, j) {
        let n = choose|n: int|
            0 <= n < other_punctuators().len() && is_lit(s, i, j, #[trigger] other_punctuators()[n]);
        if n == 0 {
            lemma_is_lit(s, i, j, other_punctuators()[0]);
            assert(other_punctuators()[0][0] as u32 == 0x7B);
            assert(s[i + 0] == 0x7B);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 1 {
            lemma_is_lit(s, i, j, other_punctuators()[1]);
            assert(other_punctuators()[1][0] as u32 == 0x28);
            assert(s[i + 0] == 0x28);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 2 {
            lemma_is_lit(s, i, j, other_punctuators()[2]);
            assert(other_punctuators()[2][0] as u32 == 0x29);
            assert(s[i + 0] == 0x29);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 3 {
            lemma_is_lit(s, i, j, other_punctuators()[3]);
            assert(other_punctuators()[3][0] as u32 == 0x5B);
            assert(s[i + 0] == 0x5B);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 4 {
            lemma_is_lit(s, i, j, other_punctuators()[4]);
            assert(other_punctuators()[4][0] as u32 == 0x5D);
            assert(s[i + 0] == 0x5D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 5 {
            lemma_is_lit(s, i, j, other_punctuators()[5]);
            assert(other_punctuators()[5][0] as u32 == 0x2E);
            assert(s[i + 0] == 0x2E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 6 {
            lemma_is_lit(s, i, j, other_punctuators()[6]);
            assert(other_punctuators()[6][0] as u32 == 0x2E);
            assert(s[i + 0] == 0x2E);
            assert(other_punctuators()[6][1] as u32 == 0x2E);
            assert(s[i + 1] == 0x2E);
            assert(other_punctuators()[6][2] as u32 == 0x2E);
            assert(s[i + 2] == 0x2E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 7 {
            lemma_is_lit(s, i, j, other_punctuators()[7]);
            assert(other_punctuators()[7][0] as u32 == 0x3B);
            assert(s[i + 0] == 0x3B);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 8 {
            lemma_is_lit(s, i, j, other_punctuators()[8]);
            assert(other_punctuators()[8][0] as u32 == 0x2C);
            assert(s[i + 0] == 0x2C);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 9 {
            lemma_is_lit(s, i, j, other_punctuators()[9]);
            assert(other_punctuators()[9][0] as u32 == 0x3C);
            assert(s[i + 0] == 0x3C);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 10 {
            lemma_is_lit(s, i, j, other_punctuators()[10]);
            assert(other_punctuators()[10][0] as u32 == 0x3E);
            assert(s[i + 0] == 0x3E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 11 {
            lemma_is_lit(s, i, j, other_punctuators()[11]);
            assert(other_punctuators()[11][0] as u32 == 0x3C);
            assert(s[i + 0] == 0x3C);
            assert(other_punctuators()[11][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 12 {
            lemma_is_lit(s, i, j, other_punctuators()[12]);
            assert(other_punctuators()[12][0] as u32 == 0x3E);
            assert(s[i + 0] == 0x3E);
            assert(other_punctuators()[12][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 13 {
            lemma_is_lit(s, i, j, other_punctuators()[13]);
            assert(other_punctuators()[13][0] as u32 == 0x3D);
            assert(s[i + 0] == 0x3D);
            assert(other_punctuators()[13][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 14 {
            lemma_is_lit(s, i, j, other_punctuators()[14]);
            assert(other_punctuators()[14][0] as u32 == 0x21);
            assert(s[i + 0] == 0x21);
            assert(other_punctuators()[14][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 15 {
            lemma_is_lit(s, i, j, other_punctuators()[15]);
            assert(other_punctuators()[15][0] as u32 == 0x3D);
            assert(s[i + 0] == 0x3D);
            assert(other_punctuators()[15][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(other_punctuators()[15][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 16 {
            lemma_is_lit(s, i, j, other_punctuators()[16]);
            assert(other_punctuators()[16][0] as u32 == 0x21);
            assert(s[i + 0] == 0x21);
            assert(other_punctuators()[16][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(other_punctuators()[16][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 17 {
            lemma_is_lit(s, i, j, other_punctuators()[17]);
            assert(other_punctuators()[17][0] as u32 == 0x2B);
            assert(s[i + 0] == 0x2B);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 18 {
            lemma_is_lit(s, i, j, other_punctuators()[18]);
            assert(other_punctuators()[18][0] as u32 == 0x2D);
            assert(s[i + 0] == 0x2D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 19 {
            lemma_is_lit(s, i, j, other_punctuators()[19]);
            assert(other_punctuators()[19][0] as u32 == 0x2A);
            assert(s[i + 0] == 0x2A);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 20 {
            lemma_is_lit(s, i, j, other_punctuators()[20]);
            assert(other_punctuators()[20][0] as u32 == 0x25);
            assert(s[i + 0] == 0x25);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 21 {
            lemma_is_lit(s, i, j, other_punctuators()[21]);
            assert(other_punctuators()[21][0] as u32 == 0x2A);
            assert(s[i + 0] == 0x2A);
            assert(other_punctuators()[21][1] as u32 == 0x2A);
            assert(s[i + 1] == 0x2A);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 22 {
            lemma_is_lit(s, i, j, other_punctuators()[22]);
            assert(other_punctuators()[22][0] as u32 == 0x2B);
            assert(s[i + 0] == 0x2B);
            assert(other_punctuators()[22][1] as u32 == 0x2B);
            assert(s[i + 1] == 0x2B);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 23 {
            lemma_is_lit(s, i, j, other_punctuators()[23]);
            assert(other_punctuators()[23][0] as u32 == 0x2D);
            assert(s[i + 0] == 0x2D);
            assert(other_punctuators()[23][1] as u32 == 0x2D);
            assert(s[i + 1] == 0x2D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 24 {
            lemma_is_lit(s, i, j, other_punctuators()[24]);
            assert(other_punctuators()[24][0] as u32 == 0x3C);
            assert(s[i + 0] == 0x3C);
            assert(other_punctuators()[24][1] as u32 == 0x3C);
            assert(s[i + 1] == 0x3C);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 25 {
            lemma_is_lit(s, i, j, other_punctuators()[25]);
            assert(other_punctuators()[25][0] as u32 == 0x3E);
            assert(s[i + 0] == 0x3E);
            assert(other_punctuators()[25][1] as u32 == 0x3E);
            assert(s[i + 1] == 0x3E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 26 {
            lemma_is_lit(s, i, j, other_punctuators()[26]);
            assert(other_punctuators()[26][0] as u32 == 0x3E);
            assert(s[i + 0] == 0x3E);
            assert(other_punctuators()[26][1] as u32 == 0x3E);
            assert(s[i + 1] == 0x3E);
            assert(other_punctuators()[26][2] as u32 == 0x3E);
            assert(s[i + 2] == 0x3E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 27 {
            lemma_is_lit(s, i, j, other_punctuators()[27]);
            assert(other_punctuators()[27][0] as u32 == 0x26);
            assert(s[i + 0] == 0x26);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 28 {
            lemma_is_lit(s, i, j, other_punctuators()[28]);
            assert(other_punctuators()[28][0] as u32 == 0x7C);
            assert(s[i + 0] == 0x7C);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 29 {
            lemma_is_lit(s, i, j, other_punctuators()[29]);
            assert(other_punctuators()[29][0] as u32 == 0x5E);
            assert(s[i + 0] == 0x5E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 30 {
            lemma_is_lit(s, i, j, other_punctuators()[30]);
            assert(other_punctuators()[30][0] as u32 == 0x21);
            assert(s[i + 0] == 0x21);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 31 {
            lemma_is_lit(s, i, j, other_punctuators()[31]);
            assert(other_punctuators()[31][0] as u32 == 0x7E);
            assert(s[i + 0] == 0x7E);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 32 {
            lemma_is_lit(s, i, j, other_punctuators()[32]);
            assert(other_punctuators()[32][0] as u32 == 0x26);
            assert(s[i + 0] == 0x26);
            assert(other_punctuators()[32][1] as u32 == 0x26);
            assert(s[i + 1] == 0x26);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 33 {
            lemma_is_lit(s, i, j, other_punctuators()[33]);
            assert(other_punctuators()[33][0] as u32 == 0x7C);
            assert(s[i + 0] == 0x7C);
            assert(other_punctuators()[33][1] as u32 == 0x7C);
            assert(s[i + 1] == 0x7C);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 34 {
            lemma_is_lit(s, i, j, other_punctuators()[34]);
            assert(other_punctuators()[34][0] as u32 == 0x3F);
            assert(s[i + 0] == 0x3F);
            assert(other_punctuators()[34][1] as u32 == 0x3F);
            assert(s[i + 1] == 0x3F);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 35 {
            lemma_is_lit(s, i, j, other_punctuators()[35]);
            assert(other_punctuators()[35][0] as u32 == 0x3F);
            assert(s[i + 0] == 0x3F);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 36 {
            lemma_is_lit(s, i, j, other_punctuators()[36]);
            assert(other_punctuators()[36][0] as u32 == 0x3A);
            assert(s[i + 0] == 0x3A);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 37 {
            lemma_is_lit(s, i, j, other_punctuators()[37]);
            assert(other_punctuators()[37][0] as u32 == 0x3D);
            assert(s[i + 0] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 38 {
            lemma_is_lit(s, i, j, other_punctuators()[38]);
            assert(other_punctuators()[38][0] as u32 == 0x2B);
            assert(s[i + 0] == 0x2B);
            assert(other_punctuators()[38][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 39 {
            lemma_is_lit(s, i, j, other_punctuators()[39]);
            assert(other_punctuators()[39][0] as u32 == 0x2D);
            assert(s[i + 0] == 0x2D);
            assert(other_punctuators()[39][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 40 {
            lemma_is_lit(s, i, j, other_punctuators()[40]);
            assert(other_punctuators()[40][0] as u32 == 0x2A);
            assert(s[i + 0] == 0x2A);
            assert(other_punctuators()[40][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 41 {
            lemma_is_lit(s, i, j, other_punctuators()[41]);
            assert(other_punctuators()[41][0] as u32 == 0x25);
            assert(s[i + 0] == 0x25);
            assert(other_punctuators()[41][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 42 {
            lemma_is_lit(s, i, j, other_punctuators()[42]);
            assert(other_punctuators()[42][0] as u32 == 0x2A);
            assert(s[i + 0] == 0x2A);
            assert(other_punctuators()[42][1] as u32 == 0x2A);
            assert(s[i + 1] == 0x2A);
            assert(other_punctuators()[42][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 43 {
            lemma_is_lit(s, i, j, other_punctuators()[43]);
            assert(other_punctuators()[43][0] as u32 == 0x3C);
            assert(s[i + 0] == 0x3C);
            assert(other_punctuators()[43][1] as u32 == 0x3C);
            assert(s[i + 1] == 0x3C);
            assert(other_punctuators()[43][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 44 {
            lemma_is_lit(s, i, j, other_punctuators()[44]);
            assert(other_punctuators()[44][0] as u32 == 0x3E);
            assert(s[i + 0] == 0x3E);
            assert(other_punctuators()[44][1] as u32 == 0x3E);
            assert(s[i + 1] == 0x3E);
            assert(other_punctuators()[44][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 45 {
            lemma_is_lit(s, i, j, other_punctuators()[45]);
            assert(other_punctuators()[45][0] as u32 == 0x3E);
            assert(s[i + 0] == 0x3E);
            assert(other_punctuators()[45][1] as u32 == 0x3E);
            assert(s[i + 1] == 0x3E);
            assert(other_punctuators()[45][2] as u32 == 0x3E);
            assert(s[i + 2] == 0x3E);
            assert(other_punctuators()[45][3] as u32 == 0x3D);
            assert(s[i + 3] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 46 {
            lemma_is_lit(s, i, j, other_punctuators()[46]);
            assert(other_punctuators()[46][0] as u32 == 0x26);
            assert(s[i + 0] == 0x26);
            assert(other_punctuators()[46][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 47 {
            lemma_is_lit(s, i, j, other_punctuators()[47]);
            assert(other_punctuators()[47][0] as u32 == 0x7C);
            assert(s[i + 0] == 0x7C);
            assert(other_punctuators()[47][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 48 {
            lemma_is_lit(s, i, j, other_punctuators()[48]);
            assert(other_punctuators()[48][0] as u32 == 0x5E);
            assert(s[i + 0] == 0x5E);
            assert(other_punctuators()[48][1] as u32 == 0x3D);
            assert(s[i + 1] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 49 {
            lemma_is_lit(s, i, j, other_punctuators()[49]);
            assert(other_punctuators()[49][0] as u32 == 0x26);
            assert(s[i + 0] == 0x26);
            assert(other_punctuators()[49][1] as u32 == 0x26);
            assert(s[i + 1] == 0x26);
            assert(other_punctuators()[49][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 50 {
            lemma_is_lit(s, i, j, other_punctuators()[50]);
            assert(other_punctuators()[50][0] as u32 == 0x7C);
            assert(s[i + 0] == 0x7C);
            assert(other_punctuators()[50][1] as u32 == 0x7C);
            assert(s[i + 1] == 0x7C);
            assert(other_punctuators()[50][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 51 {
            lemma_is_lit(s, i, j, other_punctuators()[51]);
            assert(other_punctuators()[51][0] as u32 == 0x3F);
            assert(s[i + 0] == 0x3F);
            assert(other_punctuators()[51][1] as u32 == 0x3F);
            assert(s[i + 1] == 0x3F);
            assert(other_punctuators()[51][2] as u32 == 0x3D);
            assert(s[i + 2] == 0x3D);
            assert(ind_other_punctuator(s, i, j));
        }
        if n == 52 {
            lemma_is_lit(s, i, j, other_punctuators()[52]);
            assert(other_punctuators()[52][0] as u32 == 0x3D);
            assert(s[i + 0] == 0x3D);
            assert(other_punctuators()[52][1] as u32 == 0x3E);
            assert(s[i + 1] == 0x3E);
            assert(ind_other_punctuator(s, i, j));
        }
    }
    // (independent ==> spec): each form is an entry of the list.
    if ind_other_punctuator(s, i, j) {
        if j == i + 1 && s[i + 0] == 0x7B {
            lemma_is_lit(s, i, j, other_punctuators()[0]);
            assert(is_lit(s, i, j, other_punctuators()[0]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x28 {
            lemma_is_lit(s, i, j, other_punctuators()[1]);
            assert(is_lit(s, i, j, other_punctuators()[1]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x29 {
            lemma_is_lit(s, i, j, other_punctuators()[2]);
            assert(is_lit(s, i, j, other_punctuators()[2]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x5B {
            lemma_is_lit(s, i, j, other_punctuators()[3]);
            assert(is_lit(s, i, j, other_punctuators()[3]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x5D {
            lemma_is_lit(s, i, j, other_punctuators()[4]);
            assert(is_lit(s, i, j, other_punctuators()[4]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x2E {
            lemma_is_lit(s, i, j, other_punctuators()[5]);
            assert(is_lit(s, i, j, other_punctuators()[5]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x2E && s[i + 1] == 0x2E && s[i + 2] == 0x2E {
            lemma_is_lit(s, i, j, other_punctuators()[6]);
            assert(is_lit(s, i, j, other_punctuators()[6]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x3B {
            lemma_is_lit(s, i, j, other_punctuators()[7]);
            assert(is_lit(s, i, j, other_punctuators()[7]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x2C {
            lemma_is_lit(s, i, j, other_punctuators()[8]);
            assert(is_lit(s, i, j, other_punctuators()[8]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x3C {
            lemma_is_lit(s, i, j, other_punctuators()[9]);
            assert(is_lit(s, i, j, other_punctuators()[9]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x3E {
            lemma_is_lit(s, i, j, other_punctuators()[10]);
            assert(is_lit(s, i, j, other_punctuators()[10]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3C && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[11]);
            assert(is_lit(s, i, j, other_punctuators()[11]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3E && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[12]);
            assert(is_lit(s, i, j, other_punctuators()[12]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3D && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[13]);
            assert(is_lit(s, i, j, other_punctuators()[13]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x21 && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[14]);
            assert(is_lit(s, i, j, other_punctuators()[14]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x3D && s[i + 1] == 0x3D && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[15]);
            assert(is_lit(s, i, j, other_punctuators()[15]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x21 && s[i + 1] == 0x3D && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[16]);
            assert(is_lit(s, i, j, other_punctuators()[16]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x2B {
            lemma_is_lit(s, i, j, other_punctuators()[17]);
            assert(is_lit(s, i, j, other_punctuators()[17]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x2D {
            lemma_is_lit(s, i, j, other_punctuators()[18]);
            assert(is_lit(s, i, j, other_punctuators()[18]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x2A {
            lemma_is_lit(s, i, j, other_punctuators()[19]);
            assert(is_lit(s, i, j, other_punctuators()[19]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x25 {
            lemma_is_lit(s, i, j, other_punctuators()[20]);
            assert(is_lit(s, i, j, other_punctuators()[20]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x2A && s[i + 1] == 0x2A {
            lemma_is_lit(s, i, j, other_punctuators()[21]);
            assert(is_lit(s, i, j, other_punctuators()[21]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x2B && s[i + 1] == 0x2B {
            lemma_is_lit(s, i, j, other_punctuators()[22]);
            assert(is_lit(s, i, j, other_punctuators()[22]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x2D && s[i + 1] == 0x2D {
            lemma_is_lit(s, i, j, other_punctuators()[23]);
            assert(is_lit(s, i, j, other_punctuators()[23]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3C && s[i + 1] == 0x3C {
            lemma_is_lit(s, i, j, other_punctuators()[24]);
            assert(is_lit(s, i, j, other_punctuators()[24]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3E && s[i + 1] == 0x3E {
            lemma_is_lit(s, i, j, other_punctuators()[25]);
            assert(is_lit(s, i, j, other_punctuators()[25]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x3E && s[i + 1] == 0x3E && s[i + 2] == 0x3E {
            lemma_is_lit(s, i, j, other_punctuators()[26]);
            assert(is_lit(s, i, j, other_punctuators()[26]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x26 {
            lemma_is_lit(s, i, j, other_punctuators()[27]);
            assert(is_lit(s, i, j, other_punctuators()[27]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x7C {
            lemma_is_lit(s, i, j, other_punctuators()[28]);
            assert(is_lit(s, i, j, other_punctuators()[28]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x5E {
            lemma_is_lit(s, i, j, other_punctuators()[29]);
            assert(is_lit(s, i, j, other_punctuators()[29]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x21 {
            lemma_is_lit(s, i, j, other_punctuators()[30]);
            assert(is_lit(s, i, j, other_punctuators()[30]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x7E {
            lemma_is_lit(s, i, j, other_punctuators()[31]);
            assert(is_lit(s, i, j, other_punctuators()[31]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x26 && s[i + 1] == 0x26 {
            lemma_is_lit(s, i, j, other_punctuators()[32]);
            assert(is_lit(s, i, j, other_punctuators()[32]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x7C && s[i + 1] == 0x7C {
            lemma_is_lit(s, i, j, other_punctuators()[33]);
            assert(is_lit(s, i, j, other_punctuators()[33]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3F && s[i + 1] == 0x3F {
            lemma_is_lit(s, i, j, other_punctuators()[34]);
            assert(is_lit(s, i, j, other_punctuators()[34]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x3F {
            lemma_is_lit(s, i, j, other_punctuators()[35]);
            assert(is_lit(s, i, j, other_punctuators()[35]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x3A {
            lemma_is_lit(s, i, j, other_punctuators()[36]);
            assert(is_lit(s, i, j, other_punctuators()[36]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 1 && s[i + 0] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[37]);
            assert(is_lit(s, i, j, other_punctuators()[37]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x2B && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[38]);
            assert(is_lit(s, i, j, other_punctuators()[38]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x2D && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[39]);
            assert(is_lit(s, i, j, other_punctuators()[39]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x2A && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[40]);
            assert(is_lit(s, i, j, other_punctuators()[40]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x25 && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[41]);
            assert(is_lit(s, i, j, other_punctuators()[41]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x2A && s[i + 1] == 0x2A && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[42]);
            assert(is_lit(s, i, j, other_punctuators()[42]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x3C && s[i + 1] == 0x3C && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[43]);
            assert(is_lit(s, i, j, other_punctuators()[43]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x3E && s[i + 1] == 0x3E && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[44]);
            assert(is_lit(s, i, j, other_punctuators()[44]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 4 && s[i + 0] == 0x3E && s[i + 1] == 0x3E && s[i + 2] == 0x3E && s[i + 3] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[45]);
            assert(is_lit(s, i, j, other_punctuators()[45]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x26 && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[46]);
            assert(is_lit(s, i, j, other_punctuators()[46]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x7C && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[47]);
            assert(is_lit(s, i, j, other_punctuators()[47]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x5E && s[i + 1] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[48]);
            assert(is_lit(s, i, j, other_punctuators()[48]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x26 && s[i + 1] == 0x26 && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[49]);
            assert(is_lit(s, i, j, other_punctuators()[49]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x7C && s[i + 1] == 0x7C && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[50]);
            assert(is_lit(s, i, j, other_punctuators()[50]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 3 && s[i + 0] == 0x3F && s[i + 1] == 0x3F && s[i + 2] == 0x3D {
            lemma_is_lit(s, i, j, other_punctuators()[51]);
            assert(is_lit(s, i, j, other_punctuators()[51]));
            assert(other_punctuator(s, i, j));
        } else if j == i + 2 && s[i + 0] == 0x3D && s[i + 1] == 0x3E {
            lemma_is_lit(s, i, j, other_punctuators()[52]);
            assert(is_lit(s, i, j, other_punctuators()[52]));
            assert(other_punctuator(s, i, j));
        } else {
            assert(false);
        }
    }
}

/// `OptionalChainingPunctuator` (§12.8), with its lookahead.
pub proof fn lemma_optional_chaining_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        optional_chaining_punctuator(s, i, j) <==> ind_optional_chaining(s, i, j),
{
    lemma_is_lit(s, i, j, seq!['?', '.']);
}

/// `DivPunctuator` (§12.8).
pub proof fn lemma_div_punctuator_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        div_punctuator(s, i, j) <==> ind_div_punctuator(s, i, j),
{
    lemma_is_lit(s, i, j, seq!['/']);
    lemma_is_lit(s, i, j, seq!['/', '=']);
    assert(seq!['/'][0] as u32 == 0x2F);
    assert(seq!['/', '='][0] as u32 == 0x2F);
    assert(seq!['/', '='][1] as u32 == 0x3D);
}

/// `RightBracePunctuator` (§12.8).
pub proof fn lemma_right_brace_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        right_brace_punctuator(s, i, j) <==> ind_right_brace(s, i, j),
{
    lemma_is_lit(s, i, j, seq!['}']);
    assert(seq!['}'][0] as u32 == 0x7D);
}

/// The two ways of writing "the code points of an ASCII word" agree.
pub proof fn lemma_word_equiv(w: Seq<char>)
    ensures
        word(w) =~= ind_word(w),
{
}

/// The two lists of reserved words are the same sequence of words.
pub proof fn lemma_reserved_words_equiv()
    ensures
        reserved_words() =~~= ind_reserved_words(),
{
}

/// `ReservedWord` (§12.7.2): a name written without escapes is reserved
/// exactly when its code points spell one of the words.
pub proof fn lemma_reserved_word_equiv(cps: Seq<u32>)
    ensures
        is_reserved_word(cps, false) <==> ind_is_reserved(cps),
{
    lemma_reserved_words_equiv();
    assert(reserved_words() == ind_reserved_words());
    assert forall|n: int| 0 <= n < reserved_words().len() implies word(
        #[trigger] reserved_words()[n],
    ) =~= ind_word(reserved_words()[n]) by {
        lemma_word_equiv(reserved_words()[n]);
    }
}

// ---------------------------------------------------------------------
// Identifier names.
// ---------------------------------------------------------------------

/// A `UnicodeEscapeSequence` that the deterministic reading finds lies
/// inside the source text and is not empty.
pub proof fn lemma_escape_end_bounds(s: Seq<u32>, k: int)
    requires
        0 <= k,
        ind_escape_end(s, k) >= 0,
    ensures
        k < ind_escape_end(s, k) <= s.len(),
{
    if k < s.len() && s[k] == 0x75 {
        lemma_hex_run_end(s, k + 1) ;
        if k + 1 < s.len() && s[k + 1] == 0x7B {
            lemma_hex_run_end(s, k + 2);
        }
    }
}

/// A unit that the left-to-right reading finds lies inside the source text.
pub proof fn lemma_unit_end_bounds(s: Seq<u32>, k: int, start: bool)
    requires
        ind_unit_end(s, k, start) >= 0,
    ensures
        0 <= k < s.len(),
        k < ind_unit_end(s, k, start) <= s.len(),
{
    if 0 <= k < s.len() && s[k] == 0x5C {
        lemma_escape_end_bounds(s, k + 1);
    }
}

/// `IdentifierStartChar` and `IdentifierPartChar` are UAX #31's `Start` and
/// `Continue`.
pub proof fn lemma_id_char_equiv(c: u32)
    ensures
        is_identifier_start_char(c) <==> ind_id_start(c),
        is_identifier_part_char(c) <==> ind_id_continue(c),
{
}

/// `IdentifierStart` and `IdentifierPart` over `s[k..e)` are the one unit the
/// left-to-right reading finds at `k`, for the class selected by `start`.
pub proof fn lemma_unit_equiv(s: Seq<u32>, k: int, e: int)
    ensures
        identifier_start(s, k, e) <==> (0 <= k && k < e && e <= s.len() && ind_unit_end(
            s,
            k,
            true,
        ) == e),
        identifier_part(s, k, e) <==> (0 <= k && k < e && e <= s.len() && ind_unit_end(
            s,
            k,
            false,
        ) == e),
{
    lemma_unicode_escape_equiv(s, k + 1, e);
    if 0 <= k && k < s.len() && s[k] == 0x5C {
        if ind_escape_end(s, k + 1) >= 0 {
            lemma_escape_end_bounds(s, k + 1);
        }
    }
    if 0 <= k {
        lemma_id_char_equiv(s[k]);
    }
}

/// Appending one `Continue` unit to a name read left to right.
pub proof fn lemma_name_from_append(s: Seq<u32>, i: int, k: int, j: int, first: bool)
    requires
        ind_name_from(s, i, k, first),
        k < j,
        ind_unit_end(s, k, false) == j,
    ensures
        ind_name_from(s, i, j, first),
    decreases k - i,
{
    if i < k {
        let e = ind_unit_end(s, i, first);
        assert(i < e && e <= k && ind_name_from(s, e, k, false));
        lemma_name_from_append(s, e, k, j, false);
        assert(ind_name_from(s, e, j, false));
        assert(i < e && e <= j);
    } else {
        assert(i == k && !first);
        assert(ind_name_from(s, j, j, false));
    }
}

/// Extending an `IdentifierName` by an `IdentifierPart` (§12.7 alternative
/// 2).
pub proof fn lemma_name_extend(s: Seq<u32>, i: int, m: int, m2: int)
    requires
        identifier_name(s, i, m),
        identifier_part(s, m, m2),
    ensures
        identifier_name(s, i, m2),
{
    let cps = choose|cps: Seq<u32>| identifier_name_cps(s, i, m, cps);
    let ext = cps.push(identifier_code_point(s, m, m2));
    assert(ext.drop_last() =~= cps);
    assert(identifier_name_cps(s, i, m2, ext)) by {
        assert(ext.len() >= 2);
        assert(i < m < m2);
        assert(identifier_name_cps(s, i, m, ext.drop_last()));
        assert(ext.last() == identifier_code_point(s, m, m2));
    }
}

/// An `IdentifierName` on `[i, m)` followed by parts read left to right up
/// to `j` is an `IdentifierName` on `[i, j)`.
pub proof fn lemma_name_then_parts(s: Seq<u32>, i: int, m: int, j: int)
    requires
        identifier_name(s, i, m),
        ind_name_from(s, m, j, false),
    ensures
        identifier_name(s, i, j),
    decreases j - m,
{
    if m < j {
        let e = ind_unit_end(s, m, false);
        assert(m < e && e <= j && ind_name_from(s, e, j, false));
        lemma_unit_end_bounds(s, m, false);
        lemma_unit_equiv(s, m, e);
        lemma_name_extend(s, i, m, e);
        lemma_name_then_parts(s, i, e, j);
    }
}

/// Every derivation of `IdentifierName` is a start unit and then parts, as
/// the left-to-right reading has it.
pub proof fn lemma_name_cps_to_ind(s: Seq<u32>, i: int, j: int, cps: Seq<u32>)
    requires
        identifier_name_cps(s, i, j, cps),
    ensures
        ind_name_from(s, i, j, true),
    decreases j - i,
{
    lemma_unit_equiv(s, i, j);
    if identifier_start(s, i, j) && cps =~= seq![identifier_code_point(s, i, j)] {
        assert(ind_unit_end(s, i, true) == j);
        assert(ind_name_from(s, j, j, false));
    } else {
        assert(cps.len() >= 2 && exists|k: int| #![auto]
            i < k < j && identifier_name_cps(s, i, k, cps.drop_last()) && identifier_part(s, k, j)
                && cps.last() == identifier_code_point(s, k, j));
        let k = choose|k: int| #![auto]
            i < k < j && identifier_name_cps(s, i, k, cps.drop_last()) && identifier_part(s, k, j)
                && cps.last() == identifier_code_point(s, k, j);
        lemma_name_cps_to_ind(s, i, k, cps.drop_last());
        lemma_unit_equiv(s, k, j);
        lemma_name_from_append(s, i, k, j, true);
    }
}

/// `IdentifierName` (§12.7) is UAX #31's `<Start> <Continue>*`, with an
/// escape standing for a code point.
pub proof fn lemma_identifier_name_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        identifier_name(s, i, j) <==> ind_identifier_name(s, i, j),
{
    if identifier_name(s, i, j) {
        let cps = choose|cps: Seq<u32>| identifier_name_cps(s, i, j, cps);
        assert(0 <= i);
        lemma_name_cps_to_ind(s, i, j, cps);
    }
    if ind_identifier_name(s, i, j) {
        let e = ind_unit_end(s, i, true);
        assert(i < e && e <= j && ind_name_from(s, e, j, false));
        lemma_unit_end_bounds(s, i, true);
        lemma_unit_equiv(s, i, e);
        assert(identifier_start(s, i, e));
        assert(identifier_name_cps(s, i, e, seq![identifier_code_point(s, i, e)]));
        assert(identifier_name(s, i, e));
        lemma_name_then_parts(s, i, e, j);
    }
}

/// `PrivateIdentifier` (§12.7).
pub proof fn lemma_private_identifier_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        private_identifier(s, i, j) <==> ind_private_identifier(s, i, j),
{
    lemma_identifier_name_equiv(s, i + 1, j);
}

} // verus!
