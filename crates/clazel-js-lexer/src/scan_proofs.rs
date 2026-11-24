//! Lemmas about [`super::independent`]'s closed forms that the proofs of
//! [`super::exec`]'s scanners use: a greedy scan of a digit run, an exponent
//! or a decimal tail ends exactly where the longest derivation ends.
//!
//! They state nothing about the spec on their own; `exec.rs` connects them
//! to it through [`super::equivalence`].

#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Digit runs with separators.
// ---------------------------------------------------------------------

/// A single digit is a run.
pub proof fn lemma_sep_base(radix: int, s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        ind_radix_digit(radix, s[k]),
    ensures
        ind_sep_digits(radix, s, k, k + 1),
{
}

/// A run followed by a digit is a longer run.
pub proof fn lemma_sep_extend1(radix: int, s: Seq<u32>, k: int, j: int)
    requires
        0 <= k < j < s.len(),
        ind_sep_digits(radix, s, k, j),
        ind_radix_digit(radix, s[j]),
    ensures
        ind_sep_digits(radix, s, k, j + 1),
{
    assert forall|t: int| k <= t < j + 1 implies (ind_radix_digit(radix, #[trigger] s[t]) || s[t]
        == 0x5F) by {
        if t < j {
            assert(ind_radix_digit(radix, s[t]) || s[t] == 0x5F);
        }
    }
    assert forall|t: int| k <= t < j implies !(#[trigger] s[t] == 0x5F && s[t + 1] == 0x5F) by {
        if t < j - 1 {
            assert(!(s[t] == 0x5F && s[t + 1] == 0x5F));
        } else {
            assert(ind_radix_digit(radix, s[j - 1]));
        }
    }
}

/// A run followed by `_` and a digit is a longer run.
pub proof fn lemma_sep_extend2(radix: int, s: Seq<u32>, k: int, j: int)
    requires
        0 <= k < j,
        j + 1 < s.len(),
        ind_sep_digits(radix, s, k, j),
        s[j] == 0x5F,
        ind_radix_digit(radix, s[j + 1]),
    ensures
        ind_sep_digits(radix, s, k, j + 2),
{
    assert forall|t: int| k <= t < j + 2 implies (ind_radix_digit(radix, #[trigger] s[t]) || s[t]
        == 0x5F) by {
        if t < j {
            assert(ind_radix_digit(radix, s[t]) || s[t] == 0x5F);
        }
    }
    assert forall|t: int| k <= t < j + 1 implies !(#[trigger] s[t] == 0x5F && s[t + 1] == 0x5F) by {
        if t < j - 1 {
            assert(!(s[t] == 0x5F && s[t + 1] == 0x5F));
        } else if t == j - 1 {
            assert(ind_radix_digit(radix, s[j - 1]));
        }
    }
}

/// A run that no digit and no `_` digit continues is the longest.
pub proof fn lemma_sep_maximal(radix: int, s: Seq<u32>, k: int, e: int)
    requires
        0 <= k < e <= s.len(),
        ind_sep_digits(radix, s, k, e),
        !(e < s.len() && ind_radix_digit(radix, s[e])),
        !(e + 1 < s.len() && s[e] == 0x5F && ind_radix_digit(radix, s[e + 1])),
    ensures
        forall|j: int| j > e ==> !ind_sep_digits(radix, s, k, j),
{
    assert forall|j: int| j > e implies !ind_sep_digits(radix, s, k, j) by {
        if ind_sep_digits(radix, s, k, j) {
            assert(ind_radix_digit(radix, s[e]) || s[e] == 0x5F);
            if s[e] == 0x5F {
                assert(e < j - 1) by {
                    assert(ind_radix_digit(radix, s[j - 1]));
                }
                assert(ind_radix_digit(radix, s[e + 1]) || s[e + 1] == 0x5F);
                assert(!(s[e] == 0x5F && s[e + 1] == 0x5F));
            }
        }
    }
}

/// Every code point of a run is a digit or `_`.
pub proof fn lemma_sep_chars(radix: int, s: Seq<u32>, k: int, e: int, t: int)
    requires
        ind_sep_digits(radix, s, k, e),
        k <= t < e,
    ensures
        ind_radix_digit(radix, s[t]) || s[t] == 0x5F,
{
}

// ---------------------------------------------------------------------
// The tail of a decimal literal.
// ---------------------------------------------------------------------

/// The `.` at `a`, the optional digits on `[a + 1, b)` and the optional
/// exponent on `[b, j)`.
pub open spec fn ind_dl_tail_mid(s: Seq<u32>, a: int, b: int, j: int) -> bool {
    a + 1 <= b <= j && (b == a + 1 || ind_sep_digits(10, s, a + 1, b)) && (b == j || ind_exponent(
        s,
        b,
        j,
    ))
}

/// What can follow a `DecimalIntegerLiteral` that ends at `a` in a
/// `DecimalLiteral` that ends at `j`: nothing, an exponent, or `.` with
/// optional digits and an optional exponent.
pub open spec fn ind_tail(s: Seq<u32>, a: int, j: int) -> bool {
    j == a || ind_exponent(s, a, j) || (0 <= a < s.len() && s[a] == 0x2E && exists|b: int|
        #![trigger ind_dl_tail_mid(s, a, b, j)]
        ind_dl_tail_mid(s, a, b, j))
}

// A decimal literal is an integer part and a tail.

/// `DecimalLiteral`: `.` and digits (and an exponent), or an integer part
/// that a tail follows.
pub proof fn lemma_decimal_literal_tail(s: Seq<u32>, i: int, j: int)
    ensures
        ind_decimal_literal(s, i, j) <==> ((exists|b: int| #[trigger] ind_dl_alt2(s, i, j, b))
            || (exists|a: int| #![trigger ind_decimal_integer(s, i, a)]
            i < a && ind_decimal_integer(s, i, a) && ind_tail(s, a, j))),
{
    if ind_decimal_literal(s, i, j) {
        if exists|a: int, b: int| #[trigger] ind_dl_alt1(s, i, j, a, b) {
            let (a, b) = choose|a: int, b: int| #[trigger] ind_dl_alt1(s, i, j, a, b);
            assert(ind_dl_tail_mid(s, a, b, j));
            assert(ind_tail(s, a, j));
        } else if exists|a: int| #[trigger] ind_dl_alt3(s, i, j, a) {
            let a = choose|a: int| #[trigger] ind_dl_alt3(s, i, j, a);
            assert(ind_tail(s, a, j));
        }
    }
    if exists|a: int| #![trigger ind_decimal_integer(s, i, a)]
        i < a && ind_decimal_integer(s, i, a) && ind_tail(s, a, j) {
        let a = choose|a: int| #![trigger ind_decimal_integer(s, i, a)]
            i < a && ind_decimal_integer(s, i, a) && ind_tail(s, a, j);
        if j == a || ind_exponent(s, a, j) {
            assert(ind_dl_alt3(s, i, j, a));
        } else {
            let b = choose|b: int| #[trigger] ind_dl_tail_mid(s, a, b, j);
            assert(ind_dl_alt1(s, i, j, a, b));
        }
    }
}

/// A tail that is not empty ends with a digit or `.`.
pub proof fn lemma_tail_last(s: Seq<u32>, a: int, j: int)
    requires
        ind_tail(s, a, j),
        j > a,
    ensures
        0 < j <= s.len(),
        ind_dec(s[j - 1]) || s[j - 1] == 0x2E,
{
    if ind_exponent(s, a, j) {
        assert(ind_sep_digits(10, s, a + 1, j) || ind_sep_digits(10, s, a + 2, j));
    } else {
        let b = choose|b: int| #[trigger] ind_dl_tail_mid(s, a, b, j);
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

/// A tail does not begin with a code point that is a digit, `_` or `n`
/// unless it is empty: its first code point is `e`, `E` or `.`.
pub proof fn lemma_tail_first(s: Seq<u32>, a: int, j: int)
    requires
        ind_tail(s, a, j),
        j > a,
    ensures
        0 <= a < s.len(),
        s[a] == 0x65 || s[a] == 0x45 || s[a] == 0x2E,
{
    if !ind_exponent(s, a, j) {
        let b = choose|b: int| #[trigger] ind_dl_tail_mid(s, a, b, j);
    }
}

/// Whether the digits of `s[k..e)` hold a `_` or a digit only: a run's
/// chars are not `n`, `e`, `E` or `.`.
pub open spec fn not_tail_start(c: u32) -> bool {
    c != 0x65 && c != 0x45 && c != 0x2E
}

/// A run of digits and `_` has no tail start in it.
pub proof fn lemma_run_not_tail_start(s: Seq<u32>, k: int, e: int, t: int)
    requires
        ind_sep_digits(10, s, k, e),
        k <= t < e,
    ensures
        not_tail_start(s[t]),
        s[t] != 0x6E,
{
}

// ---------------------------------------------------------------------
// The integer part of a decimal literal.
// ---------------------------------------------------------------------

/// A `0` and no digit: the integer part is the `0`.
pub proof fn lemma_int_zero_alone(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        s[k] == 0x30,
        !(k + 1 < s.len() && ind_dec(s[k + 1])),
    ensures
        forall|a: int| ind_decimal_integer(s, k, a) <==> a == k + 1,
{
    assert forall|a: int| ind_decimal_integer(s, k, a) <==> a == k + 1 by {
        if ind_decimal_integer(s, k, a) && a != k + 1 {
            assert(ind_non_octal_decimal_integer(s, k, a));
            assert(ind_dec(s[k + 1]));
        }
    }
}

/// A `0` and a digit.
pub proof fn lemma_int_zero_digit(s: Seq<u32>, k: int)
    requires
        0 <= k,
        k + 1 < s.len(),
        s[k] == 0x30,
        ind_dec(s[k + 1]),
    ensures
        forall|a: int|
            ind_decimal_integer(s, k, a) <==> (a == k + 1 || ind_non_octal_decimal_integer(s, k, a)),
{
}

/// A non-zero digit: the integer part is a run.
pub proof fn lemma_int_nonzero(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        ind_dec(s[k]),
        s[k] != 0x30,
    ensures
        forall|a: int| ind_decimal_integer(s, k, a) <==> ind_sep_digits(10, s, k, a),
{
}

// ---------------------------------------------------------------------
// The flags of a numeric literal, and its shapes by first code points.
// ---------------------------------------------------------------------

/// The `NumericLiteral` over `s[i..j)` is a BigInt literal, in the closed
/// forms.
pub open spec fn ind_is_bigint(s: Seq<u32>, i: int, j: int) -> bool {
    ind_decimal_bigint(s, i, j) || (i + 1 < j && ind_bigint_suffix(s, j - 1)
        && ind_non_decimal_integer(s, i, j - 1))
}

/// The `NumericLiteral` over `s[i..j)` is a legacy one, in the closed forms.
pub open spec fn ind_is_legacy(s: Seq<u32>, i: int, j: int) -> bool {
    ind_legacy_octal(s, i, j) || (ind_decimal_literal(s, i, j) && exists|k: int|
        #![trigger ind_non_octal_decimal_integer(s, i, k)]
        i < k <= j && ind_non_octal_decimal_integer(s, i, k))
}

/// `0` and a prefix letter and a digit of its radix start `s[k..]`.
pub open spec fn prefix_digit(s: Seq<u32>, k: int) -> bool {
    k + 2 < s.len() && s[k] == 0x30 && (((s[k + 1] == 0x62 || s[k + 1] == 0x42) && ind_bin(
        s[k + 2],
    )) || ((s[k + 1] == 0x6F || s[k + 1] == 0x4F) && ind_oct(s[k + 2])) || ((s[k + 1] == 0x78
        || s[k + 1] == 0x58) && ind_hex(s[k + 2])))
}

/// A `.` and a digit: only the second shape of `DecimalLiteral` applies.
pub proof fn lemma_shape_dot(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        s[k] == 0x2E,
    ensures
        forall|j: int|
            ind_numeric_literal(s, k, j) ==> exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b),
        forall|j: int| !ind_is_bigint(s, k, j),
        forall|j: int| !ind_is_legacy(s, k, j),
{
    assert forall|j: int| ind_numeric_literal(s, k, j) implies exists|b: int|
        #[trigger] ind_dl_alt2(s, k, j, b) by {
        lemma_decimal_literal_tail(s, k, j);
        if ind_decimal_literal(s, k, j) {
            if !(exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b)) {
                let a = choose|a: int| #![trigger ind_decimal_integer(s, k, a)]
                    k < a && ind_decimal_integer(s, k, a) && ind_tail(s, a, j);
                assert(false);
            }
        }
    }
    assert forall|j: int| !ind_is_legacy(s, k, j) by {
        assert(!ind_legacy_octal(s, k, j));
        if exists|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
            k < kk <= j && ind_non_octal_decimal_integer(s, k, kk) {
            let kk = choose|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
                k < kk <= j && ind_non_octal_decimal_integer(s, k, kk);
            assert(false);
        }
    }
}

/// A `0` and nothing that makes it a longer literal: the literal is the `0`
/// and a tail.
pub proof fn lemma_shape_zero_alone(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        s[k] == 0x30,
        !(k + 1 < s.len() && ind_dec(s[k + 1])),
        !(k + 1 < s.len() && s[k + 1] == 0x6E),
        !prefix_digit(s, k),
    ensures
        forall|j: int| ind_numeric_literal(s, k, j) <==> ind_tail(s, k + 1, j),
        forall|j: int| !ind_is_bigint(s, k, j),
        forall|j: int| !ind_is_legacy(s, k, j),
{
    lemma_int_zero_alone(s, k);
    assert forall|j: int| ind_numeric_literal(s, k, j) <==> ind_tail(s, k + 1, j) by {
        lemma_decimal_literal_tail(s, k, j);
        if ind_tail(s, k + 1, j) {
            assert(ind_decimal_integer(s, k, k + 1));
        }
        if ind_numeric_literal(s, k, j) {
            if ind_decimal_literal(s, k, j) {
                if !(exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b)) {
                    let a = choose|a: int| #![trigger ind_decimal_integer(s, k, a)]
                        k < a && ind_decimal_integer(s, k, a) && ind_tail(s, a, j);
                    assert(a == k + 1);
                }
            }
        }
    }
    assert forall|j: int| !ind_is_bigint(s, k, j) by {
        if ind_is_bigint(s, k, j) {
            assert(false);
        }
    }
    assert forall|j: int| !ind_is_legacy(s, k, j) by {
        if exists|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
            k < kk <= j && ind_non_octal_decimal_integer(s, k, kk) {
            let kk = choose|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
                k < kk <= j && ind_non_octal_decimal_integer(s, k, kk);
            assert(false);
        }
    }
}

/// `0n`.
pub proof fn lemma_shape_zero_n(s: Seq<u32>, k: int)
    requires
        0 <= k,
        k + 1 < s.len(),
        s[k] == 0x30,
        s[k + 1] == 0x6E,
    ensures
        forall|j: int| ind_numeric_literal(s, k, j) <==> (j == k + 1 || j == k + 2),
        ind_is_bigint(s, k, k + 2),
        forall|j: int| !ind_is_legacy(s, k, j),
{
    lemma_int_zero_alone(s, k);
    assert forall|j: int| ind_numeric_literal(s, k, j) <==> (j == k + 1 || j == k + 2) by {
        lemma_decimal_literal_tail(s, k, j);
        if j == k + 1 {
            assert(ind_tail(s, k + 1, j));
            assert(ind_decimal_integer(s, k, k + 1));
        }
        if ind_numeric_literal(s, k, j) {
            if ind_decimal_literal(s, k, j) {
                if !(exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b)) {
                    let a = choose|a: int| #![trigger ind_decimal_integer(s, k, a)]
                        k < a && ind_decimal_integer(s, k, a) && ind_tail(s, a, j);
                    assert(a == k + 1);
                    if j > a {
                        lemma_tail_first(s, a, j);
                    }
                }
            }
        }
    }
    assert forall|j: int| !ind_is_legacy(s, k, j) by {
        if exists|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
            k < kk <= j && ind_non_octal_decimal_integer(s, k, kk) {
            let kk = choose|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
                k < kk <= j && ind_non_octal_decimal_integer(s, k, kk);
            assert(false);
        }
    }
}

/// A `0` and a prefix letter, and a digit of its radix: a literal is the
/// `0`, or the digits (and a `BigIntLiteralSuffix`).
pub proof fn lemma_shape_prefix(s: Seq<u32>, k: int, radix: int)
    requires
        0 <= k,
        prefix_digit(s, k),
        radix == 2 || radix == 8 || radix == 16,
        radix == 2 ==> (s[k + 1] == 0x62 || s[k + 1] == 0x42),
        radix == 8 ==> (s[k + 1] == 0x6F || s[k + 1] == 0x4F),
        radix == 16 ==> (s[k + 1] == 0x78 || s[k + 1] == 0x58),
    ensures
        forall|j: int|
            ind_numeric_literal(s, k, j) ==> (j == k + 1 || ind_sep_digits(radix, s, k + 2, j) || (
            j > k + 3 && s[j - 1] == 0x6E && ind_sep_digits(radix, s, k + 2, j - 1))),
        forall|j: int| ind_sep_digits(radix, s, k + 2, j) ==> (ind_numeric_literal(s, k, j)
            && !ind_is_bigint(s, k, j)),
        forall|j: int|
            (j > k + 2 && j <= s.len() && s[j - 1] == 0x6E && ind_sep_digits(radix, s, k + 2, j - 1))
                ==> (ind_numeric_literal(s, k, j) && ind_is_bigint(s, k, j)),
        forall|j: int| !ind_is_legacy(s, k, j),
{
    lemma_int_zero_alone(s, k);
    assert forall|j: int| ind_numeric_literal(s, k, j) implies (j == k + 1 || ind_sep_digits(
        radix,
        s,
        k + 2,
        j,
    ) || (j > k + 3 && s[j - 1] == 0x6E && ind_sep_digits(radix, s, k + 2, j - 1))) by {
        lemma_decimal_literal_tail(s, k, j);
        if ind_decimal_literal(s, k, j) {
            if !(exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b)) {
                let a = choose|a: int| #![trigger ind_decimal_integer(s, k, a)]
                    k < a && ind_decimal_integer(s, k, a) && ind_tail(s, a, j);
                assert(a == k + 1);
                if j > a {
                    lemma_tail_first(s, a, j);
                }
            }
        }
    }
    assert forall|j: int| !ind_is_legacy(s, k, j) by {
        if exists|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
            k < kk <= j && ind_non_octal_decimal_integer(s, k, kk) {
            let kk = choose|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
                k < kk <= j && ind_non_octal_decimal_integer(s, k, kk);
            assert(false);
        }
    }
    assert forall|j: int| ind_sep_digits(radix, s, k + 2, j) implies (ind_numeric_literal(s, k, j)
        && !ind_is_bigint(s, k, j)) by {
        assert(ind_non_decimal_integer(s, k, j));
        if ind_is_bigint(s, k, j) {
            assert(false);
        }
    }
    assert forall|j: int|
        (j > k + 2 && j <= s.len() && s[j - 1] == 0x6E && ind_sep_digits(radix, s, k + 2, j - 1))
            implies (
    ind_numeric_literal(s, k, j) && ind_is_bigint(s, k, j)) by {
        assert(ind_non_decimal_integer(s, k, j - 1));
    }
}

/// A `0` and a decimal digit.
pub proof fn lemma_shape_zero_digit(s: Seq<u32>, k: int)
    requires
        0 <= k,
        k + 1 < s.len(),
        s[k] == 0x30,
        ind_dec(s[k + 1]),
    ensures
        forall|j: int|
            ind_numeric_literal(s, k, j) ==> (j == k + 1 || ind_legacy_octal(s, k, j) || (exists|
                a: int,
            |
                #![trigger ind_non_octal_decimal_integer(s, k, a)]
                ind_non_octal_decimal_integer(s, k, a) && ind_tail(s, a, j))),
        forall|j: int| !ind_is_bigint(s, k, j),
        forall|j: int| ind_legacy_octal(s, k, j) ==> (ind_numeric_literal(s, k, j) && ind_is_legacy(
            s,
            k,
            j,
        )),
        forall|a: int, j: int|
            (ind_non_octal_decimal_integer(s, k, a) && ind_tail(s, a, j)) ==> (
            ind_numeric_literal(s, k, j) && ind_is_legacy(s, k, j)),
{
    lemma_int_zero_digit(s, k);
    assert forall|j: int| ind_numeric_literal(s, k, j) implies (j == k + 1 || ind_legacy_octal(
        s,
        k,
        j,
    ) || (exists|a: int| #![trigger ind_non_octal_decimal_integer(s, k, a)]
        ind_non_octal_decimal_integer(s, k, a) && ind_tail(s, a, j))) by {
        lemma_decimal_literal_tail(s, k, j);
        if ind_decimal_literal(s, k, j) {
            if !(exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b)) {
                let a = choose|a: int| #![trigger ind_decimal_integer(s, k, a)]
                    k < a && ind_decimal_integer(s, k, a) && ind_tail(s, a, j);
                if a == k + 1 {
                    if j > a {
                        lemma_tail_first(s, a, j);
                    }
                } else {
                    assert(ind_non_octal_decimal_integer(s, k, a));
                }
            }
        }
    }
    assert forall|j: int| !ind_is_bigint(s, k, j) by {
        if ind_is_bigint(s, k, j) {
            assert(false);
        }
    }
    assert forall|a: int, j: int|
        (ind_non_octal_decimal_integer(s, k, a) && ind_tail(s, a, j)) implies (
    ind_numeric_literal(s, k, j) && ind_is_legacy(s, k, j)) by {
        if ind_non_octal_decimal_integer(s, k, a) && ind_tail(s, a, j) {
            assert(ind_decimal_integer(s, k, a));
            lemma_decimal_literal_tail(s, k, j);
            assert(ind_decimal_literal(s, k, j));
            assert(ind_non_octal_decimal_integer(s, k, a));
        }
    }
}

/// A non-zero digit.
pub proof fn lemma_shape_nonzero(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        ind_dec(s[k]),
        s[k] != 0x30,
    ensures
        forall|j: int|
            ind_numeric_literal(s, k, j) ==> ((j > k + 1 && s[j - 1] == 0x6E && ind_sep_digits(
                10,
                s,
                k,
                j - 1,
            )) || (exists|a: int| #![trigger ind_sep_digits(10, s, k, a)]
                ind_sep_digits(10, s, k, a) && ind_tail(s, a, j))),
        forall|j: int| !ind_is_legacy(s, k, j),
        forall|e: int|
            (ind_sep_digits(10, s, k, e) && e < s.len() && s[e] == 0x6E) ==> (ind_numeric_literal(
                s,
                k,
                e + 1,
            ) && ind_is_bigint(s, k, e + 1)),
        forall|e: int, j: int|
            (ind_sep_digits(10, s, k, e) && ind_tail(s, e, j)) ==> (ind_numeric_literal(s, k, j)
                && !ind_is_bigint(s, k, j)),
{
    lemma_int_nonzero(s, k);
    assert forall|j: int| ind_numeric_literal(s, k, j) implies ((j > k + 1 && s[j - 1] == 0x6E
        && ind_sep_digits(10, s, k, j - 1)) || (exists|a: int|
        #![trigger ind_sep_digits(10, s, k, a)]
        ind_sep_digits(10, s, k, a) && ind_tail(s, a, j))) by {
        lemma_decimal_literal_tail(s, k, j);
        if ind_decimal_literal(s, k, j) {
            if !(exists|b: int| #[trigger] ind_dl_alt2(s, k, j, b)) {
                let a = choose|a: int| #![trigger ind_decimal_integer(s, k, a)]
                    k < a && ind_decimal_integer(s, k, a) && ind_tail(s, a, j);
                assert(ind_sep_digits(10, s, k, a));
            } else {
                assert(false);
            }
        }
    }
    assert forall|j: int| !ind_is_legacy(s, k, j) by {
        if exists|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
            k < kk <= j && ind_non_octal_decimal_integer(s, k, kk) {
            let kk = choose|kk: int| #![trigger ind_non_octal_decimal_integer(s, k, kk)]
                k < kk <= j && ind_non_octal_decimal_integer(s, k, kk);
            assert(false);
        }
    }
    assert forall|e: int, j: int| (ind_sep_digits(10, s, k, e) && ind_tail(s, e, j)) implies (
    ind_numeric_literal(s, k, j) && !ind_is_bigint(s, k, j)) by {
        if ind_sep_digits(10, s, k, e) && ind_tail(s, e, j) {
            assert(ind_decimal_integer(s, k, e));
            lemma_decimal_literal_tail(s, k, j);
            assert(ind_decimal_literal(s, k, j));
            if j > e {
                lemma_tail_last(s, e, j);
            }
            if ind_is_bigint(s, k, j) {
                assert(false);
            }
        }
    }
}

/// The code points `s[a..b)` are all decimal digits.
pub open spec fn all_dec(s: Seq<u32>, a: int, b: int) -> bool {
    forall|t: int| a <= t < b ==> ind_dec(#[trigger] s[t])
}

/// The flags of a numeric literal in the spec are the closed forms'.
pub proof fn lemma_flags_equiv(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i,
        j <= s.len(),
    ensures
        numeric_literal_is_bigint(s, i, j) <==> ind_is_bigint(s, i, j),
        numeric_literal_is_legacy(s, i, j) <==> ind_is_legacy(s, i, j),
{
    lemma_decimal_bigint_equiv(s, i, j);
    lemma_legacy_octal_equiv(s, i, j);
    lemma_decimal_literal_equiv(s, i, j);
    if i + 1 < j {
        lemma_non_decimal_equiv(s, i, j - 1);
    }
    if numeric_literal_is_legacy(s, i, j) && !legacy_octal_integer_literal(s, i, j) {
        let kk = choose|kk: int| i < kk <= j && non_octal_decimal_integer_literal(s, i, kk);
        lemma_non_octal_decimal_equiv(s, i, kk);
        assert(ind_non_octal_decimal_integer(s, i, kk));
    }
    if ind_is_legacy(s, i, j) && !ind_legacy_octal(s, i, j) {
        let kk = choose|kk: int| #![trigger ind_non_octal_decimal_integer(s, i, kk)]
            i < kk <= j && ind_non_octal_decimal_integer(s, i, kk);
        lemma_non_octal_decimal_equiv(s, i, kk);
        assert(non_octal_decimal_integer_literal(s, i, kk));
    }
}

} // verus!
