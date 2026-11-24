//! An independent transcription of the string algorithms the form data set
//! uses (docs/VERIFICATION.md, "Trust without reviewers", item 2), proven
//! equal to [`super::spec`]'s. **Scope: only these algorithms.** The form
//! owner, the entry list's steps, the encodings and the submission
//! algorithm have no independent transcription yet; this file does not make
//! the crate's spec independent as a whole.
//!
//! Sources, read as text and transcribed in a different shape from
//! `spec.rs` (which the transcription was written beside, not before: the
//! two are independent in formulation, not in author):
//! - Infra, "ASCII lowercase" (replace each ASCII upper alpha with the
//!   corresponding ASCII lower alpha: a pointwise map), "strip newlines"
//!   (remove every LF and CR: a filter), "strip leading and trailing ASCII
//!   whitespace" (remove the whitespace at the start and at the end: two
//!   indices), "normalize newlines" (two passes, as the standard words it:
//!   first CR LF pairs, then the remaining CRs);
//! - HTML §2.3.4.2 "rules for parsing integers" and "rules for parsing
//!   non-negative integers", with the standard's *position* variable over
//!   the input, instead of `spec.rs`'s slicing and accumulator;
//! - HTML "valid non-negative integer string" / "the shortest string of
//!   ASCII digits that represents the number in base ten": a string of
//!   ASCII digits, with no leading zero unless it is the one digit "0",
//!   whose positional value is the number. It is a relation here
//!   ([`is_decimal_of`]); [`lemma_decimal_unique`] shows there is exactly
//!   one such string, so equality with `spec.rs`'s `decimal` is "it is
//!   such a string".
//!
//! Modelling choices: as in `spec.rs`, a string is a `Seq<u32>` of code
//! points and a number is a `nat`.

#[cfg(verus_only)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// ASCII lowercase, strip newlines

/// An ASCII upper alpha: U+0041 (A) to U+005A (Z).
pub open spec fn ind_upper_alpha(c: u32) -> bool {
    0x41 <= c && c <= 0x5A
}

/// Infra "ASCII lowercase": each ASCII upper alpha is replaced with the
/// code point 32 above it (its ASCII lower alpha), everything else stays.
pub open spec fn ind_ascii_lowercase(s: Seq<u32>) -> Seq<u32> {
    Seq::new(s.len(), |i: int| if ind_upper_alpha(s[i]) { (s[i] + 32) as u32 } else { s[i] })
}

/// Infra "strip newlines": remove every LF and every CR.
pub open spec fn ind_strip_newlines(s: Seq<u32>) -> Seq<u32> {
    s.filter(|c: u32| c != 0x0A && c != 0x0D)
}

/// `ascii_lower` is the pointwise map of the standard.
pub proof fn lemma_ascii_lower_equal(s: Seq<u32>)
    ensures
        ascii_lower(s) =~= ind_ascii_lowercase(s),
{
    assert forall|i: int| 0 <= i < s.len() implies ascii_lower(s)[i] == ind_ascii_lowercase(s)[i] by {
        assert(ascii_lower(s)[i] == ascii_lower_cp(s[i]));
    }
}

/// `strip_newlines` is the filter of the standard.
pub proof fn lemma_strip_newlines_equal(s: Seq<u32>)
    ensures
        strip_newlines(s) =~= ind_strip_newlines(s),
    decreases s.len(),
{
    reveal_with_fuel(Seq::<u32>::filter, 2);
    if s.len() > 0 {
        let pred = |c: u32| c != 0x0A && c != 0x0D;
        lemma_strip_newlines_equal(s.drop_first());
        assert(s =~= seq![s[0]] + s.drop_first());
        Seq::<u32>::filter_distributes_over_add(seq![s[0]], s.drop_first(), pred);
        assert(seq![s[0]].filter(pred) =~= if pred(s[0]) { seq![s[0]] } else { Seq::<u32>::empty() });
    }
}

// ---------------------------------------------------------------------
// Strip leading and trailing ASCII whitespace

/// Infra "ASCII whitespace": TAB, LF, FF, CR, SPACE.
pub open spec fn ind_white(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// The index of the first code point of `s` at or after `from` that is not
/// ASCII whitespace, or the length of `s` if every one is.
pub open spec fn ind_first_kept(s: Seq<u32>, from: int) -> int
    decreases s.len() - from,
    when 0 <= from
{
    if from >= s.len() || !ind_white(s[from]) {
        from
    } else {
        ind_first_kept(s, from + 1)
    }
}

/// The index just after the last code point of `s` below `to` that is not
/// ASCII whitespace, but not below `floor`.
pub open spec fn ind_end_kept(s: Seq<u32>, floor: int, to: int) -> int
    decreases to - floor,
    when floor <= to
{
    if to > floor && ind_white(s[to - 1]) {
        ind_end_kept(s, floor, to - 1)
    } else {
        to
    }
}

/// Infra "strip leading and trailing ASCII whitespace": the code points
/// from the first one that is not whitespace up to and including the last
/// one that is not whitespace.
pub open spec fn ind_strip_whitespace(s: Seq<u32>) -> Seq<u32> {
    let lo = ind_first_kept(s, 0);
    let hi = ind_end_kept(s, lo, s.len() as int);
    s.subrange(lo, hi)
}

/// `ind_first_kept` stays within `s`.
pub proof fn lemma_first_kept_bounds(s: Seq<u32>, from: int)
    requires
        0 <= from <= s.len(),
    ensures
        from <= ind_first_kept(s, from) <= s.len(),
        ind_first_kept(s, from) < s.len() ==> !ind_white(s[ind_first_kept(s, from)]),
    decreases s.len() - from,
{
    if from < s.len() && ind_white(s[from]) {
        lemma_first_kept_bounds(s, from + 1);
    }
}

/// `trim_start` drops the code points before the first kept one.
proof fn lemma_trim_start_equal(s: Seq<u32>, from: int)
    requires
        0 <= from <= s.len(),
    ensures
        trim_start(s.skip(from)) =~= s.skip(ind_first_kept(s, from)),
    decreases s.len() - from,
{
    if from < s.len() && ind_white(s[from]) {
        lemma_trim_start_equal(s, from + 1);
        assert(s.skip(from).drop_first() =~= s.skip(from + 1));
    }
}

/// `trim_end` drops the code points after the last kept one (not below
/// `floor`).
proof fn lemma_trim_end_equal(s: Seq<u32>, floor: int, to: int)
    requires
        0 <= floor <= to <= s.len(),
    ensures
        trim_end(s.subrange(floor, to)) =~= s.subrange(floor, ind_end_kept(s, floor, to)),
    decreases to - floor,
{
    if to > floor && ind_white(s[to - 1]) {
        lemma_trim_end_equal(s, floor, to - 1);
        assert(s.subrange(floor, to).drop_last() =~= s.subrange(floor, to - 1));
    }
}

/// `strip_whitespace` is the two-index slice of the standard.
pub proof fn lemma_strip_whitespace_equal(s: Seq<u32>)
    ensures
        strip_whitespace(s) =~= ind_strip_whitespace(s),
{
    lemma_first_kept_bounds(s, 0);
    assert(s.skip(0) =~= s);
    lemma_trim_start_equal(s, 0);
    let lo = ind_first_kept(s, 0);
    let t = s.skip(lo);
    assert(t =~= s.subrange(lo, s.len() as int));
    lemma_trim_end_equal(s, lo, s.len() as int);
}

// ---------------------------------------------------------------------
// Normalize newlines, as two passes

/// Pass 1 of Infra "normalize newlines": "replace every U+000D CR U+000A
/// LF code point pair with a single U+000A LF code point", reading `s`
/// from position `i`.
pub open spec fn ind_crlf_pass(s: Seq<u32>, i: int) -> Seq<u32>
    decreases s.len() - i,
    when 0 <= i
{
    if i >= s.len() {
        Seq::empty()
    } else if s[i] == 0x0D && i + 1 < s.len() && s[i + 1] == 0x0A {
        seq![0x0Au32] + ind_crlf_pass(s, i + 2)
    } else {
        seq![s[i]] + ind_crlf_pass(s, i + 1)
    }
}

/// Pass 2: "replace every remaining U+000D CR code point with a U+000A LF
/// code point".
pub open spec fn ind_cr_pass(s: Seq<u32>) -> Seq<u32> {
    Seq::new(s.len(), |i: int| if s[i] == 0x0D { 0x0Au32 } else { s[i] })
}

/// Infra "normalize newlines".
pub open spec fn ind_normalize_newlines(s: Seq<u32>) -> Seq<u32> {
    ind_cr_pass(ind_crlf_pass(s, 0))
}

/// `ind_cr_pass` of a concatenation.
proof fn lemma_cr_pass_add(a: Seq<u32>, b: Seq<u32>)
    ensures
        ind_cr_pass(a + b) =~= ind_cr_pass(a) + ind_cr_pass(b),
{
}

/// The two passes from position `i` give `normalize_newlines` of the rest.
proof fn lemma_normalize_from(s: Seq<u32>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        ind_cr_pass(ind_crlf_pass(s, i)) =~= normalize_newlines(s.skip(i)),
    decreases s.len() - i,
{
    if i < s.len() {
        if s[i] == 0x0D && i + 1 < s.len() && s[i + 1] == 0x0A {
            lemma_normalize_from(s, i + 2);
            lemma_cr_pass_add(seq![0x0Au32], ind_crlf_pass(s, i + 2));
            assert(s.skip(i).skip(2) =~= s.skip(i + 2));
            assert(s.skip(i)[1] == s[i + 1]);
        } else {
            lemma_normalize_from(s, i + 1);
            lemma_cr_pass_add(seq![s[i]], ind_crlf_pass(s, i + 1));
            assert(s.skip(i).drop_first() =~= s.skip(i + 1));
            if s[i] == 0x0D {
                assert(s.skip(i).len() > 1 ==> s.skip(i)[1] == s[i + 1]);
            }
        }
    }
}

/// `normalize_newlines` is the two passes of the standard.
pub proof fn lemma_normalize_newlines_equal(s: Seq<u32>)
    ensures
        normalize_newlines(s) =~= ind_normalize_newlines(s),
{
    lemma_normalize_from(s, 0);
    assert(s.skip(0) =~= s);
}

// ---------------------------------------------------------------------
// Rules for parsing integers, with a position

/// An ASCII digit: U+0030 (0) to U+0039 (9).
pub open spec fn ind_digit(c: u32) -> bool {
    0x30 <= c && c <= 0x39
}

/// The position after the digits "collected" from `p`: the first position
/// at or after `p` whose code point is not an ASCII digit, or the end.
pub open spec fn ind_digits_end(s: Seq<u32>, p: int) -> int
    decreases s.len() - p,
    when 0 <= p
{
    if p >= s.len() || !ind_digit(s[p]) {
        p
    } else {
        ind_digits_end(s, p + 1)
    }
}

/// The number written by the digits `s[p..q]`, in base ten: each digit
/// shifts what precedes it one place left.
pub open spec fn ind_number(s: Seq<u32>, p: int, q: int) -> nat
    decreases q - p,
    when p <= q
{
    if q == p {
        0
    } else {
        ind_number(s, p, q - 1) * 10 + (s[q - 1] - 0x30) as nat
    }
}

/// HTML "rules for parsing integers", then "rules for parsing non-negative
/// integers", with the standard's variables:
/// 1. `input` is `s`. 2. `position` is 0. 3. `sign` is "positive" (here
/// `negative` is false). 4. "Skip ASCII whitespace within input given
/// position." 5. "If position is past the end of input, return an error."
/// 6. "If the character indicated by position is U+002D (-), set sign to
/// "negative" and advance position; otherwise if it is U+002B (+), advance
/// position." 7. "If position is past the end of input, return an error."
/// 8. "If the character indicated by position is not an ASCII digit, then
/// return an error." 9. "Collect a sequence of code points that are ASCII
/// digits from input given position, and interpret the resulting sequence
/// as a base-ten integer. Let value be that integer." 10. "If sign is
/// "positive", return value. Otherwise, return 0 - value." Non-negative:
/// "If result is an error, return an error. If result is less than 0,
/// return an error. Return result."
pub open spec fn ind_parse_non_negative(s: Seq<u32>) -> Option<nat> {
    let p4 = ind_first_kept(s, 0);
    if p4 >= s.len() {
        None
    } else {
        let negative = s[p4] == 0x2D;
        let p6 = if s[p4] == 0x2D || s[p4] == 0x2B { p4 + 1 } else { p4 };
        if p6 >= s.len() || !ind_digit(s[p6]) {
            None
        } else {
            let value = ind_number(s, p6, ind_digits_end(s, p6));
            // "0 - value" is below 0 exactly when value is above 0.
            if negative && value > 0 {
                None
            } else {
                Some(value)
            }
        }
    }
}

/// Bounds of `ind_digits_end`.
proof fn lemma_digits_end_bounds(s: Seq<u32>, p: int)
    requires
        0 <= p <= s.len(),
    ensures
        p <= ind_digits_end(s, p) <= s.len(),
    decreases s.len() - p,
{
    if p < s.len() && ind_digit(s[p]) {
        lemma_digits_end_bounds(s, p + 1);
    }
}

/// `digits_value(s.skip(p), acc)` continues the number from `acc`.
proof fn lemma_digits_value_number(s: Seq<u32>, p: int, acc: nat)
    requires
        0 <= p <= s.len(),
    ensures
        digits_value(s.skip(p), acc) == ind_number_from(s, p, ind_digits_end(s, p), acc),
    decreases s.len() - p,
{
    lemma_digits_end_bounds(s, p);
    if p < s.len() && ind_digit(s[p]) {
        let acc2 = (acc * 10 + (s[p] - 0x30) as nat) as nat;
        lemma_digits_value_number(s, p + 1, acc2);
        assert(s.skip(p).drop_first() =~= s.skip(p + 1));
        assert(s.skip(p)[0] == s[p]);
        let q = ind_digits_end(s, p);
        lemma_digits_end_bounds(s, p + 1);
        assert(q == ind_digits_end(s, p + 1));
        assert(p < q);
        lemma_number_from_step(s, p, q, acc);
    }
}

/// The number written by `s[p..q]` after the value `acc` (what `acc`
/// followed by those digits writes).
pub open spec fn ind_number_from(s: Seq<u32>, p: int, q: int, acc: nat) -> nat
    decreases q - p,
    when p <= q
{
    if q == p {
        acc
    } else {
        ind_number_from(s, p, q - 1, acc) * 10 + (s[q - 1] - 0x30) as nat
    }
}

/// With `acc` = 0 the two numbers agree.
proof fn lemma_number_from_zero(s: Seq<u32>, p: int, q: int)
    requires
        p <= q,
    ensures
        ind_number_from(s, p, q, 0) == ind_number(s, p, q),
    decreases q - p,
{
    if q > p {
        lemma_number_from_zero(s, p, q - 1);
    }
}

/// `ind_number_from` shifts: stepping the start forward one digit.
proof fn lemma_number_from_step(s: Seq<u32>, p: int, q: int, acc: nat)
    requires
        0 <= p < q <= s.len(),
    ensures
        ind_number_from(s, p, q, acc) == ind_number_from(s, p + 1, q, (acc * 10 + (s[p] - 0x30) as nat) as nat),
    decreases q - p,
{
    if q > p + 1 {
        lemma_number_from_step(s, p, q - 1, acc);
        assert(ind_number_from(s, p, q, acc) == ind_number_from(s, p, q - 1, acc) * 10 + (s[q - 1] - 0x30) as nat);
        assert(ind_number_from(s, p + 1, q, (acc * 10 + (s[p] - 0x30) as nat) as nat)
            == ind_number_from(s, p + 1, q - 1, (acc * 10 + (s[p] - 0x30) as nat) as nat) * 10 + (s[q - 1] - 0x30) as nat);
    } else {
        assert(ind_number_from(s, p, q, acc) == ind_number_from(s, p, p, acc) * 10 + (s[p] - 0x30) as nat);
        assert(ind_number_from(s, p + 1, p + 1, (acc * 10 + (s[p] - 0x30) as nat) as nat)
            == (acc * 10 + (s[p] - 0x30) as nat) as nat);
    }
}

/// `parse_after_sign` agrees with steps 7 to 10.
proof fn lemma_after_sign(s: Seq<u32>, p: int, negative: bool)
    requires
        0 <= p <= s.len(),
    ensures
        parse_after_sign(s.skip(p), negative) == if p >= s.len() || !ind_digit(s[p]) {
            None
        } else {
            let value = ind_number(s, p, ind_digits_end(s, p));
            if negative && value > 0 {
                None
            } else {
                Some(value)
            }
        },
{
    if p < s.len() && ind_digit(s[p]) {
        lemma_digits_value_number(s, p, 0);
        lemma_digits_end_bounds(s, p);
        lemma_number_from_zero(s, p, ind_digits_end(s, p));
        assert(s.skip(p)[0] == s[p]);
    }
}

/// `parse_non_negative` is the standard's steps.
pub proof fn lemma_parse_non_negative_equal(s: Seq<u32>)
    ensures
        parse_non_negative(s) == ind_parse_non_negative(s),
{
    lemma_first_kept_bounds(s, 0);
    assert(s.skip(0) =~= s);
    lemma_trim_start_equal(s, 0);
    let p4 = ind_first_kept(s, 0);
    let t = trim_start(s);
    assert(t =~= s.skip(p4));
    if p4 < s.len() {
        assert(t[0] == s[p4]);
        if s[p4] == 0x2D || s[p4] == 0x2B {
            lemma_after_sign(s, p4 + 1, s[p4] == 0x2D);
            assert(t.drop_first() =~= s.skip(p4 + 1));
        } else {
            lemma_after_sign(s, p4, false);
        }
    }
}

// ---------------------------------------------------------------------
// The shortest string of ASCII digits for a number

/// The positional value of a string of ASCII digits.
pub open spec fn ind_positional(d: Seq<u32>) -> nat
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        ind_positional(d.drop_last()) * 10 + (d.last() - 0x30) as nat
    }
}

/// `d` is a string of ASCII digits.
pub open spec fn ind_all_digits(d: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < d.len() ==> ind_digit(#[trigger] d[i])
}

/// `d` is the base-ten string of `n`: ASCII digits only, at least one, no
/// leading zero unless it is the single digit "0", and value `n`.
pub open spec fn is_decimal_of(d: Seq<u32>, n: nat) -> bool {
    &&& d.len() > 0
    &&& ind_all_digits(d)
    &&& (d.len() == 1 || d[0] != 0x30)
    &&& ind_positional(d) == n
}

/// A digit string of length 2 or more with no leading zero is worth at
/// least 10; one of length 1 is worth less than 10.
proof fn lemma_positional_floor(d: Seq<u32>)
    requires
        d.len() >= 1,
        ind_all_digits(d),
        d[0] != 0x30,
    ensures
        ind_positional(d) >= 1,
        d.len() >= 2 ==> ind_positional(d) >= 10,
    decreases d.len(),
{
    if d.len() >= 2 {
        let h = d.drop_last();
        assert(h[0] == d[0]);
        assert forall|i: int| 0 <= i < h.len() implies ind_digit(#[trigger] h[i]) by {
            assert(h[i] == d[i]);
        }
        lemma_positional_floor(h);
    }
}

/// Every digit string is worth less than 10 times as much as its length
/// minus one allows: the last digit is its value modulo 10 and the rest
/// is its value divided by 10.
proof fn lemma_positional_split(d: Seq<u32>)
    requires
        d.len() >= 1,
        ind_all_digits(d),
    ensures
        ind_positional(d) % 10 == (d.last() - 0x30) as nat,
        ind_positional(d) / 10 == ind_positional(d.drop_last()),
{
    assert(ind_digit(d.last()));
}

/// There is exactly one base-ten string for a number.
pub proof fn lemma_decimal_unique(a: Seq<u32>, b: Seq<u32>, n: nat)
    requires
        is_decimal_of(a, n),
        is_decimal_of(b, n),
    ensures
        a =~= b,
    decreases a.len(),
{
    lemma_positional_split(a);
    lemma_positional_split(b);
    if a.len() == 1 || b.len() == 1 {
        // A one-digit string is below 10, and a longer one is not.
        if a.len() >= 2 {
            let h = a.drop_last();
            assert(a[0] != 0x30);
            assert(h[0] == a[0]);
            assert forall|i: int| 0 <= i < a.len() implies ind_digit(#[trigger] a[i]) by {}
            lemma_positional_floor(a);
            assert(ind_positional(b) < 10) by {
                assert(ind_digit(b[0]));
                assert(b.drop_last().len() == 0);
            }
        }
        if b.len() >= 2 {
            lemma_positional_floor(b);
            assert(ind_positional(a) < 10) by {
                assert(ind_digit(a[0]));
                assert(a.drop_last().len() == 0);
            }
        }
        if a.len() == 1 && b.len() == 1 {
            assert(a[0] == b[0]);
        }
    } else {
        let ha = a.drop_last();
        let hb = b.drop_last();
        assert(ha[0] == a[0]);
        assert(hb[0] == b[0]);
        assert forall|i: int| 0 <= i < ha.len() implies ind_digit(#[trigger] ha[i]) by {
            assert(ha[i] == a[i]);
        }
        assert forall|i: int| 0 <= i < hb.len() implies ind_digit(#[trigger] hb[i]) by {
            assert(hb[i] == b[i]);
        }
        lemma_decimal_unique(ha, hb, (n / 10) as nat);
        assert(a.last() == b.last());
        assert(a =~= ha.push(a.last()));
        assert(b =~= hb.push(b.last()));
    }
}

/// `decimal(n)` is a string of ASCII digits, with no leading zero unless
/// it is "0", worth `n`.
pub proof fn lemma_decimal_is_decimal(n: nat)
    ensures
        is_decimal_of(decimal(n), n),
    decreases n,
{
    let d = decimal(n);
    if n < 10 {
        assert(d =~= seq![(0x30 + n) as u32]);
        assert(d.drop_last() =~= Seq::<u32>::empty());
        assert(d.last() == (0x30 + n) as u32);
        assert(ind_positional(Seq::<u32>::empty()) == 0);
        assert(ind_positional(d) == ind_positional(d.drop_last()) * 10 + (d.last() - 0x30) as nat);
        assert forall|i: int| 0 <= i < d.len() implies ind_digit(#[trigger] d[i]) by {}
    } else {
        lemma_decimal_is_decimal(n / 10);
        let h = decimal(n / 10);
        assert(d.drop_last() =~= h);
        assert(d.last() == (0x30 + n % 10) as u32);
        assert forall|i: int| 0 <= i < d.len() implies ind_digit(#[trigger] d[i]) by {
            if i < h.len() {
                assert(d[i] == h[i]);
            }
        }
        assert(d[0] == h[0]);
        assert(ind_positional(d) == ind_positional(h) * 10 + (d.last() - 0x30) as nat);
        assert(n == (n / 10) * 10 + n % 10) by (nonlinear_arith);
        if h.len() == 1 {
            // n / 10 is at least 1: its one digit is not "0".
            assert(ind_positional(h) == n / 10);
            assert(h[0] != 0x30) by {
                assert(n / 10 >= 1);
                assert(ind_positional(h) == ind_positional(h.drop_last()) * 10 + (h.last() - 0x30) as nat);
                assert(h.drop_last().len() == 0);
            }
        }
    }
}

} // verus!
