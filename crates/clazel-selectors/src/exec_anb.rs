//! §21.1's `<an+b>` (CSS Syntax §6.2) on items: the integer values the clauses of
//! [`a_n_plus_b`] give, clamped as the spec clamps them ([`clamp`]).
//!
//! A value is kept as an `i64` between `-2^32` and `2^32` ([`wide`]) until the end: clamping
//! to 32 bits first would lose the sign of "-b" for a `b` of 2^31 or more.

use super::exec_items::*;
#[cfg(verus_only)]
use super::exec_numbers::*;
use super::exec_parse::{skip_ws, tok};
use super::exec_types::item;
#[allow(unused_imports)]
use super::spec::*;
use clazel_css::parser::exec_declaration::{lowercase, matches_ignoring_case};
use clazel_css::parser::exec_parse::ExecParsed;
#[cfg(verus_only)]
use clazel_css::tokenizer::exec::{view_number, view_token};
use clazel_css::tokenizer::exec::{ExecNumber, ExecToken};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Values
// ------------------------------------------------------------------------------------

/// Where a value stops counting: well above what [`clamp`] keeps.
pub open spec fn cap() -> int {
    0x1_0000_0000
}

/// `v`, kept within `-cap()` and `cap()`.
pub open spec fn wide(v: int) -> int {
    if v > cap() {
        cap()
    } else if v < -cap() {
        -cap()
    } else {
        v
    }
}

/// Clamping after keeping within the cap is clamping.
proof fn lemma_clamp_wide(v: int)
    ensures
        clamp(wide(v)) == clamp(v),
        wide(-v) == -wide(v),
{
}

/// `m` is `dv`, or past the cap if `dv` is.
pub open spec fn sat_ok(m: u64, dv: nat) -> bool {
    if dv <= cap() {
        m == dv
    } else {
        m > cap()
    }
}

/// One more digit onto the digits' value.
proof fn lemma_dv_push(ds: Seq<u32>, c: u32, v: nat)
    requires
        0x30 <= c <= 0x39,
    ensures
        digits_value(ds.push(c), v) == digits_value(ds, v) * 10 + (c - 0x30) as nat,
    decreases ds.len(),
{
    reveal_with_fuel(digits_value, 2);
    if ds.len() == 0 {
        assert(ds.push(c).drop_first() =~= Seq::<u32>::empty());
        assert(ds.push(c)[0] == c);
    } else {
        assert(ds.push(c).drop_first() =~= ds.drop_first().push(c));
        assert(ds.push(c)[0] == ds[0]);
        lemma_dv_push(ds.drop_first(), c, v * 10 + (ds[0] - 0x30) as nat);
    }
}

/// The value of the first `n + 1` digits.
proof fn lemma_dv_take(s: Seq<u32>, n: int)
    requires
        0 <= n < s.len(),
        0x30 <= s[n] <= 0x39,
    ensures
        digits_value(s.subrange(0, n + 1), 0) == digits_value(s.subrange(0, n), 0) * 10 + (s[n]
            - 0x30) as nat,
{
    assert(s.subrange(0, n + 1) =~= s.subrange(0, n).push(s[n]));
    lemma_dv_push(s.subrange(0, n), s[n], 0);
}

/// One more digit onto a saturating magnitude.
fn push_digit(m: u64, c: u32) -> (r: u64)
    requires
        0x30 <= c <= 0x39,
        m <= 0x1_0000_0000 || true,
    ensures
        m <= cap() ==> r == m * 10 + (c - 0x30),
        m > cap() ==> r == m,
{
    if m <= 0x1_0000_0000 {
        m.saturating_mul(10).saturating_add((c.saturating_sub(0x30)) as u64)
    } else {
        m
    }
}

/// [`sat_ok`] after one more digit.
proof fn lemma_sat_step(m: u64, dv: nat, c: u32, r: u64)
    requires
        0x30 <= c <= 0x39,
        sat_ok(m, dv),
        m <= cap() ==> r == m * 10 + (c - 0x30),
        m > cap() ==> r == m,
    ensures
        sat_ok(r, dv * 10 + (c - 0x30) as nat),
{
}

/// `-b`, which cannot overflow for a `b` that is not the least.
fn negate(b: i64) -> (r: i64)
    requires
        -0x1_0000_0000 <= b <= 0x1_0000_0000,
    ensures
        r == -b,
{
    match 0i64.checked_sub(b) {
        Some(v) => v,
        None => vstd::pervasive::unreached(),
    }
}

/// The value of a magnitude with a sign, kept within the cap.
fn signed(negative: bool, magnitude: u64) -> (r: i64)
    ensures
        negative ==> r == -(if magnitude > cap() { cap() } else { magnitude as int }),
        !negative ==> r == (if magnitude > cap() { cap() } else { magnitude as int }),
        -cap() <= r <= cap(),
{
    let w: i64 = if magnitude > 0x1_0000_0000 {
        0x1_0000_0000
    } else {
        magnitude as i64
    };
    if negative {
        negate(w)
    } else {
        w
    }
}

/// `w` clamped to the range the spec keeps: [`clamp`] of it.
pub fn clamp32(w: i64) -> (r: i32)
    ensures
        r == clamp(w as int),
{
    if w < -0x8000_0000 {
        i32::MIN
    } else if w > 0x7FFF_FFFF {
        i32::MAX
    } else {
        w as i32
    }
}

/// With no `.` among them, the digits of a part are all of it.
proof fn lemma_point_of(part: Seq<u32>, i: nat)
    requires
        digits_only(part),
        i <= part.len(),
    ensures
        point_of(part, i) == part.len(),
    decreases part.len() - i,
{
    if i < part.len() {
        assert(is_digit(part[i as int]));
        lemma_point_of(part, i + 1);
    }
}

/// The integer value of a number made as the tokenizer makes an integer.
proof fn lemma_integer_value(n: Number)
    requires
        n.is_integer,
        num_ok(n),
    ensures
        integer_value(n) == if is_negative(n.number_part) {
            -(digits_value(unsigned(n.number_part), 0) as int)
        } else {
            digits_value(unsigned(n.number_part), 0) as int
        },
{
    let part = unsigned(n.number_part);
    lemma_point_of(part, 0);
    assert(part.subrange(0, part.len() as int) =~= part);
    assert(part + Seq::<u32>::empty() =~= part);
    assert(unsigned(n.exponent_part) =~= Seq::<u32>::empty());
}

/// The first digit of a part past its sign (the sign being `start` long).
spec fn digit_start(part: Seq<u32>) -> int {
    if part.len() > 0 && (part[0] == 0x2B || part[0] == 0x2D) {
        1
    } else {
        0
    }
}

/// The value of an integer number, kept within the cap ([`wide`]).
pub fn wide_value(number: &ExecNumber) -> (r: i64)
    requires
        number.is_integer,
        num_ok(view_number(*number)),
    ensures
        r == wide(integer_value(view_number(*number))),
{
    let part = number.number_part.as_slice();
    let ghost n = view_number(*number);
    let ghost s = unsigned(part@);
    let mut start: usize = 0;
    let mut negative = false;
    if !part.is_empty() && (*item(part, 0) == 0x2B || *item(part, 0) == 0x2D) {
        negative = *item(part, 0) == 0x2D;
        start = 1;
    }
    proof {
        lemma_integer_value(n);
        assert(start == digit_start(part@));
        if start == 1 {
            assert(s =~= part@.drop_first());
        } else {
            assert(s =~= part@);
        }
        assert(negative == is_negative(part@));
    }
    let mut k = start;
    let mut magnitude: u64 = 0;
    proof {
        assert(s.subrange(0, 0) =~= Seq::<u32>::empty());
    }
    while k < part.len()
        invariant
            start <= k <= part.len(),
            s.len() == part.len() - start,
            forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] == part@[start + j],
            digits_only(s),
            sat_ok(magnitude, digits_value(s.subrange(0, k - start), 0)),
        decreases part.len() - k,
    {
        let c = *item(part, k);
        proof {
            assert(is_digit(s[k - start]));
            lemma_dv_take(s, k - start);
        }
        let next = push_digit(magnitude, c);
        proof {
            lemma_sat_step(magnitude, digits_value(s.subrange(0, k - start), 0), c, next);
        }
        magnitude = next;
        k = k.saturating_add(1);
    }
    proof {
        assert(s.subrange(0, s.len() as int) =~= s);
    }
    signed(negative, magnitude)
}

/// The digits from `start` of `s`, as a negative number: [`negative_remainder`] kept within
/// the cap.
pub fn remainder(s: &[u32], start: usize) -> (r: i64)
    requires
        start < s.len(),
        digits_only(s@.skip(start as int + 1)),
    ensures
        r == wide(negative_remainder(s@, start as int)),
{
    let ghost digits = s@.subrange(start as int + 1, s@.len() as int);
    let mut k = start.saturating_add(1);
    let mut magnitude: u64 = 0;
    proof {
        assert(k == start + 1);
        assert(digits =~= s@.skip(start as int + 1));
        assert(digits.subrange(0, 0) =~= Seq::<u32>::empty());
    }
    while k < s.len()
        invariant
            start + 1 <= k <= s.len(),
            digits.len() == s.len() - start - 1,
            forall|j: int| 0 <= j < digits.len() ==> #[trigger] digits[j] == s@[start + 1 + j],
            digits_only(digits),
            sat_ok(magnitude, digits_value(digits.subrange(0, k - start - 1), 0)),
        decreases s.len() - k,
    {
        let c = *item(s, k);
        proof {
            assert(is_digit(digits[k - start - 1]));
            lemma_dv_take(digits, k - start - 1);
        }
        let next = push_digit(magnitude, c);
        proof {
            lemma_sat_step(magnitude, digits_value(digits.subrange(0, k - start - 1), 0), c, next);
        }
        magnitude = next;
        k = k.saturating_add(1);
    }
    proof {
        assert(digits.subrange(0, digits.len() as int) =~= digits);
    }
    signed(true, magnitude)
}


// ------------------------------------------------------------------------------------
// Reading an item
// ------------------------------------------------------------------------------------

/// The component values of `items`.
pub open spec fn vw(src: ExecParsed, items: Seq<&ExecItem>) -> Seq<ComponentValue> {
    items.map_values(|it: &ExecItem| item_view(src, *it))
}

/// Every item's numbers are as the tokenizer makes them.
pub open spec fn all_ok(items: Seq<&ExecItem>) -> bool {
    forall|k: int| 0 <= k < items.len() ==> item_ok(*#[trigger] items[k])
}

/// The item at `i` of a list of item references.
fn at<'a>(items: &[&'a ExecItem], i: usize) -> (r: &'a ExecItem)
    requires
        i < items@.len(),
    ensures
        *r == *items@[i as int],
{
    match items.get(i) {
        Some(x) => x,
        None => vstd::pervasive::unreached(),
    }
}

/// The token of an item that is one.
fn token_of<'a>(it: &'a ExecItem) -> (r: Option<&'a ExecToken>)
    ensures
        match r {
            Some(t) => *it == (ExecItem::Token { token: *t }),
            None => !(it is Token),
        },
{
    match it {
        ExecItem::Token { token } => Some(token),
        _ => None,
    }
}

/// [`is_keyword`].
fn keyword(src: &ExecParsed, it: &ExecItem, lowercase: &[u32]) -> (r: bool)
    ensures
        r == is_keyword(item_view(*src, *it), lowercase@),
{
    let _ = src;
    match token_of(it) {
        Some(ExecToken::Ident { value }) => matches_ignoring_case(value, lowercase),
        _ => false,
    }
}

/// [`is_plus`] and [`is_minus`].
fn delim_item(src: &ExecParsed, it: &ExecItem, c: u32) -> (r: bool)
    ensures
        r == is(item_view(*src, *it), Token::Delim { value: c }),
{
    let _ = src;
    matches!(token_of(it), Some(ExecToken::Delim { value }) if *value == c)
}

/// [`integer_number`].
fn integer_of<'a>(src: &ExecParsed, it: &'a ExecItem) -> (r: Option<&'a ExecNumber>)
    ensures
        match r {
            Some(n) => integer_number(item_view(*src, *it)) == Some(view_number(*n)),
            None => integer_number(item_view(*src, *it)) is None,
        },
{
    let _ = src;
    match token_of(it) {
        Some(ExecToken::Number { number }) if number.is_integer => Some(number),
        _ => None,
    }
}

/// [`signed_integer`], within the cap.
fn signed_of(src: &ExecParsed, it: &ExecItem) -> (r: Option<i64>)
    requires
        item_ok(*it),
    ensures
        match r {
            Some(v) => signed_integer(item_view(*src, *it)) is Some && v == wide(
                signed_integer(item_view(*src, *it)).unwrap(),
            ),
            None => signed_integer(item_view(*src, *it)) is None,
        },
{
    match integer_of(src, it) {
        Some(number) if number.sign_character.is_some() => Some(wide_value(number)),
        _ => None,
    }
}

/// [`signless_integer`], within the cap.
fn signless_of(src: &ExecParsed, it: &ExecItem) -> (r: Option<i64>)
    requires
        item_ok(*it),
    ensures
        match r {
            Some(v) => signless_integer(item_view(*src, *it)) is Some && v == wide(
                signless_integer(item_view(*src, *it)).unwrap(),
            ),
            None => signless_integer(item_view(*src, *it)) is None,
        },
{
    match integer_of(src, it) {
        Some(number) if number.sign_character.is_none() => Some(wide_value(number)),
        _ => None,
    }
}

/// An integer dimension: its value, within the cap, and unit.
fn integer_dimension<'a>(src: &ExecParsed, it: &'a ExecItem) -> (r: Option<(i64, &'a Vec<u32>)>)
    requires
        item_ok(*it),
    ensures
        match r {
            Some((v, unit)) => v == wide(dimension_value(item_view(*src, *it))) && unit@
                == dimension_unit(item_view(*src, *it)) && is_integer_dimension(item_view(*src, *it)),
            None => !is_integer_dimension(item_view(*src, *it)),
        },
{
    let _ = src;
    match token_of(it) {
        Some(ExecToken::Dimension { number, unit }) if number.is_integer => Some(
            (wide_value(number), unit),
        ),
        _ => None,
    }
}


// ------------------------------------------------------------------------------------
// The clauses
// ------------------------------------------------------------------------------------

/// `n` and the digits after it, from `i`.
fn digits_from(string: &[u32], start: usize) -> (r: bool)
    ensures
        r == all_digits(string@, start as int),
{
    let mut i = start;
    while i < string.len()
        invariant
            start <= i,
            all_digits(string@, start as int) == all_digits(string@, i as int),
        decreases string.len() - i,
    {
        let c = *item(string, i);
        if !(0x30 <= c && c <= 0x39) {
            proof {
                lemma_digit_fails(string@, start as int, i as int);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

/// [`all_digits`] is false before something else.
proof fn lemma_digit_fails(string: Seq<u32>, i: int, k: int)
    requires
        i <= k < string.len(),
        0 <= k,
        !is_digit(string[k]),
    ensures
        !all_digits(string, i),
    decreases k - i,
{
    if i < k {
        lemma_digit_fails(string, i + 1, k);
    }
}

/// [`all_digits`] from `i` is every code point from `i` being a digit.
proof fn lemma_all_digits(string: Seq<u32>, i: int)
    requires
        0 <= i <= string.len(),
        all_digits(string, i),
    ensures
        digits_only(string.skip(i)),
    decreases string.len() - i,
{
    if i < string.len() {
        assert(is_digit(string[i]));
        lemma_all_digits(string, i + 1);
        assert forall|k: int| 0 <= k < string.skip(i).len() implies is_digit(string.skip(i)[k]) by {
            if k == 0 {
            } else {
                assert(string.skip(i + 1)[k - 1] == string.skip(i)[k]);
            }
        }
    }
}

/// [`is_n_dash_digits`].
fn n_dash_digits(s: &[u32], start: usize) -> (r: bool)
    requires
        start <= 1,
    ensures
        r == is_n_dash_digits(s@, start as int),
{
    if s.len() < start.saturating_add(3) {
        return false;
    }
    lowercase(*item(s, start)) == 0x6E && *item(s, start.saturating_add(1)) == 0x2D && digits_from(
        s,
        start.saturating_add(2),
    )
}

/// What a clause gives: (A, taken), as spec ints.
pub open spec fn view_a(r: Option<(i64, usize)>) -> Option<(int, int)> {
    match r {
        Some((a, t)) => Some((a as int, t as int)),
        None => None,
    }
}

/// The pair with its first within the cap.
pub open spec fn wide_first(p: Option<(int, int)>) -> Option<(int, int)> {
    match p {
        Some((a, t)) => Some((wide(a), t)),
        None => None,
    }
}

/// [`a_of_n`] (`dash` false) or [`a_of_n_dash`] (`dash` true): (A, items taken).
fn a_of(src: &ExecParsed, items: &[&ExecItem], plus_adjacent: bool, dash: bool) -> (r: Option<(i64, usize)>)
    requires
        all_ok(items@),
    ensures
        view_a(r) == wide_first(
            if dash {
                a_of_n_dash(vw(*src, items@), plus_adjacent)
            } else {
                a_of_n(vw(*src, items@), plus_adjacent)
            },
        ),
{
    let ghost w = vw(*src, items@);
    proof {
        assert(w.len() == items@.len());
        assert forall|k: int| 0 <= k < w.len() implies w[k] == item_view(*src, *items@[k]) by {}
    }
    if items.is_empty() {
        return None;
    }
    let first = at(items, 0);
    let (n, dash_n): (&[u32], &[u32]) = if dash {
        (&[0x6E, 0x2D], &[0x2D, 0x6E, 0x2D])
    } else {
        (&[0x6E], &[0x2D, 0x6E])
    };
    proof {
        if dash {
            assert(n@ =~= n_dash_string());
            assert(dash_n@ =~= dash_n_dash_string());
        } else {
            assert(n@ =~= n_string());
            assert(dash_n@ =~= dash_n_string());
        }
        assert(item_ok(*items@[0]));
    }
    let dim = integer_dimension(src, first);
    if let Some((value, unit)) = dim {
        if matches_ignoring_case(unit, n) {
            return Some((value, 1));
        }
    }
    if keyword(src, first, n) {
        Some((1, 1))
    } else if keyword(src, first, dash_n) {
        Some((-1, 1))
    } else if items.len() >= 2 && delim_item(src, first, 0x2B) && plus_adjacent && keyword(
        src,
        at(items, 1),
        n,
    ) {
        Some((1, 2))
    } else {
        None
    }
}

/// [`single_clause`], with each of A and B within the cap.
fn single_clause_of(src: &ExecParsed, items: &[&ExecItem], plus_adjacent: bool) -> (r: Option<(i64, i64)>)
    requires
        all_ok(items@),
        items@.len() > 0,
    ensures
        match r {
            Some((a, b)) => match single_clause(vw(*src, items@), plus_adjacent) {
                Some((x, y)) => a == wide(x) && b == wide(y),
                None => false,
            },
            None => single_clause(vw(*src, items@), plus_adjacent) is None,
        },
{
    let ghost w = vw(*src, items@);
    proof {
        assert(w.len() == items@.len());
        assert forall|k: int| 0 <= k < w.len() implies w[k] == item_view(*src, *items@[k]) by {}
    }
    let last = at(items, items.len().saturating_sub(1));
    let plussed = items.len() == 2 && delim_item(src, at(items, 0), 0x2B) && plus_adjacent;
    proof {
        assert(w.last() == w[w.len() - 1]);
        assert(item_ok(*last));
    }
    let dim = integer_dimension(src, last);
    if let Some((value, unit)) = dim {
        if items.len() == 1 && n_dash_digits(unit, 0) {
            proof {
                lemma_all_digits(unit@, 2);
            }
            return Some((value, remainder(unit, 1)));
        }
    }
    if let Some(ExecToken::Ident { value }) = token_of(last) {
        if (items.len() == 1 || plussed) && n_dash_digits(value, 0) {
            proof {
                lemma_all_digits(value@, 2);
            }
            return Some((1, remainder(value, 1)));
        }
        if items.len() == 1 && !value.is_empty() && *item(value, 0) == 0x2D && n_dash_digits(value, 1) {
            proof {
                lemma_all_digits(value@, 3);
            }
            return Some((-1, remainder(value, 2)));
        }
    }
    None
}


/// The clauses of [`a_n_plus_b_items`], with each of A and B within the cap.
fn clauses(src: &ExecParsed, items: &[&ExecItem], plus_adjacent: bool) -> (r: Option<(i64, i64)>)
    requires
        all_ok(items@),
    ensures
        match r {
            Some((a, b)) => match a_n_plus_b_items(vw(*src, items@), plus_adjacent) {
                Some((x, y)) => a == wide(x) && b == wide(y),
                None => false,
            },
            None => a_n_plus_b_items(vw(*src, items@), plus_adjacent) is None,
        },
{
    let ghost w = vw(*src, items@);
    proof {
        assert(w.len() == items@.len());
        assert forall|k: int| 0 <= k < w.len() implies w[k] == item_view(*src, *items@[k]) by {}
    }
    let count = items.len();
    if count == 0 {
        return None;
    }
    let odd: [u32; 3] = [0x6F, 0x64, 0x64];
    let even: [u32; 4] = [0x65, 0x76, 0x65, 0x6E];
    proof {
        assert(odd@ =~= seq![0x6Fu32, 0x64, 0x64]);
        assert(even@ =~= seq![0x65u32, 0x76, 0x65, 0x6E]);
        assert(item_ok(*items@[0]));
    }
    if count == 1 && keyword(src, at(items, 0), odd.as_slice()) {
        return Some((2, 1));
    }
    if count == 1 && keyword(src, at(items, 0), even.as_slice()) {
        return Some((2, 0));
    }
    if count == 1 {
        if let Some(number) = integer_of(src, at(items, 0)) {
            proof {
                assert(num_ok(view_number(*number)));
            }
            return Some((0, wide_value(number)));
        }
    }
    let last = at(items, count.saturating_sub(1));
    proof {
        assert(w.last() == w[w.len() - 1]);
        assert(item_ok(*last));
    }
    match a_of(src, items, plus_adjacent, false) {
        Some((a, taken)) => {
            proof {
                assert(taken == 1 || taken == 2);
            }
            if count == taken {
                Some((a, 0))
            } else if count == taken.saturating_add(1) {
                match signed_of(src, last) {
                    Some(b) => Some((a, b)),
                    None => None,
                }
            } else if count == taken.saturating_add(2) {
                match signless_of(src, last) {
                    Some(b) => {
                        let sign = at(items, taken);
                        if delim_item(src, sign, 0x2B) {
                            Some((a, b))
                        } else if delim_item(src, sign, 0x2D) {
                            Some((a, negate(b)))
                        } else {
                            None
                        }
                    },
                    None => None,
                }
            } else {
                None
            }
        },
        None => match a_of(src, items, plus_adjacent, true) {
            Some((a, taken)) if count == taken.saturating_add(1) => match signless_of(src, last) {
                Some(b) => Some((a, negate(b))),
                None => None,
            },
            _ => single_clause_of(src, items, plus_adjacent),
        },
    }
}

/// [`first_non_whitespace`] from `i` is [`skip_whitespace`] to the end.
proof fn lemma_fnw_skip(l: Seq<ComponentValue>, i: int)
    requires
        0 <= i <= l.len(),
    ensures
        first_non_whitespace(l, i) == skip_whitespace(l, i, l.len() as int),
    decreases l.len() - i,
{
    if i < l.len() && is_whitespace_token(l[i]) {
        lemma_fnw_skip(l, i + 1);
        assert(whitespace_run(l, i, l.len() as int) == 1 + whitespace_run(l, i + 1, l.len() as int));
    }
}

/// [`without_whitespace`] of the first `k + 1` items, from that of the first `k`.
proof fn lemma_ww_step(l: Seq<ComponentValue>, k: int)
    requires
        0 <= k < l.len(),
    ensures
        without_whitespace(l.subrange(0, k + 1)) == if is_whitespace_token(l[k]) {
            without_whitespace(l.subrange(0, k))
        } else {
            without_whitespace(l.subrange(0, k)).push(l[k])
        },
{
    let p = l.subrange(0, k + 1);
    assert(p.drop_last() =~= l.subrange(0, k));
    assert(p.last() == l[k]);
}

/// [`a_n_plus_b`] on the rows `lo` up to `hi`, with A and B clamped.
pub fn a_n_plus_b_of(src: &ExecParsed, lo: usize, hi: usize) -> (r: Option<(i32, i32)>)
    requires
        src_ok(*src),
    ensures
        match r {
            Some((a, b)) => match a_n_plus_b(rows_list(*src, lo as int, hi as int)) {
                Some((x, y)) => a == clamp(x) && b == clamp(y),
                None => false,
            },
            None => a_n_plus_b(rows_list(*src, lo as int, hi as int)) is None,
        },
{
    let value = read_items(src, lo, hi);
    let value = value.as_slice();
    let ghost l = view_items(*src, value@);
    let len = value.len();
    proof {
        assert(l == rows_list(*src, lo as int, hi as int));
        assert(l.len() == len);
    }
    let start = skip_ws(src, value, 0, len);
    let plus_adjacent = start.saturating_add(1) < len && !matches!(
        tok(src, value, start.saturating_add(1), len),
        Some(ExecToken::Whitespace)
    );
    proof {
        lemma_fnw_skip(l, 0);
        assert(start == first_non_whitespace(l, 0));
        if start + 1 < len {
            assert(start < len);
        }
        assert(plus_adjacent == (start + 1 < l.len() && !is_whitespace_token(l[start + 1])));
    }
    let mut items: Vec<&ExecItem> = Vec::new();
    let mut k = 0;
    proof {
        assert(l.subrange(0, 0) =~= Seq::<ComponentValue>::empty());
        assert(vw(*src, items@) =~= Seq::<ComponentValue>::empty());
    }
    while k < len
        invariant
            k <= len,
            l == view_items(*src, value@),
            len == value.len(),
            l.len() == len,
            vw(*src, items@) == without_whitespace(l.subrange(0, k as int)),
            all_ok(items@),
            forall|j: int| 0 <= j < value@.len() ==> item_ok(#[trigger] value@[j]),
        decreases len - k,
    {
        let it = item(value, k);
        proof {
            lemma_ww_step(l, k as int);
            assert(l[k as int] == item_view(*src, value@[k as int]));
        }
        if !matches!(token_of(it), Some(ExecToken::Whitespace)) {
            proof {
                let before = items@;
                assert(vw(*src, before.push(it)) =~= vw(*src, before).push(item_view(*src, *it)));
            }
            items.push(it);
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(l.subrange(0, len as int) =~= l);
    }
    let items = items.as_slice();
    let result = clauses(src, items, plus_adjacent);
    proof {
        assert(a_n_plus_b(l) == a_n_plus_b_items(without_whitespace(l), plus_adjacent));
    }
    match result {
        Some((a, b)) => {
            proof {
                match a_n_plus_b_items(without_whitespace(l), plus_adjacent) {
                    Some((x, y)) => {
                        lemma_clamp_wide(x);
                        lemma_clamp_wide(y);
                    },
                    None => {},
                }
            }
            Some((clamp32(a), clamp32(b)))
        },
        None => None,
    }
}

} // verus!
