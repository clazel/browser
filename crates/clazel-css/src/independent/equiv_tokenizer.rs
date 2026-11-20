//! The equivalence of the independent tokenizer ([`super`]) with the spec
//! ([`crate::tokenizer::spec`]). This is the only file of the independent
//! transcription's tokenizer that names the spec; see the header of
//! [`super`] for when it was written.
//!
//! The spec's input is `Seq<u32>` with the EOF code point 0x110000 past either end,
//! the independent one's is `Seq<int>` with EOF -1. [`ints`] is the one and [`cp`]
//! the other, [`valid`] is the precondition the spec itself states (the input is a
//! stream of code points, so no value is above U+10FFFF). The spec's tokens keep the
//! strings of a number, the independent ones its sign, mantissa, fraction length and
//! exponent: [`inum_of`] reads the second off the first, and [`tok_of`] maps a
//! token. So every theorem says: the mapped result of the spec is the independent
//! result. Positions are `int` in the spec and `nat` in the independent one.

#[cfg(verus_only)]
use super::equiv_base::*;
#[cfg(verus_only)]
use super::*;
#[cfg(verus_only)]
use crate::tokenizer::spec as t;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use super::equiv_base::lemma_at, super::equiv_base::lemma_class_digit, super::equiv_base::lemma_class_hex,
    super::equiv_base::lemma_class_ident_start, super::equiv_base::lemma_class_ident,
    super::equiv_base::lemma_class_non_printable, super::equiv_base::lemma_class_newline,
    super::equiv_base::lemma_class_whitespace, super::equiv_base::lemma_class_valid_escape,
    super::equiv_base::lemma_class_starts_ident, super::equiv_base::lemma_class_starts_number,
    super::equiv_base::lemma_class_starts_unicode_range, super::equiv_base::lemma_digit_value;

// ---------------------------------------------------------------------
// Numbers spelled in digits

/// 10^(n+1) and 16^(n+1) unfold.
pub proof fn lemma_pow_succ(base: nat, n: nat)
    ensures
        i_pow(base, n + 1) == base * i_pow(base, n),
{
}

/// A digit string splits at any point: `value(a..b) = value(a..m) * base^(b-m) + value(m..b)`.
pub proof fn lemma_value_split(s: Seq<int>, a: nat, m: nat, b: nat, base: nat)
    requires
        a <= m <= b,
    ensures
        i_value(s, a, b, base) == i_value(s, a, m, base) * i_pow(base, (b - m) as nat) + i_value(s, m, b, base),
    decreases b,
{
    if b > m {
        lemma_value_split(s, a, m, (b - 1) as nat, base);
        let k = (b - 1 - m) as nat;
        lemma_pow_succ(base, k);
        let va = i_value(s, a, m, base);
        let vm = i_value(s, m, (b - 1) as nat, base);
        let d = i_digit_value(i_at(s, (b - 1) as nat));
        let pk = i_pow(base, k);
        assert(i_value(s, a, b, base) == i_value(s, a, (b - 1) as nat, base) * base + d);
        assert(i_value(s, m, b, base) == vm * base + d);
        assert(i_pow(base, (b - m) as nat) == base * pk);
        assert(i_value(s, a, (b - 1) as nat, base) == va * pk + vm);
        assert((va * pk + vm) * base + d == va * (base * pk) + (vm * base + d)) by (nonlinear_arith);
        assert(i_value(s, a, b, base) == va * i_pow(base, (b - m) as nat) + i_value(s, m, b, base));
    } else {
        assert(m == b);
        assert(i_pow(base, 0) == 1);
        assert(i_value(s, m, m, base) == 0);
        assert(i_value(s, a, m, base) * 1 == i_value(s, a, m, base)) by (nonlinear_arith);
        assert(i_value(s, a, b, base) == i_value(s, a, m, base) * i_pow(base, (b - m) as nat) + i_value(s, m, b, base));
    }
}

/// The value of the first digit, then the rest.
pub proof fn lemma_value_cons(s: Seq<int>, a: nat, b: nat, base: nat)
    requires
        a < b,
    ensures
        i_value(s, a, b, base) == i_digit_value(i_at(s, a)) * i_pow(base, (b - a - 1) as nat) + i_value(
            s,
            a + 1,
            b,
            base,
        ),
{
    lemma_value_split(s, a, a + 1, b, base);
    assert(i_value(s, a, a, base) == 0);
    assert(i_value(s, a, a + 1, base) == i_value(s, a, a, base) * base + i_digit_value(i_at(s, a)));
    assert(i_value(s, a, a + 1, base) == i_digit_value(i_at(s, a))) by (nonlinear_arith)
        requires
            i_value(s, a, a, base) == 0,
            i_value(s, a, a + 1, base) == i_value(s, a, a, base) * base + i_digit_value(i_at(s, a)),
    ;
    assert((b - (a + 1)) as nat == (b - a - 1) as nat);
}


// ---------------------------------------------------------------------
// Runs and comments

/// "Consume comments": the end of one comment.
pub proof fn lemma_comment_end(s: Seq<u32>, q: nat)
    requires
        valid(s),
    ensures
        t::end_of_comment(s, q as int) == (q + i_comment_body_len(ints(s), q)) as int,
    decreases t::remaining(s, q as int),
{
    if q < s.len() && !(t::at(s, q as int) == 0x2A && t::at(s, q as int + 1) == 0x2F) {
        lemma_comment_end(s, q + 1);
    }
}

/// §4.3.2 "consume comments".
pub proof fn theorem_comments_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        t::consume_comments(s, p as int) == i_consume_comments(ints(s), p) as int,
    decreases t::remaining(s, p as int),
{
    if t::at(s, p as int) == 0x2F && t::at(s, p as int + 1) == 0x2A {
        lemma_comment_end(s, p + 2);
        let n = 2 + i_comment_body_len(ints(s), p + 2);
        theorem_comments_equal(s, p + n);
        assert(i_consume_comments(ints(s), p) == p + n + i_comments_len(ints(s), p + n));
    }
}

/// "Consume as much whitespace as possible".
pub proof fn lemma_whitespace_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        t::consume_whitespace(s, p as int) == i_whitespace_end(ints(s), p) as int,
    decreases t::remaining(s, p as int),
{
    if t::is_whitespace(t::at(s, p as int)) {
        lemma_whitespace_equal(s, p + 1);
    }
}

/// "While the next two input code points are whitespace, consume the next input code
/// point."
pub proof fn lemma_whitespace_but_one_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        t::consume_whitespace_but_one(s, p as int) == i_skip_double_whitespace(ints(s), p) as int,
    decreases t::remaining(s, p as int),
{
    if t::is_whitespace(t::at(s, p as int)) && t::is_whitespace(t::at(s, p as int + 1)) {
        lemma_whitespace_but_one_equal(s, p + 1);
    }
}

/// The value of a string of digits, and how the independent one reads them.
pub proof fn lemma_digits_value_fold(x: Seq<u32>, y: Seq<u32>, v: nat)
    ensures
        t::digits_value(x + y, v) == t::digits_value(y, t::digits_value(x, v)),
    decreases x.len(),
{
    if x.len() > 0 {
        let xs = x.drop_first();
        assert((x + y).drop_first() =~= xs + y);
        assert((x + y)[0] == x[0]);
        lemma_digits_value_fold(xs, y, v * 10 + (x[0] - 0x30) as nat);
    } else {
        assert(x + y =~= y);
    }
}

/// `digits_value(d, v) = v * 10^|d| + digits_value(d, 0)`.
pub proof fn lemma_digits_value_shift(d: Seq<u32>, v: nat)
    ensures
        t::digits_value(d, v) == v * t::power_of_ten(d.len()) + t::digits_value(d, 0),
    decreases d.len(),
{
    if d.len() > 0 {
        let rest = d.drop_first();
        let c = (d[0] - 0x30) as nat;
        lemma_digits_value_shift(rest, v * 10 + c);
        lemma_digits_value_shift(rest, c);
        let pr = t::power_of_ten(rest.len());
        assert(t::power_of_ten(d.len()) == 10 * pr);
        let dv = t::digits_value(rest, 0);
        assert(t::digits_value(d, v) == t::digits_value(rest, v * 10 + c));
        assert(t::digits_value(d, 0) == t::digits_value(rest, c)) by {
            assert(0 * 10 + c == c);
        }
        assert((v * 10 + c) * pr + dv == v * (10 * pr) + (c * pr + dv)) by (nonlinear_arith);
        assert(t::digits_value(rest, c) == c * pr + dv);
    } else {
        assert(t::digits_value(d, v) == v);
        assert(t::power_of_ten(0) == 1);
        assert(t::digits_value(d, 0) == 0);
        assert(v * 1 == v) by (nonlinear_arith);
    }
}


// ---------------------------------------------------------------------
// Strings of the spec as strings of the independent transcription

/// `ints` of a concatenation.
pub proof fn lemma_ints_add(x: Seq<u32>, y: Seq<u32>)
    ensures
        ints(x + y) =~= ints(x) + ints(y),
{
}

/// `ints` of a push.
pub proof fn lemma_ints_push(x: Seq<u32>, c: u32)
    ensures
        ints(x.push(c)) =~= ints(x).push(c as int),
{
}

/// `ints` of a part of a string.
pub proof fn lemma_ints_subrange(x: Seq<u32>, a: int, b: int)
    requires
        0 <= a <= b <= x.len(),
    ensures
        ints(x.subrange(a, b)) =~= ints(x).subrange(a, b),
{
}

// ---------------------------------------------------------------------
// Digits and hex digits

/// "While the next input code point is a digit, consume it and append it to": the
/// digits are a run, the spec appends it, the independent one gives its end.
pub proof fn lemma_digits_equal(s: Seq<u32>, p: nat, part: Seq<u32>)
    requires
        valid(s),
    ensures
        t::consume_digits(s, p as int, part).1 == i_digits_end(ints(s), p) as int,
        p <= s.len() ==> t::consume_digits(s, p as int, part).0 =~= part + s.subrange(
            p as int,
            i_digits_end(ints(s), p) as int,
        ),
        i_digits_end(ints(s), p) >= p,
        p <= s.len() ==> i_digits_end(ints(s), p) <= s.len(),
        i_digits_end(ints(s), p) > p ==> t::is_digit(t::at(s, p as int)),
        t::is_digit(t::at(s, p as int)) ==> i_digits_end(ints(s), p) > p,
        forall|k: nat| p <= k < i_digits_end(ints(s), p) ==> t::is_digit(t::at(s, k as int)),
    decreases t::remaining(s, p as int),
{
    if t::is_digit(t::at(s, p as int)) {
        lemma_digits_equal(s, p + 1, part.push(t::at(s, p as int)));
        let e = i_digits_end(ints(s), p + 1);
        if p + 1 <= s.len() {
            assert(e >= p + 1 && e <= s.len());
            assert(part.push(s[p as int]) + s.subrange(p as int + 1, e as int) =~= part + s.subrange(p as int, e as int));
        }
    }
}

/// "Consume as many hex digits as possible, but no more than `limit`".
pub proof fn lemma_hex_equal(s: Seq<u32>, p: nat, limit: nat, value: nat)
    requires
        valid(s),
    ensures
        ({
            let k = i_hex_run(ints(s), p, limit);
            &&& t::consume_hex_digits(s, p as int, limit, value).1 == (p + k) as int
            &&& t::consume_hex_digits(s, p as int, limit, value).0 == value * i_pow(16, k) + i_value(
                ints(s),
                p,
                p + k,
                16,
            )
            &&& k <= limit
            &&& forall|j: nat| p <= j < p + k ==> t::is_hex_digit(t::at(s, j as int))
        }),
    decreases limit,
{
    let c = t::at(s, p as int);
    if limit > 0 && t::is_hex_digit(c) {
        let v2 = value * 16 + t::hex_value(c);
        lemma_hex_equal(s, p + 1, (limit - 1) as nat, v2);
        let k1 = i_hex_run(ints(s), p + 1, (limit - 1) as nat);
        let k = 1 + k1;
        assert(i_hex_run(ints(s), p, limit) == k);
        lemma_value_cons(ints(s), p, p + k, 16);
        lemma_pow_succ(16, k1);
        assert(i_digit_value(i_at(ints(s), p)) == t::hex_value(c));
        let pk = i_pow(16, k1);
        let vv = i_value(ints(s), p + 1, p + 1 + k1, 16);
        assert((value * 16 + t::hex_value(c)) * pk + vv == value * (16 * pk) + (t::hex_value(c) * pk + vv))
            by (nonlinear_arith);
        assert(forall|j: nat| p <= j < p + k ==> t::is_hex_digit(t::at(s, j as int))) by {
            assert forall|j: nat| p <= j < p + k implies t::is_hex_digit(t::at(s, j as int)) by {
                if j > p {
                    assert(p + 1 <= j < p + 1 + k1);
                }
            }
        }
    } else {
        assert(i_pow(16, 0) == 1);
        assert(i_value(ints(s), p, p, 16) == 0);
        assert(value * 1 == value) by (nonlinear_arith);
    }
}

/// "Consume as many U+003F QUESTION MARK (?) code points as possible, but no more than".
pub proof fn lemma_question_equal(s: Seq<u32>, p: nat, limit: nat)
    requires
        valid(s),
    ensures
        t::consume_question_marks(s, p as int, limit) == i_question_run(ints(s), p, limit),
    decreases limit,
{
    if limit > 0 && t::at(s, p as int) == 0x3F {
        lemma_question_equal(s, p + 1, (limit - 1) as nat);
    }
}

// ---------------------------------------------------------------------
// §4.3.7 Consume an escaped code point

/// §4.3.7 "consume an escaped code point".
pub proof fn theorem_escaped_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        cp(t::consume_escaped_code_point(s, p as int).0) == i_consume_escaped(ints(s), p).0,
        t::consume_escaped_code_point(s, p as int).1 == i_consume_escaped(ints(s), p).1 as int,
        i_consume_escaped(ints(s), p).1 >= p,
        i_consume_escaped(ints(s), p).0 >= 0,
        t::consume_escaped_code_point(s, p as int).0 <= 0x10FFFF,
{
    let c = t::at(s, p as int);
    if t::is_hex_digit(c) {
        lemma_hex_equal(s, p + 1, 5, t::hex_value(c));
        let k = i_hex_run(ints(s), p + 1, 5);
        lemma_value_cons(ints(s), p, p + 1 + k, 16);
        assert(i_digit_value(i_at(ints(s), p)) == t::hex_value(c));
    }
}


// ---------------------------------------------------------------------
// §4.3.11 Consume an ident sequence

/// The loop of §4.3.11, which appends to `result`.
pub proof fn lemma_name_loop_equal(s: Seq<u32>, p: nat, result: Seq<u32>)
    requires
        valid(s),
    ensures
        ints(t::consume_ident_sequence_loop(s, p as int, result).0) =~= ints(result) + i_consume_name(
            ints(s),
            p,
        ).0,
        t::consume_ident_sequence_loop(s, p as int, result).1 == i_consume_name(ints(s), p).1 as int,
        i_consume_name(ints(s), p).1 >= p,
        (i_ident(i_at(ints(s), p)) || i_valid_escape(i_at(ints(s), p), i_at(ints(s), p + 1))) ==> i_consume_name(
            ints(s),
            p,
        ).1 > p,
    decreases t::remaining(s, p as int),
{
    let c = t::at(s, p as int);
    if t::is_ident_code_point(c) {
        lemma_name_loop_equal(s, p + 1, result.push(c));
        lemma_ints_push(result, c);
    } else if t::are_a_valid_escape(c, t::at(s, p as int + 1)) {
        theorem_escaped_equal(s, p + 1);
        crate::tokenizer::termination::lemma_escape_advances(s, p as int + 1);
        let (code_point, next) = t::consume_escaped_code_point(s, p as int + 1);
        lemma_name_loop_equal(s, next as nat, result.push(code_point));
        lemma_ints_push(result, code_point);
    }
}

/// §4.3.11 "consume an ident sequence".
pub proof fn theorem_name_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        ints(t::consume_ident_sequence(s, p as int).0) =~= i_consume_name(ints(s), p).0,
        t::consume_ident_sequence(s, p as int).1 == i_consume_name(ints(s), p).1 as int,
{
    lemma_name_loop_equal(s, p, Seq::empty());
    assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
}

// ---------------------------------------------------------------------
// §4.3.12 Consume a number

/// The digits of `s[a..b)` are the number the independent value function gives.
pub proof fn lemma_digits_value_of_range(s: Seq<u32>, a: nat, b: nat)
    requires
        valid(s),
        a <= b <= s.len(),
        forall|k: nat| a <= k < b ==> t::is_digit(t::at(s, k as int)),
    ensures
        t::digits_value(s.subrange(a as int, b as int), 0) == i_value(ints(s), a, b, 10),
    decreases b,
{
    if b > a {
        lemma_digits_value_of_range(s, a, (b - 1) as nat);
        let x = s.subrange(a as int, b as int - 1);
        let d = s[b as int - 1];
        assert(s.subrange(a as int, b as int) =~= x.push(d));
        assert(x.push(d) =~= x + seq![d]);
        lemma_digits_value_fold(x, seq![d], 0);
        assert(seq![d].drop_first() =~= Seq::<u32>::empty());
        reveal_with_fuel(t::digits_value, 2);
        assert(t::digits_value(seq![d], t::digits_value(x, 0)) == t::digits_value(x, 0) * 10 + (d - 0x30) as nat);
        assert(i_value(ints(s), a, b, 10) == i_value(ints(s), a, (b - 1) as nat, 10) * 10 + i_digit_value(
            i_at(ints(s), (b - 1) as nat),
        ));
        assert(i_digit_value(i_at(ints(s), (b - 1) as nat)) == (d - 0x30) as nat);
    } else {
        assert(s.subrange(a as int, b as int) =~= Seq::<u32>::empty());
    }
}

/// "The position of '.' in `part`": the first one.
pub proof fn lemma_point_of(part: Seq<u32>, i: nat, j: nat)
    requires
        i <= j <= part.len(),
        forall|k: int| i <= k < j ==> part[k] != 0x2E,
        j == part.len() || part[j as int] == 0x2E,
    ensures
        t::point_of(part, i) == j,
    decreases j - i,
{
    if i < j {
        lemma_point_of(part, i + 1, j);
    }
}

/// `digits_value` of two digit strings spelled one after the other.
pub proof fn lemma_digits_value_concat(x: Seq<u32>, y: Seq<u32>)
    ensures
        t::digits_value(x + y, 0) == t::digits_value(x, 0) * t::power_of_ten(y.len()) + t::digits_value(y, 0),
{
    lemma_digits_value_fold(x, y, 0);
    lemma_digits_value_shift(y, t::digits_value(x, 0));
}

/// "power_of_ten" is the independent power.
pub proof fn lemma_power_of_ten(n: nat)
    ensures
        t::power_of_ten(n) == i_pow(10, n),
    decreases n,
{
    if n > 0 {
        lemma_power_of_ten((n - 1) as nat);
    }
}

/// The code points after the point of a number part with its sign removed.
pub open spec fn num_fraction(part: Seq<u32>) -> Seq<u32> {
    let u = t::unsigned(part);
    let point = t::point_of(u, 0);
    if point < u.len() { u.subrange(point as int + 1, u.len() as int) } else { Seq::empty() }
}

/// "interpreting number part as a base-10 number": the digits, without the point.
pub open spec fn num_mantissa(part: Seq<u32>) -> nat {
    let u = t::unsigned(part);
    t::digits_value(u.subrange(0, t::point_of(u, 0) as int) + num_fraction(part), 0)
}

/// The exponent part as an integer: "interpret it as a base-10 integer".
pub open spec fn num_exponent(exponent_part: Seq<u32>) -> int {
    let magnitude = t::digits_value(t::unsigned(exponent_part), 0) as int;
    if exponent_part.len() == 0 {
        0
    } else if t::is_negative(exponent_part) {
        -magnitude
    } else {
        magnitude
    }
}

/// What the independent transcription reads off the spec's number.
pub open spec fn inum_of(n: t::Number) -> INum {
    INum {
        sign: match n.sign_character {
            None => ISign::NoSign,
            Some(c) => if c == 0x2B { ISign::Plus } else { ISign::Minus },
        },
        mantissa: num_mantissa(n.number_part),
        frac_len: num_fraction(n.number_part).len(),
        exponent: num_exponent(n.exponent_part),
    }
}

/// The exponent of §4.3.12 step 5, from the code point `c` at which it may start.
pub proof fn lemma_exponent_equal(s: Seq<u32>, c: nat)
    requires
        valid(s),
        c <= s.len(),
    ensures
        ({
            let e0 = t::at(s, c as int);
            let e1 = t::at(s, c as int + 1);
            let exp_signed = (e1 == 0x2B || e1 == 0x2D) && t::is_digit(t::at(s, c as int + 2));
            let has_exp = (e0 == 0x45 || e0 == 0x65) && (t::is_digit(e1) || exp_signed);
            let ds: nat = if exp_signed { c + 2 } else { c + 1 };
            let de = i_digits_end(ints(s), ds);
            let (exponent_part, has_exponent, end) = t::number_step_5(s, c as int);
            let value = i_value(ints(s), ds, de, 10) as int;
            &&& has_exponent == has_exp
            &&& end == (if has_exp { de } else { c }) as int
            &&& num_exponent(exponent_part) == (if !has_exp { 0 } else if e1 == 0x2D { -value } else { value })
        }),
{
    let e0 = t::at(s, c as int);
    let e1 = t::at(s, c as int + 1);
    let exp_signed = (e1 == 0x2B || e1 == 0x2D) && t::is_digit(t::at(s, c as int + 2));
    let has_exp = (e0 == 0x45 || e0 == 0x65) && (t::is_digit(e1) || exp_signed);
    let (exponent_part, has_exponent, end) = t::number_step_5(s, c as int);
    if has_exp {
        let ds: nat = if exp_signed { c + 2 } else { c + 1 };
        let start: Seq<u32> = if exp_signed { seq![e1] } else { Seq::empty() };
        assert(ds <= s.len() || !exp_signed);
        lemma_digits_equal(s, ds, start);
        let de = i_digits_end(ints(s), ds);
        assert(de > ds);
        assert(de <= s.len()) by {
            assert(ds <= s.len());
        }
        let digits_c = s.subrange(ds as int, de as int);
        assert(exponent_part =~= start + digits_c);
        assert(t::unsigned(exponent_part) =~= digits_c) by {
            if exp_signed {
                assert(exponent_part[0] == e1);
                assert(exponent_part.drop_first() =~= digits_c);
            } else {
                assert(exponent_part =~= digits_c);
                assert(exponent_part[0] == s[ds as int]);
                assert(t::is_digit(t::at(s, ds as int)));
            }
        }
        lemma_digits_value_of_range(s, ds, de);
        assert(exponent_part.len() > 0);
        assert(t::is_negative(exponent_part) == (exp_signed && e1 == 0x2D));
    } else {
        assert(exponent_part =~= Seq::<u32>::empty());
    }
}

/// Whether the number at `p` has a fraction, as [`i_consume_number`] has it.
pub open spec fn i_number_has_fraction(s: Seq<int>, p: nat) -> bool {
    let ch = i_at(s, p);
    let a = if ch == 0x2B || ch == 0x2D { p + 1 } else { p };
    let b = i_digits_end(s, a);
    i_at(s, b) == 0x2E && i_digit(i_at(s, b + 1))
}

/// The position after the fraction of the number at `p`, as [`i_consume_number`] has it.
pub open spec fn i_number_fraction_end(s: Seq<int>, p: nat) -> nat {
    let ch = i_at(s, p);
    let a = if ch == 0x2B || ch == 0x2D { p + 1 } else { p };
    let b = i_digits_end(s, a);
    if i_at(s, b) == 0x2E && i_digit(i_at(s, b + 1)) { i_digits_end(s, b + 1) } else { b }
}

/// The integer and fraction parts of §4.3.12 steps 2 to 4.
#[verifier::rlimit(200)]
pub proof fn lemma_integer_fraction_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
        p <= s.len(),
    ensures
        ({
            let (num, integer, e) = i_consume_number(ints(s), p);
            let (signed, sign_character, after_sign) = t::number_step_2(s, p as int);
            let (digits_part, after_integer) = t::consume_digits(s, after_sign, signed);
            let (number_part, no_fraction, after_fraction) = t::number_step_4(s, after_integer, digits_part);
            &&& 0 <= after_fraction <= s.len()
            &&& num_mantissa(number_part) == num.mantissa
            &&& num_fraction(number_part).len() == num.frac_len
            &&& (match sign_character {
                None => ISign::NoSign,
                Some(ch) => if ch == 0x2B { ISign::Plus } else { ISign::Minus },
            }) == num.sign
            &&& no_fraction == !i_number_has_fraction(ints(s), p)
            &&& after_fraction == i_number_fraction_end(ints(s), p) as int
        }),
{
    let ch = t::at(s, p as int);
    let has_sign = ch == 0x2B || ch == 0x2D;
    let a: nat = if has_sign { p + 1 } else { p };
    let (signed, sign_character, after_sign) = t::number_step_2(s, p as int);
    assert(after_sign == a as int);
    lemma_digits_equal(s, a, signed);
    let b = i_digits_end(ints(s), a);
    let (integer, after_integer) = t::consume_digits(s, after_sign, signed);
    assert(after_integer == b as int);
    let digits_a = s.subrange(a as int, b as int);
    assert(integer =~= signed + digits_a);
    let has_frac = t::at(s, b as int) == 0x2E && t::is_digit(t::at(s, b as int + 1));
    let (number_part, no_fraction, after_fraction) = t::number_step_4(s, after_integer, integer);
    assert(no_fraction == !has_frac);
    let c: nat = if has_frac { i_digits_end(ints(s), b + 1) } else { b };
    if has_frac {
        lemma_digits_equal(s, b + 1, integer.push(0x2E));
        assert(c <= s.len());
    }
    assert(after_fraction == c as int);
    let digits_b = if has_frac { s.subrange(b as int + 1, c as int) } else { Seq::<u32>::empty() };
    assert(number_part =~= if has_frac { integer.push(0x2E) + digits_b } else { integer });
    let unsigned_part = t::unsigned(number_part);
    let body = if has_frac { digits_a.push(0x2E) + digits_b } else { digits_a };
    assert(unsigned_part =~= body) by {
        if has_sign {
            assert(signed =~= seq![ch]);
            assert(number_part[0] == ch);
            assert(number_part.drop_first() =~= body);
        } else {
            assert(signed =~= Seq::<u32>::empty());
            assert(number_part =~= body);
            if number_part.len() > 0 {
                assert(number_part[0] != 0x2B && number_part[0] != 0x2D) by {
                    if b > a {
                        assert(number_part[0] == s[a as int]);
                        assert(t::is_digit(t::at(s, a as int)));
                    } else {
                        assert(number_part[0] == 0x2E);
                    }
                }
            }
        }
    }
    assert(forall|k: int| 0 <= k < digits_a.len() ==> unsigned_part[k] != 0x2E) by {
        assert forall|k: int| 0 <= k < digits_a.len() implies unsigned_part[k] != 0x2E by {
            assert(unsigned_part[k] == s[a as int + k]);
            assert(t::is_digit(t::at(s, (a as int + k))));
        }
    }
    lemma_point_of(unsigned_part, 0, digits_a.len());
    let point = t::point_of(unsigned_part, 0);
    assert(point == digits_a.len());
    let fraction = if point < unsigned_part.len() {
        unsigned_part.subrange(point as int + 1, unsigned_part.len() as int)
    } else {
        Seq::empty()
    };
    assert(fraction =~= digits_b);
    assert(unsigned_part.subrange(0, point as int) =~= digits_a);
    lemma_digits_value_of_range(s, a, b);
    if has_frac {
        lemma_digits_value_of_range(s, b + 1, c);
        lemma_digits_value_concat(digits_a, digits_b);
        lemma_power_of_ten(digits_b.len());
    } else {
        assert(digits_a + digits_b =~= digits_a);
        assert(t::digits_value(Seq::<u32>::empty(), 0) == 0);
    }
}


/// §4.3.12 "consume a number".
pub proof fn theorem_number_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
        p <= s.len(),
    ensures
        inum_of(t::consume_a_number(s, p as int).0) == i_consume_number(ints(s), p).0,
        t::consume_a_number(s, p as int).0.is_integer == i_consume_number(ints(s), p).1,
        t::consume_a_number(s, p as int).1 == i_consume_number(ints(s), p).2 as int,
{
    lemma_integer_fraction_equal(s, p);
    let c = i_number_fraction_end(ints(s), p);
    lemma_exponent_equal(s, c);
}


// ---------------------------------------------------------------------
// Tokens

/// The independent transcription's token for a token of the spec.
pub open spec fn tok_of(tk: t::Token) -> ITok {
    match tk {
        t::Token::Ident { value } => ITok::Ident(ints(value)),
        t::Token::Function { value } => ITok::Function(ints(value)),
        t::Token::AtKeyword { value } => ITok::AtKeyword(ints(value)),
        t::Token::Hash { value, is_id } => ITok::Hash(ints(value), is_id),
        t::Token::String { value } => ITok::Str(ints(value)),
        t::Token::BadString => ITok::BadStr,
        t::Token::Url { value } => ITok::Url(ints(value)),
        t::Token::BadUrl => ITok::BadUrl,
        t::Token::Delim { value } => ITok::Delim(value as int),
        t::Token::Number { number } => ITok::Number(inum_of(number), number.is_integer),
        t::Token::Percentage { number } => ITok::Percentage(inum_of(number)),
        t::Token::Dimension { number, unit } => ITok::Dimension(inum_of(number), number.is_integer, ints(unit)),
        t::Token::UnicodeRange { start, end } => ITok::UnicodeRange(start as int, end as int),
        t::Token::Whitespace => ITok::Whitespace,
        t::Token::Cdo => ITok::Cdo,
        t::Token::Cdc => ITok::Cdc,
        t::Token::Colon => ITok::Colon,
        t::Token::Semicolon => ITok::Semicolon,
        t::Token::Comma => ITok::Comma,
        t::Token::OpenSquare => ITok::OpenSquare,
        t::Token::CloseSquare => ITok::CloseSquare,
        t::Token::OpenParen => ITok::OpenParen,
        t::Token::CloseParen => ITok::CloseParen,
        t::Token::OpenCurly => ITok::OpenCurly,
        t::Token::CloseCurly => ITok::CloseCurly,
        t::Token::Eof => ITok::Eof,
    }
}

/// §4.3.3 "consume a numeric token".
pub proof fn theorem_numeric_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
        p <= s.len(),
    ensures
        tok_of(t::consume_a_numeric_token(s, p as int).0) == i_consume_numeric(ints(s), p).0,
        t::consume_a_numeric_token(s, p as int).1 == i_consume_numeric(ints(s), p).1 as int,
{
    theorem_number_equal(s, p);
    let (number, after) = t::consume_a_number(s, p as int);
    theorem_name_equal(s, after as nat);
}

// ---------------------------------------------------------------------
// §4.3.5 Consume a string token

/// The loop of §4.3.5, which appends to `value`.
pub proof fn lemma_string_loop_equal(s: Seq<u32>, p: nat, ending: u32, value: Seq<u32>)
    requires
        valid(s),
        ending <= 0x10FFFF,
    ensures
        ({
            let (v, bad, e) = i_consume_string(ints(s), p, ending as int);
            &&& tok_of(t::consume_string_loop(s, p as int, ending, value).0) == (if bad {
                ITok::BadStr
            } else {
                ITok::Str(ints(value) + v)
            })
            &&& t::consume_string_loop(s, p as int, ending, value).1 == e as int
        }),
    decreases t::remaining(s, p as int),
{
    let c = t::at(s, p as int);
    if c == ending || c == t::EOF || t::is_newline(c) {
    } else if c == 0x5C {
        if t::at(s, p as int + 1) == t::EOF {
            lemma_string_loop_equal(s, p + 1, ending, value);
        } else if t::is_newline(t::at(s, p as int + 1)) {
            lemma_string_loop_equal(s, p + 2, ending, value);
        } else {
            theorem_escaped_equal(s, p + 1);
            crate::tokenizer::termination::lemma_escape_advances(s, p as int + 1);
            let (code_point, next) = t::consume_escaped_code_point(s, p as int + 1);
            lemma_string_loop_equal(s, next as nat, ending, value.push(code_point));
            lemma_ints_push(value, code_point);
            let (v, bad, e) = i_consume_string(ints(s), p, ending as int);
            let esc = i_consume_escaped(ints(s), p + 1);
            let rest = i_consume_string(ints(s), fwd(p, esc.1), ending as int);
            assert(fwd(p, esc.1) == esc.1);
            assert(ints(value.push(code_point)) + rest.0 =~= ints(value) + (seq![esc.0] + rest.0));
        }
    } else {
        lemma_string_loop_equal(s, p + 1, ending, value.push(c));
        lemma_ints_push(value, c);
        let rest = i_consume_string(ints(s), p + 1, ending as int);
        assert(ints(value.push(c)) + rest.0 =~= ints(value) + (seq![c as int] + rest.0));
    }
}

/// §4.3.5 "consume a string token".
pub proof fn theorem_string_equal(s: Seq<u32>, p: nat, ending: u32)
    requires
        valid(s),
        ending <= 0x10FFFF,
    ensures
        ({
            let (v, bad, e) = i_consume_string(ints(s), p, ending as int);
            &&& tok_of(t::consume_a_string_token(s, p as int, ending).0) == (if bad { ITok::BadStr } else {
                ITok::Str(v)
            })
            &&& t::consume_a_string_token(s, p as int, ending).1 == e as int
        }),
{
    lemma_string_loop_equal(s, p, ending, Seq::empty());
    assert(ints(Seq::<u32>::empty()) + i_consume_string(ints(s), p, ending as int).0 =~= i_consume_string(
        ints(s),
        p,
        ending as int,
    ).0);
}

// ---------------------------------------------------------------------
// §4.3.14 and §4.3.6: bad urls and urls

/// §4.3.14 "consume the remnants of a bad url".
pub proof fn theorem_bad_url_remnants_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        t::consume_remnants_of_a_bad_url(s, p as int) == i_consume_bad_url_remnants(ints(s), p) as int,
    decreases t::remaining(s, p as int),
{
    let c = t::at(s, p as int);
    if c != 0x29 && c != t::EOF {
        if t::are_a_valid_escape(c, t::at(s, p as int + 1)) {
            theorem_escaped_equal(s, p + 1);
            crate::tokenizer::termination::lemma_escape_advances(s, p as int + 1);
            let (_, next) = t::consume_escaped_code_point(s, p as int + 1);
            theorem_bad_url_remnants_equal(s, next as nat);
        } else {
            theorem_bad_url_remnants_equal(s, p + 1);
        }
    }
}

/// The loop of §4.3.6, which appends to `value`.
pub proof fn lemma_url_loop_equal(s: Seq<u32>, p: nat, value: Seq<u32>)
    requires
        valid(s),
    ensures
        tok_of(t::consume_url_loop(s, p as int, value).0) == i_consume_url_rest(ints(s), p, ints(value)).0,
        t::consume_url_loop(s, p as int, value).1 == i_consume_url_rest(ints(s), p, ints(value)).1 as int,
    decreases t::remaining(s, p as int),
{
    let c = t::at(s, p as int);
    if c == 0x29 || c == t::EOF {
    } else if t::is_whitespace(c) {
        lemma_whitespace_equal(s, p + 1);
        let after = t::consume_whitespace(s, p as int + 1);
        theorem_bad_url_remnants_equal(s, after as nat);
        assert(i_whitespace_end(ints(s), p) == i_whitespace_end(ints(s), p + 1));
    } else if c == 0x22 || c == 0x27 || c == 0x28 || t::is_non_printable_code_point(c) {
        theorem_bad_url_remnants_equal(s, p + 1);
    } else if c == 0x5C {
        if t::are_a_valid_escape(c, t::at(s, p as int + 1)) {
            theorem_escaped_equal(s, p + 1);
            crate::tokenizer::termination::lemma_escape_advances(s, p as int + 1);
            let (code_point, next) = t::consume_escaped_code_point(s, p as int + 1);
            lemma_url_loop_equal(s, next as nat, value.push(code_point));
            lemma_ints_push(value, code_point);
            let esc = i_consume_escaped(ints(s), p + 1);
            assert(fwd(p, esc.1) == esc.1);
            assert(ints(value.push(code_point)) == ints(value) + seq![esc.0]);
        } else {
            theorem_bad_url_remnants_equal(s, p + 1);
        }
    } else {
        lemma_url_loop_equal(s, p + 1, value.push(c));
        lemma_ints_push(value, c);
        assert(ints(value.push(c)) == ints(value) + seq![c as int]);
    }
}

/// §4.3.6 "consume a url token".
pub proof fn theorem_url_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        tok_of(t::consume_a_url_token(s, p as int).0) == i_consume_url(ints(s), p).0,
        t::consume_a_url_token(s, p as int).1 == i_consume_url(ints(s), p).1 as int,
{
    lemma_whitespace_equal(s, p);
    crate::tokenizer::termination::lemma_whitespace_advances(s, p as int);
    lemma_url_loop_equal(s, i_whitespace_end(ints(s), p), Seq::empty());
    assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
}

// ---------------------------------------------------------------------
// §4.3.4 Consume an ident-like token

/// "an ASCII case-insensitive match for "url"".
pub proof fn lemma_is_url(x: Seq<u32>)
    ensures
        t::is_url(x) == i_ci_match(ints(x), seq![0x75 as int, 0x72, 0x6C]),
{
    let lower = seq![0x75 as int, 0x72, 0x6C];
    if x.len() == 3 {
        assert(ints(x).len() == 3);
        assert(i_ci_match(ints(x), lower) == (i_ascii_lower(x[0] as int) == 0x75 && i_ascii_lower(x[1] as int) == 0x72
            && i_ascii_lower(x[2] as int) == 0x6C)) by {
            assert(forall|k: int| 0 <= k < 3 ==> ints(x)[k] == x[k] as int);
        }
    }
}

/// §4.3.4 "consume an ident-like token".
pub proof fn theorem_ident_like_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        tok_of(t::consume_an_ident_like_token(s, p as int).0) == i_consume_ident_like(ints(s), p).0,
        t::consume_an_ident_like_token(s, p as int).1 == i_consume_ident_like(ints(s), p).1 as int,
{
    theorem_name_equal(s, p);
    let (string, after) = t::consume_ident_sequence(s, p as int);
    lemma_is_url(string);
    if t::is_url(string) && t::at(s, after) == 0x28 {
        lemma_whitespace_but_one_equal(s, after as nat + 1);
        let next = t::consume_whitespace_but_one(s, after + 1);
        crate::tokenizer::termination::lemma_whitespace_but_one_advances(s, after + 1);
        theorem_url_equal(s, next as nat);
    }
}

// ---------------------------------------------------------------------
// §4.3.13 Consume a unicode-range token

/// "Replace the question marks ... with" a digit, and "interpret the result as a
/// hexadecimal number".
pub proof fn lemma_with_digits(v: nat, n: nat)
    ensures
        t::with_digits(v, n, 0) == v * i_pow(16, n),
        t::with_digits(v, n, 15) == v * i_pow(16, n) + i_pow(16, n) - 1,
    decreases n,
{
    if n > 0 {
        let k = (n - 1) as nat;
        lemma_with_digits(v * 16, k);
        lemma_with_digits(v * 16 + 15, k);
        lemma_pow_succ(16, k);
        let pk = i_pow(16, k);
        assert(v * 16 * pk == v * (16 * pk)) by (nonlinear_arith);
        assert((v * 16 + 15) * pk + pk - 1 == v * (16 * pk) + 16 * pk - 1) by (nonlinear_arith);
    } else {
        assert(i_pow(16, 0) == 1);
        assert(v * 1 == v) by (nonlinear_arith);
    }
}

/// §4.3.13 "consume a unicode-range token".
pub proof fn theorem_unicode_range_equal(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        tok_of(t::consume_a_unicode_range_token(s, p as int).0) == i_consume_unicode_range(ints(s), p).0,
        t::consume_a_unicode_range_token(s, p as int).1 == i_consume_unicode_range(ints(s), p).1 as int,
{
    let a = p + 2;
    lemma_hex_equal(s, a, 6, 0);
    let digits = i_hex_run(ints(s), a, 6);
    let first = i_value(ints(s), a, a + digits, 16);
    assert(0 * i_pow(16, digits) == 0) by (nonlinear_arith);
    if digits < 6 {
        lemma_question_equal(s, a + digits, (6 - digits) as nat);
    }
    let questions = if digits < 6 { i_question_run(ints(s), a + digits, (6 - digits) as nat) } else { 0 };
    let marks = t::consume_question_marks(s, a as int + digits, (6 - digits) as nat);
    if questions > 0 {
        lemma_with_digits(first, questions);
    } else {
        let first_end = a + digits + questions;
        if t::at(s, first_end as int) == 0x2D && t::is_hex_digit(t::at(s, first_end as int + 1)) {
            lemma_hex_equal(s, first_end + 1, 6, 0);
            let more = i_hex_run(ints(s), first_end + 1, 6);
            assert(0 * i_pow(16, more) == 0) by (nonlinear_arith);
        }
    }
}


// ---------------------------------------------------------------------
// §4.3.1 Consume a token

/// A comment does not run past the end.
pub proof fn lemma_comment_body_bound(s: Seq<int>, q: nat)
    requires
        q <= s.len(),
    ensures
        q + i_comment_body_len(s, q) <= s.len(),
    decreases (if s.len() > q { s.len() - q } else { 0 }),
{
    if q < s.len() {
        if !(s[q as int] == 0x2A && i_at(s, q + 1) == 0x2F) {
            lemma_comment_body_bound(s, q + 1);
        }
    }
}

/// "Consume comments" stays within the stream and does not go back.
pub proof fn lemma_comments_bound(s: Seq<int>, p: nat)
    requires
        p <= s.len(),
    ensures
        p <= i_consume_comments(s, p) <= s.len(),
    decreases (if s.len() > p { s.len() - p } else { 0 }),
{
    if i_at(s, p) == 0x2F && i_at(s, p + 1) == 0x2A {
        lemma_comment_body_bound(s, p + 2);
        let n = 2 + i_comment_body_len(s, p + 2);
        lemma_comments_bound(s, p + n);
    }
}

/// Consuming comments twice is consuming them once.
pub proof fn lemma_comments_idempotent(s: Seq<u32>, p: nat)
    ensures
        t::consume_comments(s, t::consume_comments(s, p as int)) == t::consume_comments(s, p as int),
    decreases t::remaining(s, p as int),
{
    if t::at(s, p as int) == 0x2F && t::at(s, p as int + 1) == 0x2A {
        crate::tokenizer::termination::lemma_end_of_comment_advances(s, p as int + 2);
        let e = t::end_of_comment(s, p as int + 2);
        assert(e >= p as int + 2);
        lemma_comments_idempotent(s, e as nat);
    }
}

/// §4.3.1 "consume a token": its first step is "consume comments", and then the
/// independent transcription's [`i_consume_token`] takes over.
#[verifier::spinoff_prover]
#[verifier::rlimit(400)]
pub proof fn theorem_token_equal(s: Seq<u32>, p: nat, unicode_ranges_allowed: bool)
    requires
        valid(s),
    ensures
        ({
            let q = i_consume_comments(ints(s), p);
            &&& tok_of(t::consume_a_token(s, p as int, unicode_ranges_allowed).0) == i_consume_token(
                ints(s),
                q,
                unicode_ranges_allowed,
            ).0
            &&& t::consume_a_token(s, p as int, unicode_ranges_allowed).1 == i_consume_token(
                ints(s),
                q,
                unicode_ranges_allowed,
            ).1 as int
        }),
{
    theorem_comments_equal(s, p);
    if p <= s.len() {
        lemma_comments_bound(ints(s), p);
        let q = i_consume_comments(ints(s), p);
        let c = t::at(s, q as int);
        theorem_name_equal(s, q + 1);
        theorem_numeric_equal(s, q);
        theorem_ident_like_equal(s, q);
        theorem_unicode_range_equal(s, q);
        if c == 0x22 || c == 0x27 {
            theorem_string_equal(s, q + 1, c);
        }
        lemma_whitespace_equal(s, q + 1);
    }
}

// ---------------------------------------------------------------------
// §4 Tokenize

/// The tokens of the independent transcription.
pub open spec fn toks_of(lexes: Seq<Lex>) -> Seq<ITok> {
    Seq::new(lexes.len(), |i: int| lexes[i].tok)
}

/// The tokens of the spec as the independent transcription's.
pub open spec fn tok_seq_of(tokens: Seq<t::Token>) -> Seq<ITok> {
    Seq::new(tokens.len(), |i: int| tok_of(tokens[i]))
}

/// The loop of §4 "tokenize": what it has pushed, and then the tokens that the
/// independent transcription reads from `p` on, and the `<EOF-token>`.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub proof fn lemma_tokenize_loop_equal(s: Seq<u32>, p: nat, unicode_ranges_allowed: bool, tokens: Seq<t::Token>)
    requires
        valid(s),
    ensures
        tok_seq_of(t::tokenize_loop(s, p as int, unicode_ranges_allowed, tokens)) =~= tok_seq_of(tokens)
            + toks_of(i_tokenize_from(ints(s), p, unicode_ranges_allowed)) + seq![ITok::Eof],
    decreases t::remaining(s, p as int),
{
    theorem_token_equal(s, p, unicode_ranges_allowed);
    crate::tokenizer::termination::lemma_token_advances(s, p as int, unicode_ranges_allowed);
    let (token, next) = t::consume_a_token(s, p as int, unicode_ranges_allowed);
    let q = i_consume_comments(ints(s), p);
    let (tok, e) = i_consume_token(ints(s), q, unicode_ranges_allowed);
    if token is Eof {
        assert(tok == ITok::Eof);
        assert(tok_seq_of(tokens.push(token)) =~= tok_seq_of(tokens) + seq![ITok::Eof]);
        // Eof only for the EOF code point, which is at and past the end.
        assert(q >= s.len() || tok == ITok::Eof);
        assert(i_tokenize_from(ints(s), p, unicode_ranges_allowed) =~= Seq::<Lex>::empty());
    } else {
        assert(q < s.len());
        theorem_comments_equal(s, p);
        lemma_comments_idempotent(s, p);
        let current = t::consume_comments(s, p as int);
        assert(current == q as int);
        crate::tokenizer::termination::lemma_token_advances(s, current, unicode_ranges_allowed);
        assert(t::consume_a_token(s, current, unicode_ranges_allowed) == t::consume_a_token(s, p as int, unicode_ranges_allowed));
        assert(next > q as int);
        // The independent loop goes on at `fwd(q, e)`, which is `e`.
        assert(fwd(q, e) == e);
        crate::tokenizer::termination::lemma_comments_advance(s, p as int);
        lemma_tokenize_loop_equal(s, e, unicode_ranges_allowed, tokens.push(token));
        assert(tok_seq_of(tokens.push(token)) =~= tok_seq_of(tokens).push(tok));
        assert(i_tokenize_from(ints(s), p, unicode_ranges_allowed) =~= seq![Lex { tok, start: q, end: e }]
            + i_tokenize_from(ints(s), e, unicode_ranges_allowed));
    }
}


/// §4 "tokenize", with the `<EOF-token>` the spec pushes last.
pub proof fn theorem_tokenize_equals(s: Seq<u32>, unicode_ranges_allowed: bool)
    requires
        valid(s),
    ensures
        tok_seq_of(t::tokenize_with(s, unicode_ranges_allowed)) =~= toks_of(
            i_tokenize(ints(s), unicode_ranges_allowed),
        ) + seq![ITok::Eof],
{
    lemma_tokenize_loop_equal(s, 0, unicode_ranges_allowed, Seq::empty());
    assert(tok_seq_of(Seq::<t::Token>::empty()) =~= Seq::<ITok>::empty());
}

/// The positions the spec gives each token, as the independent transcription's
/// start and end.
pub proof fn lemma_spans_loop_equal(s: Seq<u32>, p: nat, unicode_ranges_allowed: bool, spans: Seq<crate::parser::spec::Span>)
    requires
        valid(s),
    ensures
        ({
            let result = crate::parser::spec::spans_loop(s, p as int, unicode_ranges_allowed, spans);
            let lexes = i_tokenize_from(ints(s), p, unicode_ranges_allowed);
            &&& result.len() == spans.len() + lexes.len() + 1
            &&& forall|i: int| 0 <= i < spans.len() ==> result[i] == spans[i]
            &&& forall|j: int|
                0 <= j < lexes.len() ==> result[spans.len() + j] == (crate::parser::spec::Span {
                    start: lexes[j].start as int,
                    end: lexes[j].end as int,
                })
        }),
    decreases t::remaining(s, p as int),
{
    theorem_token_equal(s, p, unicode_ranges_allowed);
    crate::tokenizer::termination::lemma_token_advances(s, p as int, unicode_ranges_allowed);
    theorem_comments_equal(s, p);
    let (token, next) = t::consume_a_token(s, p as int, unicode_ranges_allowed);
    let q = i_consume_comments(ints(s), p);
    let (tok, e) = i_consume_token(ints(s), q, unicode_ranges_allowed);
    let span = crate::parser::spec::Span { start: t::consume_comments(s, p as int), end: next };
    if token is Eof {
        assert(i_tokenize_from(ints(s), p, unicode_ranges_allowed) =~= Seq::<Lex>::empty());
    } else {
        lemma_comments_idempotent(s, p);
        crate::tokenizer::termination::lemma_token_advances(s, t::consume_comments(s, p as int), unicode_ranges_allowed);
        assert(fwd(q, e) == e);
        lemma_spans_loop_equal(s, e, unicode_ranges_allowed, spans.push(span));
        let lexes = i_tokenize_from(ints(s), p, unicode_ranges_allowed);
        assert(lexes =~= seq![Lex { tok, start: q, end: e }] + i_tokenize_from(ints(s), e, unicode_ranges_allowed));
    }
}

/// §3.3 "filter code points", for any string of code points.
pub proof fn lemma_filter_loop_equal(input: Seq<u32>, pos: nat, output: Seq<u32>)
    ensures
        ints(t::filter_loop(input, pos as int, output)) =~= ints(output) + i_filter_from(ints(input), pos),
    decreases t::remaining(input, pos as int),
{
    if pos < input.len() {
        let c = input[pos as int];
        if c == 0x0D && t::at(input, pos as int + 1) == 0x0A {
            lemma_filter_loop_equal(input, pos + 2, output.push(0x0A));
            lemma_ints_push(output, 0x0A);
        } else if c == 0x0D || c == 0x0C {
            lemma_filter_loop_equal(input, pos + 1, output.push(0x0A));
            lemma_ints_push(output, 0x0A);
        } else if c == 0 || t::is_surrogate(c as nat) {
            lemma_filter_loop_equal(input, pos + 1, output.push(t::REPLACEMENT));
            lemma_ints_push(output, t::REPLACEMENT);
        } else {
            lemma_filter_loop_equal(input, pos + 1, output.push(c));
            lemma_ints_push(output, c);
        }
    }
}

/// §3.3 "filter code points".
pub proof fn theorem_filter_equals(input: Seq<u32>)
    ensures
        ints(t::filter_code_points(input)) =~= i_filter(ints(input)),
{
    lemma_filter_loop_equal(input, 0, Seq::empty());
    assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
}

/// What filtering gives is a stream of code points, as the tokenizer needs.
pub proof fn lemma_filter_valid(input: Seq<u32>)
    requires
        forall|i: int| 0 <= i < input.len() ==> #[trigger] input[i] <= 0x10FFFF,
    ensures
        valid(t::filter_code_points(input)),
{
    lemma_filter_loop_valid(input, 0, Seq::empty());
}

/// The loop of "filter code points" gives code points when it is given them.
pub proof fn lemma_filter_loop_valid(input: Seq<u32>, pos: nat, output: Seq<u32>)
    requires
        forall|i: int| 0 <= i < input.len() ==> #[trigger] input[i] <= 0x10FFFF,
        valid(output),
    ensures
        valid(t::filter_loop(input, pos as int, output)),
    decreases t::remaining(input, pos as int),
{
    if pos < input.len() {
        let c = input[pos as int];
        if c == 0x0D && t::at(input, pos as int + 1) == 0x0A {
            lemma_filter_loop_valid(input, pos + 2, output.push(0x0A));
        } else if c == 0x0D || c == 0x0C {
            lemma_filter_loop_valid(input, pos + 1, output.push(0x0A));
        } else if c == 0 || t::is_surrogate(c as nat) {
            lemma_filter_loop_valid(input, pos + 1, output.push(t::REPLACEMENT));
        } else {
            lemma_filter_loop_valid(input, pos + 1, output.push(c));
        }
    }
}


/// Where the independent tokenizer's non-`<EOF-token>` token ends is after where it
/// started, and within the stream.
pub proof fn lemma_token_progress(s: Seq<u32>, p: nat, unicode_ranges_allowed: bool)
    requires
        valid(s),
        p <= s.len(),
    ensures
        ({
            let q = i_consume_comments(ints(s), p);
            let (tok, e) = i_consume_token(ints(s), q, unicode_ranges_allowed);
            &&& p <= q <= s.len()
            &&& tok != ITok::Eof ==> e > q && e <= s.len()
        }),
{
    theorem_token_equal(s, p, unicode_ranges_allowed);
    theorem_comments_equal(s, p);
    lemma_comments_bound(ints(s), p);
    lemma_comments_idempotent(s, p);
    let q = i_consume_comments(ints(s), p);
    let current = t::consume_comments(s, p as int);
    crate::tokenizer::termination::lemma_token_advances(s, current, unicode_ranges_allowed);
    assert(t::consume_a_token(s, current, unicode_ranges_allowed) == t::consume_a_token(s, p as int, unicode_ranges_allowed));
    super::equiv_bounds::lemma_token_bound(ints(s), q, unicode_ranges_allowed);
    assert(ints(s).len() == s.len());
    assert(super::equiv_bounds::nonneg(ints(s)));
}

/// The tokens of a stream lie within it, in order, and none is the `<EOF-token>`.
pub proof fn lemma_tokenize_wellformed(s: Seq<u32>, p: nat, unicode_ranges_allowed: bool)
    requires
        valid(s),
        p <= s.len(),
    ensures
        ({
            let lx = i_tokenize_from(ints(s), p, unicode_ranges_allowed);
            &&& forall|j: int| 0 <= j < lx.len() ==> #[trigger] lx[j].start <= lx[j].end && lx[j].end <= s.len()
            &&& forall|j: int| 0 <= j < lx.len() ==> p <= #[trigger] lx[j].start
            &&& forall|j: int| 0 <= j && j + 1 < lx.len() ==> #[trigger] lx[j].end <= lx[j + 1].start
            &&& forall|j: int| 0 <= j < lx.len() ==> #[trigger] lx[j].tok != ITok::Eof
        }),
    decreases s.len() - p,
{
    lemma_token_progress(s, p, unicode_ranges_allowed);
    let q = i_consume_comments(ints(s), p);
    let (tok, e) = i_consume_token(ints(s), q, unicode_ranges_allowed);
    if q >= s.len() || tok == ITok::Eof {
        assert(i_tokenize_from(ints(s), p, unicode_ranges_allowed) =~= Seq::<Lex>::empty());
    } else {
        assert(fwd(q, e) == e);
        lemma_tokenize_wellformed(s, e, unicode_ranges_allowed);
        let rest = i_tokenize_from(ints(s), e, unicode_ranges_allowed);
        let lx = i_tokenize_from(ints(s), p, unicode_ranges_allowed);
        assert(lx =~= seq![Lex { tok, start: q, end: e }] + rest);
        assert forall|j: int| 0 <= j < lx.len() implies #[trigger] lx[j].start <= lx[j].end && lx[j].end <= s.len() by {
            if j > 0 {
                assert(lx[j] == rest[j - 1]);
            }
        }
        assert forall|j: int| 0 <= j < lx.len() implies p <= #[trigger] lx[j].start by {
            if j > 0 {
                assert(lx[j] == rest[j - 1]);
            }
        }
        assert forall|j: int| 0 <= j && j + 1 < lx.len() implies #[trigger] lx[j].end <= lx[j + 1].start by {
            if j > 0 {
                assert(lx[j] == rest[j - 1]);
                assert(lx[j + 1] == rest[j]);
            } else {
                assert(lx[1] == rest[0]);
            }
        }
        assert forall|j: int| 0 <= j < lx.len() implies #[trigger] lx[j].tok != ITok::Eof by {
            if j > 0 {
                assert(lx[j] == rest[j - 1]);
            }
        }
    }
}

} // verus!
