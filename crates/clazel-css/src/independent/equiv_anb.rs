//! The independent transcription of §6 (the `<a-n-plus-b>` type) and §9.1
//! (serialize an `<a-n-plus-b>` value), [`super::anb`], is the spec's
//! ([`crate::parser::spec`], "§6 The An+B microsyntax" and "§9 Serialization"):
//! for every list of component values whose numbers the tokenizer could have made
//! ([`cvs_ok`]), both say the same about whether it matches `<a-n-plus-b>`, and the
//! same A and B; and both serialize every A and B to the same string.

#[cfg(verus_only)]
use super::anb::*;
#[cfg(verus_only)]
use super::equiv_base::*;
#[cfg(verus_only)]
use super::equiv_map::*;
#[cfg(verus_only)]
use super::equiv_tokenizer::*;
#[cfg(verus_only)]
use super::parse::*;
#[cfg(verus_only)]
use super::*;
#[cfg(verus_only)]
use crate::parser::spec as ps;
#[cfg(verus_only)]
use crate::tokenizer::spec as t;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §9.1 Serialization

/// The digits of a natural number, spelled the same.
pub proof fn lemma_serialize_nat(n: nat, d: Seq<u32>)
    ensures
        ints(ps::decimal_digits(n, d)) == i_serialize_nat(n) + ints(d),
    decreases n,
{
    if n < 10 {
        assert(ints(seq![(0x30 + n) as u32] + d) =~= seq![(0x30 + n) as int] + ints(d));
    } else {
        let x = (0x30 + n % 10) as u32;
        lemma_serialize_nat(n / 10, seq![x] + d);
        assert(ints(seq![x] + d) =~= seq![x as int] + ints(d));
        assert(i_serialize_nat(n / 10) + (seq![x as int] + ints(d)) =~= (i_serialize_nat(n / 10) + seq![x as int])
            + ints(d));
    }
}

/// The serialization of an integer, spelled the same.
pub proof fn lemma_serialize_int(v: int)
    ensures
        ints(ps::serialize_integer(v)) == i_serialize_int(v),
{
    if v < 0 {
        lemma_serialize_nat((-v) as nat, Seq::empty());
        assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
        assert(ints(seq![0x2Du32] + ps::decimal_digits((-v) as nat, Seq::empty())) =~= seq![0x2D as int]
            + ints(ps::decimal_digits((-v) as nat, Seq::empty())));
        assert(i_serialize_nat((-v) as nat) + Seq::<int>::empty() =~= i_serialize_nat((-v) as nat));
    } else {
        lemma_serialize_nat(v as nat, Seq::empty());
        assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
        assert(i_serialize_nat(v as nat) + Seq::<int>::empty() =~= i_serialize_nat(v as nat));
    }
}

/// §9.1 "serialize an `<a-n-plus-b>` value".
pub proof fn theorem_serialize_a_n_plus_b_equals(a: int, b: int)
    ensures
        ints(ps::serialize_a_n_plus_b(a, b)) == i_serialize_anb(a, b),
{
    lemma_serialize_int(a);
    lemma_serialize_int(b);
    if a != 0 {
        let head = if a == 1 {
            seq![0x6Eu32]
        } else if a == -1 {
            seq![0x2Du32, 0x6E]
        } else {
            ps::serialize_integer(a) + seq![0x6Eu32]
        };
        assert(ints(head) =~= (if a == 1 {
            seq![0x6E as int]
        } else if a == -1 {
            seq![0x2D as int, 0x6E]
        } else {
            i_serialize_int(a) + seq![0x6E as int]
        }));
        if b > 0 {
            assert(ints(head + seq![0x2Bu32] + ps::serialize_integer(b)) =~= ints(head) + seq![0x2B as int]
                + ints(ps::serialize_integer(b)));
        } else if b < 0 {
            assert(ints(head + ps::serialize_integer(b)) =~= ints(head) + ints(ps::serialize_integer(b)));
        }
    }
}

// ---------------------------------------------------------------------
// The numbers and strings that the tokens of §6 are made of

/// A number that the tokenizer could have made, if its type flag is "integer": it has
/// no exponent part, and its sign character is the one its number part starts with.
pub open spec fn int_ok(n: t::Number) -> bool {
    n.is_integer ==> (n.exponent_part.len() == 0 && match n.sign_character {
        None => !(n.number_part.len() > 0 && (n.number_part[0] == 0x2B || n.number_part[0] == 0x2D)),
        Some(c) => (c == 0x2B || c == 0x2D) && n.number_part.len() > 0 && n.number_part[0] == c,
    })
}

/// An item whose number, if it is one, is one that the tokenizer could have made.
pub open spec fn item_ok(x: ps::ComponentValue) -> bool {
    match x {
        ps::ComponentValue::Token { token: t::Token::Number { number } } => int_ok(number),
        ps::ComponentValue::Token { token: t::Token::Dimension { number, .. } } => int_ok(number),
        _ => true,
    }
}

/// A list of component values all of whose items are [`item_ok`].
pub open spec fn cvs_ok(v: Seq<ps::ComponentValue>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> #[trigger] item_ok(v[i])
}

/// The value of an integer number is the independent one.
pub proof fn lemma_integer_value(n: t::Number)
    requires
        n.is_integer,
        int_ok(n),
    ensures
        ps::integer_value(n) == i_int_value(inum_of(n)),
{
    let part = t::unsigned(n.number_part);
    let point = t::point_of(part, 0);
    assert(t::number_value(n).0 == (if t::is_negative(n.number_part) {
        -(num_mantissa(n.number_part) as int)
    } else {
        num_mantissa(n.number_part) as int
    }));
}

/// "ASCII lowercase" of a code point is the independent one.
pub broadcast proof fn lemma_lower(c: u32)
    ensures
        #[trigger] i_ascii_lower(c as int) == ps::ascii_lowercase(c) as int,
{
}

/// A string "from `i` on is an ASCII case-insensitive match" when each code point is.
pub proof fn lemma_matches(s: Seq<u32>, l: Seq<u32>, i: int)
    requires
        s.len() == l.len(),
        0 <= i,
    ensures
        ps::matches_from(s, l, i) == (forall|k: int| i <= k < s.len() ==> #[trigger] ps::ascii_lowercase(s[k]) == l[k]),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_matches(s, l, i + 1);
        assert(ps::matches_from(s, l, i) == (ps::ascii_lowercase(s[i]) == l[i] && ps::matches_from(s, l, i + 1)));
        if ps::matches_from(s, l, i) {
            assert forall|k: int| i <= k < s.len() implies #[trigger] ps::ascii_lowercase(s[k]) == l[k] by {
                if k > i {
                    assert(ps::matches_from(s, l, i + 1));
                }
            }
        }
    }
}

/// "ASCII case-insensitive match" is the independent one.
pub proof fn lemma_ci(u: Seq<u32>, l: Seq<u32>)
    ensures
        i_ci_match(ints(u), ints(l)) == ps::ascii_case_insensitive_match(u, l),
{
    broadcast use lemma_lower;
    if u.len() == l.len() {
        lemma_matches(u, l, 0);
        if i_ci_match(ints(u), ints(l)) {
            assert forall|k: int| 0 <= k < u.len() implies #[trigger] ps::ascii_lowercase(u[k]) == l[k] by {
                assert(i_ascii_lower(ints(u)[k]) == ints(l)[k]);
            }
        }
        if ps::ascii_case_insensitive_match(u, l) {
            assert forall|k: int| 0 <= k < ints(u).len() implies i_ascii_lower(#[trigger] ints(u)[k]) == ints(l)[k] by {
                assert(ps::ascii_lowercase(u[k]) == l[k]);
            }
        }
    }
}

/// `all_digits` from `i` on is each one being a digit.
pub proof fn lemma_all_digits(s: Seq<u32>, i: int)
    requires
        0 <= i,
    ensures
        ps::all_digits(s, i) == (forall|k: int| i <= k < s.len() ==> #[trigger] t::is_digit(s[k])),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_all_digits(s, i + 1);
        if ps::all_digits(s, i) {
            assert forall|k: int| i <= k < s.len() implies #[trigger] t::is_digit(s[k]) by {
                if k > i {
                    assert(ps::all_digits(s, i + 1));
                }
            }
        }
    }
}

/// The digits of `u[a..b)` are the same number in both.
pub proof fn lemma_dv(u: Seq<u32>, a: nat, b: nat)
    requires
        a <= b <= u.len(),
        forall|k: int| a <= k < b ==> t::is_digit(#[trigger] u[k]),
    ensures
        t::digits_value(u.subrange(a as int, b as int), 0) == i_value(ints(u), a, b, 10),
    decreases b,
{
    if b > a {
        lemma_dv(u, a, (b - 1) as nat);
        let x = u.subrange(a as int, b as int - 1);
        let d = u[b as int - 1];
        assert(u.subrange(a as int, b as int) =~= x.push(d));
        assert(x.push(d) =~= x + seq![d]);
        lemma_digits_value_fold(x, seq![d], 0);
        assert(seq![d].drop_first() =~= Seq::<u32>::empty());
        reveal_with_fuel(t::digits_value, 2);
        assert(t::digits_value(seq![d], t::digits_value(x, 0)) == t::digits_value(x, 0) * 10 + (d - 0x30) as nat);
        assert(i_value(ints(u), a, b, 10) == i_value(ints(u), a, (b - 1) as nat, 10) * 10 + i_digit_value(
            i_at(ints(u), (b - 1) as nat),
        ));
        assert(i_at(ints(u), (b - 1) as nat) == d as int);
        assert(i_digit_value(d as int) == (d - 0x30) as nat);
    } else {
        assert(u.subrange(a as int, b as int) =~= Seq::<u32>::empty());
    }
}

/// The strings of the clauses, as the independent transcription's.
pub proof fn lemma_strings()
    ensures
        ints(ps::n_string()) == seq![0x6E as int],
        ints(ps::n_dash_string()) == seq![0x6E as int, 0x2D],
        ints(ps::dash_n_string()) == seq![0x2D as int, 0x6E],
        ints(ps::dash_n_dash_string()) == seq![0x2D as int, 0x6E, 0x2D],
        ints(seq![0x6Fu32, 0x64, 0x64]) == seq![0x6F as int, 0x64, 0x64],
        ints(seq![0x65u32, 0x76, 0x65, 0x6E]) == seq![0x65 as int, 0x76, 0x65, 0x6E],
{
    assert(ints(ps::n_string()) =~= seq![0x6E as int]);
    assert(ints(ps::n_dash_string()) =~= seq![0x6E as int, 0x2D]);
    assert(ints(ps::dash_n_string()) =~= seq![0x2D as int, 0x6E]);
    assert(ints(ps::dash_n_dash_string()) =~= seq![0x2D as int, 0x6E, 0x2D]);
    assert(ints(seq![0x6Fu32, 0x64, 0x64]) =~= seq![0x6F as int, 0x64, 0x64]);
    assert(ints(seq![0x65u32, 0x76, 0x65, 0x6E]) =~= seq![0x65 as int, 0x76, 0x65, 0x6E]);
}

/// The stem of a string is what the spec's tests say.
pub proof fn lemma_stem(u: Seq<u32>)
    ensures
        (i_stem(ints(u)) is N) == ps::ascii_case_insensitive_match(u, ps::n_string()),
        (i_stem(ints(u)) is NDash) == ps::ascii_case_insensitive_match(u, ps::n_dash_string()),
        (i_stem(ints(u)) is NDashDigits) == ps::is_n_dash_digits(u, 0),
        ps::is_n_dash_digits(u, 0) ==> i_stem(ints(u)) == IStem::NDashDigits(
            t::digits_value(u.subrange(2, u.len() as int), 0),
        ),
{
    broadcast use lemma_lower;
    lemma_strings();
    lemma_ci(u, ps::n_string());
    lemma_ci(u, ps::n_dash_string());
    lemma_all_digits(u, 2);
    if u.len() >= 3 {
        assert(i_digits_from(ints(u), 2) == ps::all_digits(u, 2)) by {
            if ps::all_digits(u, 2) {
                assert forall|k: int| 2 <= k < ints(u).len() implies i_digit(#[trigger] ints(u)[k]) by {
                    assert(t::is_digit(u[k]));
                }
            }
            if i_digits_from(ints(u), 2) {
                assert forall|k: int| 2 <= k < u.len() implies t::is_digit(#[trigger] u[k]) by {
                    assert(i_digit(ints(u)[k]));
                }
            }
        }
        if ps::is_n_dash_digits(u, 0) {
            lemma_dv(u, 2, u.len());
        }
    }
}
/// The spec's matches of the four strings, spelled out by code point.
pub proof fn lemma_ci_chars(u: Seq<u32>)
    ensures
        ps::ascii_case_insensitive_match(u, ps::n_string()) == (u.len() == 1 && ps::ascii_lowercase(u[0]) == 0x6E),
        ps::ascii_case_insensitive_match(u, ps::n_dash_string()) == (u.len() == 2 && ps::ascii_lowercase(u[0])
            == 0x6E && u[1] == 0x2D),
        ps::ascii_case_insensitive_match(u, ps::dash_n_string()) == (u.len() == 2 && u[0] == 0x2D
            && ps::ascii_lowercase(u[1]) == 0x6E),
        ps::ascii_case_insensitive_match(u, ps::dash_n_dash_string()) == (u.len() == 3 && u[0] == 0x2D
            && ps::ascii_lowercase(u[1]) == 0x6E && u[2] == 0x2D),
{
    reveal_with_fuel(ps::matches_from, 5);
}

/// The stem of a string after a `-` is what the spec's tests say.
pub proof fn lemma_dashed_stem(u: Seq<u32>)
    ensures
        (i_dashed_stem(ints(u)) is N) == ps::ascii_case_insensitive_match(u, ps::dash_n_string()),
        (i_dashed_stem(ints(u)) is NDash) == ps::ascii_case_insensitive_match(u, ps::dash_n_dash_string()),
        (i_dashed_stem(ints(u)) is NDashDigits) == (u.len() > 0 && u[0] == 0x2D && ps::is_n_dash_digits(u, 1)),
        (u.len() > 0 && u[0] == 0x2D && ps::is_n_dash_digits(u, 1)) ==> i_dashed_stem(ints(u)) == IStem::NDashDigits(
            t::digits_value(u.subrange(3, u.len() as int), 0),
        ),
{
    lemma_ci_chars(u);
    if u.len() >= 1 && u[0] == 0x2D {
        let w = u.skip(1);
        assert(ints(u).skip(1) =~= ints(w));
        lemma_stem(w);
        lemma_ci_chars(w);
        lemma_all_digits(u, 3);
        lemma_all_digits(w, 2);
        assert(ps::all_digits(u, 3) == ps::all_digits(w, 2)) by {
            if ps::all_digits(w, 2) {
                assert forall|k: int| 3 <= k < u.len() implies t::is_digit(#[trigger] u[k]) by {
                    assert(t::is_digit(w[k - 1]));
                }
            }
            if ps::all_digits(u, 3) {
                assert forall|k: int| 2 <= k < w.len() implies t::is_digit(#[trigger] w[k]) by {
                    assert(t::is_digit(u[k + 1]));
                }
            }
        }
        if u.len() >= 4 {
            assert(w.subrange(2, w.len() as int) =~= u.subrange(3, u.len() as int));
        }
    }
}

// ---------------------------------------------------------------------
// The independent matching, on the list of non-whitespace items

/// The items of `vs` from `p` on that are not `<whitespace-token>`s.
pub open spec fn nonws_from(vs: Seq<ICv>, p: nat) -> Seq<ICv>
    decreases (if vs.len() > p { vs.len() - p } else { 0 }),
{
    if p >= vs.len() {
        seq![]
    } else if vs[p as int] == ICv::Token(ITok::Whitespace) {
        nonws_from(vs, p + 1)
    } else {
        seq![vs[p as int]] + nonws_from(vs, p + 1)
    }
}

/// Skipping whitespace leaves the non-whitespace items as they are.
pub proof fn lemma_skip_nonws(vs: Seq<ICv>, p: nat)
    ensures
        nonws_from(vs, p) == nonws_from(vs, i_anb_skip(vs, p)),
        p <= i_anb_skip(vs, p),
        i_anb_skip(vs, p) < vs.len() ==> vs[i_anb_skip(vs, p) as int] != ICv::Token(ITok::Whitespace),
        p <= vs.len() ==> i_anb_skip(vs, p) <= vs.len(),
    decreases (if vs.len() > p { vs.len() - p } else { 0 }),
{
    if p < vs.len() && vs[p as int] == ICv::Token(ITok::Whitespace) {
        lemma_skip_nonws(vs, p + 1);
    }
}

/// "Nothing but whitespace from `p` on" is no non-whitespace items.
pub proof fn lemma_end_nonws(vs: Seq<ICv>, p: nat)
    ensures
        i_anb_end(vs, p) == (nonws_from(vs, p).len() == 0),
{
    lemma_skip_nonws(vs, p);
    let q = i_anb_skip(vs, p);
    if q < vs.len() {
        assert(nonws_from(vs, q) == seq![vs[q as int]] + nonws_from(vs, q + 1));
    }
}

/// What follows the `n` of a clause, on the list of the items that follow.
pub open spec fn l_after_n(w: Seq<ICv>, a: int) -> Option<(int, int)> {
    if w.len() == 0 {
        Some((a, 0))
    } else if w.len() == 1 {
        match i_anb_tok(w, 0) {
            Some(ITok::Number(n, true)) => if n.sign != ISign::NoSign { Some((a, i_int_value(n))) } else { None },
            _ => None,
        }
    } else if w.len() == 2 {
        match i_anb_tok(w, 0) {
            Some(ITok::Delim(c)) => if c == 0x2B || c == 0x2D {
                match i_anb_tok(w, 1) {
                    Some(ITok::Number(n, true)) => if n.sign == ISign::NoSign {
                        Some((a, if c == 0x2D { -i_int_value(n) } else { i_int_value(n) }))
                    } else {
                        None
                    },
                    _ => None,
                }
            } else {
                None
            },
            _ => None,
        }
    } else {
        None
    }
}

/// What follows the `n-` of a clause, on the list of the items that follow.
pub open spec fn l_after_ndash(w: Seq<ICv>, a: int) -> Option<(int, int)> {
    if w.len() == 1 {
        match i_anb_tok(w, 0) {
            Some(ITok::Number(n, true)) => if n.sign == ISign::NoSign { Some((a, -i_int_value(n))) } else { None },
            _ => None,
        }
    } else {
        None
    }
}

/// What follows a stem, on the list of the items that follow.
pub open spec fn l_after_stem(w: Seq<ICv>, a: int, stem: IStem) -> Option<(int, int)> {
    match stem {
        IStem::N => l_after_n(w, a),
        IStem::NDash => l_after_ndash(w, a),
        IStem::NDashDigits(d) => if w.len() == 0 { Some((a, -(d as int))) } else { None },
        IStem::Other => None,
    }
}

/// `<a-n-plus-b>` on the list of the non-whitespace items, with whether a `+` at the
/// start has no whitespace after it.
pub open spec fn l_anb(w: Seq<ICv>, adj: bool) -> Option<(int, int)> {
    match i_anb_tok(w, 0) {
        Some(ITok::Ident(s)) => {
            if i_is_odd(s) {
                if w.len() == 1 { Some((2, 1)) } else { None }
            } else if i_is_even(s) {
                if w.len() == 1 { Some((2, 0)) } else { None }
            } else {
                match i_stem(s) {
                    IStem::Other => l_after_stem(w.skip(1), -1, i_dashed_stem(s)),
                    stem => l_after_stem(w.skip(1), 1, stem),
                }
            }
        },
        Some(ITok::Number(n, true)) => if w.len() == 1 { Some((0, i_int_value(n))) } else { None },
        Some(ITok::Dimension(n, true, u)) => l_after_stem(w.skip(1), i_int_value(n), i_stem(u)),
        Some(ITok::Delim(c)) => {
            if c == 0x2B && adj {
                match i_anb_tok(w, 1) {
                    Some(ITok::Ident(s)) => l_after_stem(w.skip(2), 1, i_stem(s)),
                    _ => None,
                }
            } else {
                None
            }
        },
        _ => None,
    }
}

/// Whether the first item that is not whitespace has an item right after it that is
/// not whitespace.
pub open spec fn adj_of(vs: Seq<ICv>) -> bool {
    let p = i_anb_skip(vs, 0);
    p + 1 < vs.len() && vs[(p + 1) as int] != ICv::Token(ITok::Whitespace)
}

/// The tail clauses of the independent matching, with the whitespace skipped, are
/// those on the list of the non-whitespace items.
pub proof fn lemma_after(vs: Seq<ICv>, p: nat, a: int)
    ensures
        i_anb_after_n(vs, p, a) == l_after_n(nonws_from(vs, p), a),
        i_anb_after_ndash(vs, p, a) == l_after_ndash(nonws_from(vs, p), a),
{
    lemma_skip_nonws(vs, p);
    let q = i_anb_skip(vs, p);
    if q < vs.len() {
        assert(nonws_from(vs, q) == seq![vs[q as int]] + nonws_from(vs, q + 1));
        lemma_end_nonws(vs, q + 1);
        lemma_skip_nonws(vs, q + 1);
        let r = i_anb_skip(vs, q + 1);
        if r < vs.len() {
            assert(nonws_from(vs, r) == seq![vs[r as int]] + nonws_from(vs, r + 1));
            lemma_end_nonws(vs, r + 1);
        }
    }
}

/// What follows a stem, likewise.
pub broadcast proof fn lemma_after_stem(vs: Seq<ICv>, p: nat, a: int, stem: IStem)
    ensures
        #[trigger] i_anb_after_stem(vs, p, a, stem) == l_after_stem(nonws_from(vs, p), a, stem),
{
    lemma_after(vs, p, a);
    lemma_end_nonws(vs, p);
}

/// The independent matching is the matching on the list of the non-whitespace items.
pub proof fn lemma_anb_list(vs: Seq<ICv>)
    ensures
        i_anb(vs) == l_anb(nonws_from(vs, 0), adj_of(vs)),
{
    broadcast use lemma_after_stem;
    lemma_skip_nonws(vs, 0);
    let p = i_anb_skip(vs, 0);
    if p < vs.len() {
        let w = nonws_from(vs, 0);
        assert(w == seq![vs[p as int]] + nonws_from(vs, p + 1));
        assert(w.skip(1) =~= nonws_from(vs, p + 1));
        lemma_end_nonws(vs, p + 1);
        lemma_after(vs, p + 1, 0);
        if let Some(ITok::Delim(c)) = i_anb_tok(vs, p) {
            if c == 0x2B {
                if i_anb_tok(vs, p + 1) is Some && vs[(p + 1) as int] != ICv::Token(ITok::Whitespace) {
                    assert(nonws_from(vs, p + 1) == seq![vs[(p + 1) as int]] + nonws_from(vs, p + 2));
                    lemma_after(vs, p + 2, 0);
                    assert(w.skip(2) =~= nonws_from(vs, p + 2));
                }
            }
        }
    } else {
        assert(nonws_from(vs, 0) == Seq::<ICv>::empty());
    }
}

// ---------------------------------------------------------------------
// The spec's matching of the non-whitespace items

/// An item of the spec, read as the independent transcription's token, if it is one.
pub open spec fn tk_of(x: ps::ComponentValue) -> Option<ITok> {
    match x {
        ps::ComponentValue::Token { token } => Some(tok_of(token)),
        _ => None,
    }
}

/// The tests of the spec on an item are the independent transcription's on its token.
pub proof fn lemma_item(x: ps::ComponentValue)
    requires
        item_ok(x),
    ensures
        ps::is_ident(x) == (tk_of(x) is Some && tk_of(x)->Some_0 is Ident),
        ps::is_integer_dimension(x) == (tk_of(x) is Some && tk_of(x)->Some_0 is Dimension && tk_of(x)->Some_0->Dimension_1),
        ps::is_integer_dimension(x) ==> ps::dimension_value(x) == i_int_value(tk_of(x)->Some_0->Dimension_0),
        ps::is_integer_dimension(x) ==> ints(ps::dimension_unit(x)) == tk_of(x)->Some_0->Dimension_2,
        (ps::integer_number(x) is Some) == (tk_of(x) is Some && tk_of(x)->Some_0 is Number && tk_of(x)->Some_0->Number_1),
        (ps::integer_number(x) is Some) ==> ps::integer_value(ps::integer_number(x)->Some_0) == i_int_value(
            tk_of(x)->Some_0->Number_0,
        ),
        (ps::signed_integer(x) is Some) == (ps::integer_number(x) is Some && tk_of(x)->Some_0->Number_0.sign
            != ISign::NoSign),
        (ps::signed_integer(x) is Some) ==> ps::signed_integer(x)->Some_0 == i_int_value(tk_of(x)->Some_0->Number_0),
        (ps::signless_integer(x) is Some) == (ps::integer_number(x) is Some && tk_of(x)->Some_0->Number_0.sign
            == ISign::NoSign),
        (ps::signless_integer(x) is Some) ==> ps::signless_integer(x)->Some_0 == i_int_value(
            tk_of(x)->Some_0->Number_0,
        ),
        ps::is_plus(x) == (tk_of(x) == Some(ITok::Delim(0x2B))),
        ps::is_minus(x) == (tk_of(x) == Some(ITok::Delim(0x2D))),
{
    match x {
        ps::ComponentValue::Token { token: t::Token::Number { number } } => {
            if number.is_integer {
                lemma_integer_value(number);
            }
        },
        ps::ComponentValue::Token { token: t::Token::Dimension { number, unit } } => {
            if number.is_integer {
                lemma_integer_value(number);
            }
        },
        _ => {},
    }
}

/// "is an `<ident-token>` matching, ASCII case-insensitively" is the independent test.
pub proof fn lemma_keyword(x: ps::ComponentValue, l: Seq<u32>)
    ensures
        ps::is_keyword(x, l) == (tk_of(x) is Some && tk_of(x)->Some_0 is Ident && i_ci_match(
            tk_of(x)->Some_0->Ident_0,
            ints(l),
        )),
{
    if let ps::ComponentValue::Token { token: t::Token::Ident { value } } = x {
        lemma_ci(value, l);
    }
}

/// The token at an index of the mapped list is that of the item.
pub broadcast proof fn lemma_tok_k(items: Seq<ps::ComponentValue>, k: nat)
    ensures
        #[trigger] i_anb_tok(cvs_of(items), k) == (if k < items.len() { tk_of(items[k as int]) } else { None }),
{
}

/// The spec's `<a-n-plus-b>` on the non-whitespace items is the independent one.
pub proof fn lemma_items(items: Seq<ps::ComponentValue>, adj: bool)
    requires
        cvs_ok(items),
    ensures
        ps::a_n_plus_b_items(items, adj) == l_anb(cvs_of(items), adj),
{
    broadcast use lemma_tok_k;
    lemma_strings();
    let w = cvs_of(items);
    assert(w.len() == items.len());
    if items.len() > 0 {
        assert(item_ok(items[0]));
        lemma_item(items[0]);
        lemma_item(items.last());
        if items.len() > 1 {
            assert(item_ok(items[1]));
            lemma_item(items[1]);
        }
        if items.len() > 2 {
            assert(item_ok(items[2]));
            lemma_item(items[2]);
        }
        lemma_keyword(items[0], seq![0x6Fu32, 0x64, 0x64]);
        lemma_keyword(items[0], seq![0x65u32, 0x76, 0x65, 0x6E]);
        lemma_keyword(items[0], ps::n_string());
        lemma_keyword(items[0], ps::n_dash_string());
        lemma_keyword(items[0], ps::dash_n_string());
        lemma_keyword(items[0], ps::dash_n_dash_string());
        if items.len() > 1 {
            lemma_keyword(items[1], ps::n_string());
            lemma_keyword(items[1], ps::n_dash_string());
        }
        if let ps::ComponentValue::Token { token: t::Token::Ident { value } } = items[0] {
            lemma_stem(value);
            lemma_dashed_stem(value);
            lemma_ci(value, seq![0x6Fu32, 0x64, 0x64]);
            lemma_ci(value, seq![0x65u32, 0x76, 0x65, 0x6E]);
        }
        if let ps::ComponentValue::Token { token: t::Token::Dimension { number, unit } } = items[0] {
            lemma_stem(unit);
        }
        if items.len() > 1 {
            if let ps::ComponentValue::Token { token: t::Token::Ident { value } } = items[1] {
                lemma_stem(value);
            }
        }
    }
}

/// An item of the spec is a `<whitespace-token>` as the independent mapping says.
pub proof fn lemma_ws(x: ps::ComponentValue)
    ensures
        ps::is_whitespace_token(x) == (cv_of(x) == ICv::Token(ITok::Whitespace)),
{
    if let ps::ComponentValue::Token { token } = x {
        assert(tok_of(token) == ITok::Whitespace ==> token == t::Token::Whitespace);
    }
}

/// Pushing an item on a list adds it to the non-whitespace items if it is not whitespace.
pub proof fn lemma_nonws_push(l: Seq<ICv>, x: ICv, p: nat)
    requires
        p <= l.len(),
    ensures
        nonws_from(l.push(x), p) == nonws_from(l, p) + (if x == ICv::Token(ITok::Whitespace) {
            Seq::<ICv>::empty()
        } else {
            seq![x]
        }),
    decreases l.len() - p,
{
    if p < l.len() {
        assert(l.push(x)[p as int] == l[p as int]);
        lemma_nonws_push(l, x, p + 1);
        if l[p as int] != ICv::Token(ITok::Whitespace) {
            assert(seq![l[p as int]] + (nonws_from(l, p + 1) + (if x == ICv::Token(ITok::Whitespace) {
                Seq::<ICv>::empty()
            } else {
                seq![x]
            })) =~= (seq![l[p as int]] + nonws_from(l, p + 1)) + (if x == ICv::Token(ITok::Whitespace) {
                Seq::<ICv>::empty()
            } else {
                seq![x]
            }));
        }
    } else {
        assert(p == l.len());
        assert(l.push(x)[p as int] == x);
        assert(nonws_from(l, p) == Seq::<ICv>::empty());
        if x != ICv::Token(ITok::Whitespace) {
            assert(nonws_from(l.push(x), p) == seq![x] + nonws_from(l.push(x), p + 1));
            assert(nonws_from(l.push(x), p + 1) == Seq::<ICv>::empty());
            assert(Seq::<ICv>::empty() + seq![x] =~= seq![x]);
        } else {
            assert(nonws_from(l.push(x), p) == nonws_from(l.push(x), p + 1));
            assert(Seq::<ICv>::empty() + Seq::<ICv>::empty() =~= Seq::<ICv>::empty());
        }
    }
}

/// The spec's items without whitespace are the independent non-whitespace items.
pub proof fn lemma_without_whitespace(v: Seq<ps::ComponentValue>)
    requires
        cvs_ok(v),
    ensures
        cvs_of(ps::without_whitespace(v)) == nonws_from(cvs_of(v), 0),
        cvs_ok(ps::without_whitespace(v)),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(cvs_of(v) =~= Seq::<ICv>::empty());
        assert(cvs_of(ps::without_whitespace(v)) =~= Seq::<ICv>::empty());
        assert(nonws_from(cvs_of(v), 0) == Seq::<ICv>::empty());
    } else {
        let d = v.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] item_ok(d[i]) by {
            assert(d[i] == v[i]);
        }
        lemma_without_whitespace(d);
        let last = v.last();
        assert(item_ok(last));
        lemma_ws(last);
        assert(cvs_of(d) =~= cvs_of(v).drop_last());
        assert(cvs_of(v) =~= cvs_of(d).push(cv_of(last)));
        lemma_nonws_push(cvs_of(d), cv_of(last), 0);
        if ps::is_whitespace_token(last) {
            assert(ps::without_whitespace(v) == ps::without_whitespace(d));
            assert(nonws_from(cvs_of(v), 0) == nonws_from(cvs_of(d), 0) + Seq::<ICv>::empty());
            assert(nonws_from(cvs_of(d), 0) + Seq::<ICv>::empty() =~= nonws_from(cvs_of(d), 0));
        } else {
            assert(ps::without_whitespace(v) == ps::without_whitespace(d).push(last));
            assert(cvs_of(ps::without_whitespace(d).push(last)) =~= cvs_of(ps::without_whitespace(d)).push(cv_of(last)));
            assert(cvs_of(ps::without_whitespace(d)).push(cv_of(last)) =~= nonws_from(cvs_of(d), 0) + seq![cv_of(last)]);
            let wd = ps::without_whitespace(d);
            assert forall|i: int| 0 <= i < wd.push(last).len() implies #[trigger] item_ok(wd.push(last)[i]) by {
                if i < wd.len() {
                    assert(wd.push(last)[i] == wd[i]);
                } else {
                    assert(wd.push(last)[i] == last);
                }
            }
        }
    }
}

/// The first item that is not whitespace is at the same place in both.
pub proof fn lemma_first_non_ws(v: Seq<ps::ComponentValue>, p: int)
    requires
        0 <= p <= v.len(),
    ensures
        ps::first_non_whitespace(v, p) == i_anb_skip(cvs_of(v), p as nat) as int,
    decreases v.len() - p,
{
    if p < v.len() {
        lemma_ws(v[p]);
        lemma_first_non_ws(v, p + 1);
    }
}

/// §6 "The `<a-n-plus-b>` type".
pub proof fn theorem_a_n_plus_b_equals(v: Seq<ps::ComponentValue>)
    requires
        cvs_ok(v),
    ensures
        ps::a_n_plus_b(v) == i_anb(cvs_of(v)),
{
    let vs = cvs_of(v);
    lemma_anb_list(vs);
    lemma_without_whitespace(v);
    lemma_first_non_ws(v, 0);
    let start = ps::first_non_whitespace(v, 0);
    let adj = start + 1 < v.len() && !ps::is_whitespace_token(v[start + 1]);
    lemma_items(ps::without_whitespace(v), adj);
    if start + 1 < v.len() {
        lemma_ws(v[start + 1]);
    }
    assert(adj == adj_of(vs));
}

// ---------------------------------------------------------------------
// The numbers of the tokenizer are ones that [`int_ok`] accepts

/// A token whose number, if it has one with the type flag "integer", is [`int_ok`].
pub open spec fn tok_ok(k: t::Token) -> bool {
    match k {
        t::Token::Number { number } => int_ok(number),
        t::Token::Dimension { number, .. } => int_ok(number),
        _ => true,
    }
}

/// "While the next input code point is a digit, consume it and append it to" `part`:
/// what was there is still there, and what is added is digits.
pub proof fn lemma_consume_digits(input: Seq<u32>, pos: int, part: Seq<u32>)
    ensures
        ({
            let r = t::consume_digits(input, pos, part).0;
            &&& r.len() >= part.len()
            &&& r.subrange(0, part.len() as int) == part
            &&& forall|k: int| part.len() <= k < r.len() ==> t::is_digit(#[trigger] r[k])
        }),
    decreases t::remaining(input, pos),
{
    if t::is_digit(t::at(input, pos)) {
        let c = t::at(input, pos);
        lemma_consume_digits(input, pos + 1, part.push(c));
        let r = t::consume_digits(input, pos + 1, part.push(c)).0;
        assert(r.subrange(0, part.len() as int) =~= part) by {
            assert(r.subrange(0, part.len() as int + 1) == part.push(c));
            assert(r.subrange(0, part.len() as int) =~= r.subrange(0, part.len() as int + 1).subrange(0, part.len() as int));
        }
        assert forall|k: int| part.len() <= k < r.len() implies t::is_digit(#[trigger] r[k]) by {
            if k == part.len() {
                assert(r[k] == part.push(c)[k]);
            }
        }
    }
}

/// §4.3.12: the number that "consume a number" returns is [`int_ok`].
pub proof fn lemma_number_ok(input: Seq<u32>, pos: int)
    ensures
        int_ok(t::consume_a_number(input, pos).0),
{
    let (signed, sign_character, after_sign) = t::number_step_2(input, pos);
    let (integer, after_integer) = t::consume_digits(input, after_sign, signed);
    lemma_consume_digits(input, after_sign, signed);
    let (number_part, no_fraction, after_fraction) = t::number_step_4(input, after_integer, integer);
    let (exponent_part, has_exponent, end) = t::number_step_5(input, after_fraction);
    if no_fraction && !has_exponent {
        assert(number_part == integer);
        assert(exponent_part.len() == 0);
        match sign_character {
            None => {
                assert(signed.len() == 0);
                if integer.len() > 0 {
                    assert(t::is_digit(integer[0]));
                }
            },
            Some(c) => {
                assert(signed =~= seq![c]);
                assert(integer[0] == signed[0]);
            },
        }
    }
}

/// A string token or a bad-string token is [`tok_ok`], as the string loop returns it.
pub proof fn lemma_string_ok(input: Seq<u32>, pos: int, ending: u32, value: Seq<u32>)
    ensures
        tok_ok(t::consume_string_loop(input, pos, ending, value).0),
    decreases t::remaining(input, pos),
{
    let c = t::at(input, pos);
    if c != ending && c != t::EOF && !t::is_newline(c) {
        if c == 0x5C {
            if t::at(input, pos + 1) == t::EOF {
                lemma_string_ok(input, pos + 1, ending, value);
            } else if t::is_newline(t::at(input, pos + 1)) {
                lemma_string_ok(input, pos + 2, ending, value);
            } else {
                crate::tokenizer::termination::lemma_escape_advances(input, pos + 1);
                let (code_point, next) = t::consume_escaped_code_point(input, pos + 1);
                lemma_string_ok(input, next, ending, value.push(code_point));
            }
        } else {
            lemma_string_ok(input, pos + 1, ending, value.push(c));
        }
    }
}

/// A url token or a bad-url token is [`tok_ok`], as the url loop returns it.
pub proof fn lemma_url_ok(input: Seq<u32>, pos: int, value: Seq<u32>)
    ensures
        tok_ok(t::consume_url_loop(input, pos, value).0),
    decreases t::remaining(input, pos),
{
    let c = t::at(input, pos);
    if c != 0x29 && c != t::EOF && !t::is_whitespace(c) && !(c == 0x22 || c == 0x27 || c == 0x28
        || t::is_non_printable_code_point(c)) {
        if c == 0x5C {
            if t::are_a_valid_escape(c, t::at(input, pos + 1)) {
                crate::tokenizer::termination::lemma_escape_advances(input, pos + 1);
                let (code_point, next) = t::consume_escaped_code_point(input, pos + 1);
                lemma_url_ok(input, next, value.push(code_point));
            }
        } else {
            lemma_url_ok(input, pos + 1, value.push(c));
        }
    }
}

/// §4.3.3: the token of "consume a numeric token" is [`tok_ok`].
pub proof fn lemma_numeric_ok(input: Seq<u32>, pos: int)
    ensures
        tok_ok(t::consume_a_numeric_token(input, pos).0),
{
    lemma_number_ok(input, pos);
}

/// §4.3.4: the token of "consume an ident-like token" is [`tok_ok`].
pub proof fn lemma_ident_like_ok(input: Seq<u32>, pos: int)
    ensures
        tok_ok(t::consume_an_ident_like_token(input, pos).0),
{
    let (string, after) = t::consume_ident_sequence(input, pos);
    if t::is_url(string) && t::at(input, after) == 0x28 {
        let next = t::consume_whitespace_but_one(input, after + 1);
        if !(t::is_quote(t::at(input, next)) || (t::is_whitespace(t::at(input, next)) && t::is_quote(
            t::at(input, next + 1),
        ))) {
            lemma_url_ok(input, t::consume_whitespace(input, next), Seq::empty());
        }
    }
}

/// §4.3.1: every token of "consume a token" is [`tok_ok`].
pub proof fn lemma_token_ok(input: Seq<u32>, start: int, unicode_ranges_allowed: bool)
    ensures
        tok_ok(t::consume_a_token(input, start, unicode_ranges_allowed).0),
{
    let current = t::consume_comments(input, start);
    lemma_numeric_ok(input, current);
    lemma_ident_like_ok(input, current);
    let c = t::at(input, current);
    let pos = current + 1;
    if c == 0x22 || c == 0x27 {
        lemma_string_ok(input, pos, c, Seq::empty());
    }
}

/// §4: every token of "tokenize" is [`tok_ok`].
pub proof fn lemma_tokenize_ok(input: Seq<u32>, pos: int, u: bool, tokens: Seq<t::Token>)
    requires
        forall|i: int| 0 <= i < tokens.len() ==> #[trigger] tok_ok(tokens[i]),
    ensures
        forall|i: int| 0 <= i < t::tokenize_loop(input, pos, u, tokens).len() ==> #[trigger] tok_ok(
            t::tokenize_loop(input, pos, u, tokens)[i],
        ),
    decreases t::remaining(input, pos),
{
    let (token, next) = t::consume_a_token(input, pos, u);
    lemma_token_ok(input, pos, u);
    crate::tokenizer::termination::lemma_token_advances(input, pos, u);
    let pushed = tokens.push(token);
    assert forall|i: int| 0 <= i < pushed.len() implies #[trigger] tok_ok(pushed[i]) by {
        if i < tokens.len() {
            assert(pushed[i] == tokens[i]);
        } else {
            assert(pushed[i] == token);
        }
    }
    if !(token is Eof) {
        lemma_tokenize_ok(input, next, u, pushed);
        assert(t::tokenize_loop(input, pos, u, tokens) == t::tokenize_loop(input, next, u, pushed));
    } else {
        assert(t::tokenize_loop(input, pos, u, tokens) == pushed);
    }
}

} // verus!
