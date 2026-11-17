//! The An+B microsyntax of CSS Syntax Level 3 (§6, the `<a-n-plus-b>` type) and
//! "serialize an `<a-n-plus-b>` value" (§9.1), transcribed from the standard
//! alone; see the header of [`super`] for the text and the modelling choices that
//! this file shares.
//!
//! ## Modelling choices
//!
//! - `<a-n-plus-b>` is a type of CSS grammar: a list of component values matches
//!   it or not, and when it does, the clauses say what A and B are. The input here
//!   is the list of component values that "parse a list of component values"
//!   returns ([`super::parse::ICv`]); [`i_anb`] is `None` when the list does not
//!   match and `Some((A, B))` when it does. A and B are mathematical integers
//!   (the standard does not bound them).
//! - "Whitespace is valid (and ignored) between any other two tokens": the
//!   whitespace tokens at the start and the end of the list and between any two
//!   tokens are skipped, except between a `+` and the ident that it precedes in the
//!   clauses marked with the dagger. Only tokens match the productions: a function
//!   or a simple block never does.
//! - The productions that start with `'+'? n` (and `n-`, and `<ndashdigit-ident>`)
//!   are taken to be the `<ident-token>` productions, with the optional `+` a
//!   `<delim-token>` for U+002B directly before the ident, no token between them.
//!   `<n-dimension>`, `<ndash-dimension>` and `<ndashdigit-dimension>` are
//!   dimension tokens with the integer type flag and a unit that is an ASCII
//!   case-insensitive match for the string. A `<signed-integer>` is an integer
//!   number token whose sign character is `+` or `-`, a `<signless-integer>` one
//!   with none.
//! - The value of an integer token is its sign and its digits ("consume a number"
//!   with the type flag `integer` has no fraction and no exponent). A "base-10
//!   number" is the value of the digits.
//! - "the serialization of B" is the decimal integer, with a U+002D HYPHEN-MINUS
//!   first when negative, as a string of code points.

#[cfg(verus_only)]
use super::parse::*;
#[cfg(verus_only)]
use super::*;

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the stem of an ident or a unit is: after the `-` of the `-n` forms.
pub ghost enum IStem {
    /// "n".
    N,
    /// "n-".
    NDash,
    /// "n-*" where "*" is a series of one or more digits, with the value of the digits.
    NDashDigits(nat),
    /// Anything else.
    Other,
}

/// Whether `s[a..]` is one or more digits.
pub open spec fn i_digits_from(s: Seq<int>, a: nat) -> bool {
    a < s.len() && forall|k: int| a <= k < s.len() ==> i_digit(s[k])
}

/// Whether the string is an ASCII case-insensitive match for "n", for "n-" or
/// for "n-*", where "*" is a series of one or more digits.
pub open spec fn i_stem(s: Seq<int>) -> IStem {
    if i_ci_match(s, seq![0x6E as int]) {
        IStem::N
    } else if i_ci_match(s, seq![0x6E as int, 0x2D]) {
        IStem::NDash
    } else if s.len() >= 3 && i_ascii_lower(s[0]) == 0x6E && s[1] == 0x2D && i_digits_from(s, 2) {
        IStem::NDashDigits(i_value(s, 2, s.len(), 10))
    } else {
        IStem::Other
    }
}

/// The same for the strings of the clauses that start with `-`: "-n", "-n-"
/// and "-n-*" (ASCII case-insensitive), by the stem after the first code point.
pub open spec fn i_dashed_stem(s: Seq<int>) -> IStem {
    if s.len() >= 1 && s[0] == 0x2D { i_stem(s.skip(1)) } else { IStem::Other }
}

/// "ASCII case-insensitive match" of `s` for "odd".
pub open spec fn i_is_odd(s: Seq<int>) -> bool { i_ci_match(s, seq![0x6F as int, 0x64, 0x64]) }

/// "ASCII case-insensitive match" of `s` for "even".
pub open spec fn i_is_even(s: Seq<int>) -> bool { i_ci_match(s, seq![0x65 as int, 0x76, 0x65, 0x6E]) }

/// The index of the first component value of `vs` from `p` on that is not a
/// `<whitespace-token>`.
pub open spec fn i_anb_skip(vs: Seq<ICv>, p: nat) -> nat
    decreases (if vs.len() > p { vs.len() - p } else { 0 }),
{
    if p < vs.len() && vs[p as int] == ICv::Token(ITok::Whitespace) { i_anb_skip(vs, p + 1) } else { p }
}

/// Nothing but whitespace from `p` on.
pub open spec fn i_anb_end(vs: Seq<ICv>, p: nat) -> bool { i_anb_skip(vs, p) >= vs.len() }

/// The token at `p`, if the component value there is a token.
pub open spec fn i_anb_tok(vs: Seq<ICv>, p: nat) -> Option<ITok> {
    if p < vs.len() {
        match vs[p as int] {
            ICv::Token(t) => Some(t),
            _ => None,
        }
    } else {
        None
    }
}

/// The value of an `<integer>`: its sign and its digits.
pub open spec fn i_int_value(n: INum) -> int {
    match n.sign {
        ISign::Minus => -(n.mantissa as int),
        _ => n.mantissa as int,
    }
}

/// After the `n` of a clause that has `A` and goes on with nothing (B is 0), a
/// `<signed-integer>`, or `['+' | '-'] <signless-integer>`; from index `p` on.
pub open spec fn i_anb_after_n(vs: Seq<ICv>, p: nat, a: int) -> Option<(int, int)> {
    let q = i_anb_skip(vs, p);
    if q >= vs.len() {
        Some((a, 0))
    } else {
        match i_anb_tok(vs, q) {
            Some(ITok::Number(n, true)) => {
                if n.sign != ISign::NoSign && i_anb_end(vs, q + 1) { Some((a, i_int_value(n))) } else { None }
            },
            Some(ITok::Delim(c)) => {
                if c == 0x2B || c == 0x2D {
                    let r = i_anb_skip(vs, q + 1);
                    match i_anb_tok(vs, r) {
                        Some(ITok::Number(n, true)) => {
                            if n.sign == ISign::NoSign && i_anb_end(vs, r + 1) {
                                Some((a, if c == 0x2D { -i_int_value(n) } else { i_int_value(n) }))
                            } else {
                                None
                            }
                        },
                        _ => None,
                    }
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// After the `n-` of a clause that has `A`: a `<signless-integer>`, B being its
/// negation.
pub open spec fn i_anb_after_ndash(vs: Seq<ICv>, p: nat, a: int) -> Option<(int, int)> {
    let q = i_anb_skip(vs, p);
    match i_anb_tok(vs, q) {
        Some(ITok::Number(n, true)) => {
            if n.sign == ISign::NoSign && i_anb_end(vs, q + 1) { Some((a, -i_int_value(n))) } else { None }
        },
        _ => None,
    }
}

/// What follows a stem, from index `p`, with `A`: the three kinds of stem.
pub open spec fn i_anb_after_stem(vs: Seq<ICv>, p: nat, a: int, stem: IStem) -> Option<(int, int)> {
    match stem {
        IStem::N => i_anb_after_n(vs, p, a),
        IStem::NDash => i_anb_after_ndash(vs, p, a),
        IStem::NDashDigits(d) => if i_anb_end(vs, p) { Some((a, -(d as int))) } else { None },
        IStem::Other => None,
    }
}

/// `<a-n-plus-b>`: whether the list of component values matches the production,
/// and if so A and B by the clauses.
pub open spec fn i_anb(vs: Seq<ICv>) -> Option<(int, int)> {
    let p = i_anb_skip(vs, 0);
    match i_anb_tok(vs, p) {
        Some(ITok::Ident(s)) => {
            if i_is_odd(s) {
                if i_anb_end(vs, p + 1) { Some((2, 1)) } else { None }
            } else if i_is_even(s) {
                if i_anb_end(vs, p + 1) { Some((2, 0)) } else { None }
            } else {
                match i_stem(s) {
                    IStem::Other => i_anb_after_stem(vs, p + 1, -1, i_dashed_stem(s)),
                    stem => i_anb_after_stem(vs, p + 1, 1, stem),
                }
            }
        },
        Some(ITok::Number(n, true)) => {
            if i_anb_end(vs, p + 1) { Some((0, i_int_value(n))) } else { None }
        },
        Some(ITok::Dimension(n, true, u)) => i_anb_after_stem(vs, p + 1, i_int_value(n), i_stem(u)),
        Some(ITok::Delim(c)) => {
            if c == 0x2B {
                match i_anb_tok(vs, p + 1) {
                    Some(ITok::Ident(s)) => i_anb_after_stem(vs, p + 2, 1, i_stem(s)),
                    _ => None,
                }
            } else {
                None
            }
        },
        _ => None,
    }
}

/// §9.1 "serialize an `<a-n-plus-b>` value": the digits of a natural number.
pub open spec fn i_serialize_nat(n: nat) -> Seq<int>
    decreases n,
{
    if n < 10 { seq![(0x30 + n) as int] } else { i_serialize_nat(n / 10) + seq![(0x30 + n % 10) as int] }
}

/// "the serialization" of an integer.
pub open spec fn i_serialize_int(v: int) -> Seq<int> {
    if v < 0 { seq![0x2D as int] + i_serialize_nat((-v) as nat) } else { i_serialize_nat(v as nat) }
}

/// §9.1 "serialize an `<a-n-plus-b>` value", with integer values |A| and |B|.
///
/// 1. "If |A| is zero, return the serialization of |B|."
/// 2. "Otherwise, let |result| initially be an empty string."
/// 3. "|A| is 1: append "n". |A| is -1: append "-n". |A| is non-zero: serialize
///    |A| and append it, then append "n"."
/// 4. "|B| is greater than zero: append "+", then the serialization of |B|. |B|
///    is less than zero: append the serialization of |B|."
/// 5. "Return |result|."
pub open spec fn i_serialize_anb(a: int, b: int) -> Seq<int> {
    if a == 0 {
        i_serialize_int(b)
    } else {
        let head = if a == 1 {
            seq![0x6E as int]
        } else if a == -1 {
            seq![0x2D as int, 0x6E]
        } else {
            i_serialize_int(a) + seq![0x6E as int]
        };
        if b > 0 {
            head + seq![0x2B as int] + i_serialize_int(b)
        } else if b < 0 {
            head + i_serialize_int(b)
        } else {
            head
        }
    }
}

} // verus!
