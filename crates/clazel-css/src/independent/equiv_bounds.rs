//! Facts about the independent tokenizer alone: what it consumes lies within the
//! stream, and its tokens come in order. The equivalence proofs for the parser need
//! them (a declaration's original text is a part of the stream), and the spec has
//! no statement of them.

#[cfg(verus_only)]
use super::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A stream of code points: none is EOF (or below).
pub open spec fn nonneg(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 0
}

/// The next input code point is EOF exactly past the end.
pub proof fn lemma_at_eof(s: Seq<int>, p: nat)
    requires
        nonneg(s),
    ensures
        (i_at(s, p) == EOF()) == (p >= s.len()),
{
}

pub proof fn lemma_whitespace_end_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_whitespace_end(s, p) <= s.len(),
    decreases s.len() - p,
{
    if i_whitespace(i_at(s, p)) {
        lemma_whitespace_end_bound(s, p + 1);
    }
}

pub proof fn lemma_digits_end_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_digits_end(s, p) <= s.len(),
    decreases s.len() - p,
{
    if i_digit(i_at(s, p)) {
        lemma_digits_end_bound(s, p + 1);
    }
}

pub proof fn lemma_skip_double_whitespace_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_skip_double_whitespace(s, p) <= s.len(),
    decreases s.len() - p,
{
    if i_whitespace(i_at(s, p)) && i_whitespace(i_at(s, p + 1)) {
        lemma_skip_double_whitespace_bound(s, p + 1);
    }
}

pub proof fn lemma_hex_run_bound(s: Seq<int>, p: nat, max: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p + i_hex_run(s, p, max) <= s.len(),
    decreases max,
{
    if max > 0 && i_hex_digit(i_at(s, p)) {
        lemma_hex_run_bound(s, p + 1, (max - 1) as nat);
    }
}

pub proof fn lemma_question_run_bound(s: Seq<int>, p: nat, max: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p + i_question_run(s, p, max) <= s.len(),
    decreases max,
{
    if max > 0 && i_at(s, p) == 0x3F {
        lemma_question_run_bound(s, p + 1, (max - 1) as nat);
    }
}

pub proof fn lemma_escaped_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_escaped(s, p).1 <= s.len(),
{
    if i_hex_digit(i_at(s, p)) {
        lemma_hex_run_bound(s, p + 1, 5);
    }
}

pub proof fn lemma_name_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_name(s, p).1 <= s.len(),
    decreases s.len() - p,
{
    let c = i_at(s, p);
    if i_ident(c) {
        lemma_name_bound(s, p + 1);
    } else if i_valid_escape(c, i_at(s, p + 1)) {
        lemma_escaped_bound(s, p + 1);
        lemma_name_bound(s, fwd(p, i_consume_escaped(s, p + 1).1));
    }
}

pub proof fn lemma_number_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_number(s, p).2 <= s.len(),
{
    let ch = i_at(s, p);
    let a = if ch == 0x2B || ch == 0x2D { p + 1 } else { p };
    lemma_digits_end_bound(s, a);
    let b = i_digits_end(s, a);
    if i_at(s, b) == 0x2E && i_digit(i_at(s, b + 1)) {
        lemma_digits_end_bound(s, b + 1);
    }
    let c = if i_at(s, b) == 0x2E && i_digit(i_at(s, b + 1)) { i_digits_end(s, b + 1) } else { b };
    let e1 = i_at(s, c + 1);
    let exp_signed = (e1 == 0x2B || e1 == 0x2D) && i_digit(i_at(s, c + 2));
    let ds = if exp_signed { c + 2 } else { c + 1 };
    if (i_at(s, c) == 0x45 || i_at(s, c) == 0x65) && (i_digit(e1) || exp_signed) {
        lemma_digits_end_bound(s, ds);
    }
}

pub proof fn lemma_numeric_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_numeric(s, p).1 <= s.len(),
{
    lemma_number_bound(s, p);
    let e = i_consume_number(s, p).2;
    lemma_name_bound(s, e);
}

pub proof fn lemma_string_bound(s: Seq<int>, p: nat, ending: int)
    requires
        nonneg(s),
        ending >= 0,
        p <= s.len(),
    ensures
        p <= i_consume_string(s, p, ending).2 <= s.len(),
    decreases s.len() - p,
{
    let c = i_at(s, p);
    if c == ending || c == EOF() || i_newline(c) {
    } else if c == 0x5C {
        let n = i_at(s, p + 1);
        if n == EOF() {
            lemma_string_bound(s, p + 1, ending);
        } else if i_newline(n) {
            lemma_string_bound(s, p + 2, ending);
        } else {
            lemma_escaped_bound(s, p + 1);
            lemma_string_bound(s, fwd(p, i_consume_escaped(s, p + 1).1), ending);
        }
    } else {
        lemma_string_bound(s, p + 1, ending);
    }
}

pub proof fn lemma_remnants_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_bad_url_remnants(s, p) <= s.len(),
    decreases s.len() - p,
{
    let c = i_at(s, p);
    if c != 0x29 && c != EOF() {
        if i_valid_escape(c, i_at(s, p + 1)) {
            lemma_escaped_bound(s, p + 1);
            lemma_remnants_bound(s, fwd(p, i_consume_escaped(s, p + 1).1));
        } else {
            lemma_remnants_bound(s, p + 1);
        }
    }
}

pub proof fn lemma_url_rest_bound(s: Seq<int>, p: nat, value: Seq<int>)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_url_rest(s, p, value).1 <= s.len(),
    decreases s.len() - p,
{
    let c = i_at(s, p);
    if c == 0x29 || c == EOF() {
    } else if i_whitespace(c) {
        lemma_whitespace_end_bound(s, p);
        let q = i_whitespace_end(s, p);
        lemma_remnants_bound(s, q);
    } else if c == 0x22 || c == 0x27 || c == 0x28 || i_non_printable(c) {
        lemma_remnants_bound(s, p + 1);
    } else if c == 0x5C {
        if i_valid_escape(c, i_at(s, p + 1)) {
            lemma_escaped_bound(s, p + 1);
            lemma_url_rest_bound(s, fwd(p, i_consume_escaped(s, p + 1).1), value + seq![i_consume_escaped(s, p + 1).0]);
        } else {
            lemma_remnants_bound(s, p + 1);
        }
    } else {
        lemma_url_rest_bound(s, p + 1, value + seq![c]);
    }
}

pub proof fn lemma_ident_like_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        p <= i_consume_ident_like(s, p).1 <= s.len(),
{
    lemma_name_bound(s, p);
    let (name, e) = i_consume_name(s, p);
    if i_ci_match(name, seq![0x75 as int, 0x72, 0x6C]) && i_at(s, e) == 0x28 {
        lemma_skip_double_whitespace_bound(s, e + 1);
        let e1 = i_skip_double_whitespace(s, e + 1);
        lemma_whitespace_end_bound(s, e1);
        lemma_url_rest_bound(s, i_whitespace_end(s, e1), seq![]);
    }
}

pub proof fn lemma_unicode_range_bound(s: Seq<int>, p: nat)
    requires
        nonneg(s),
        p + 2 <= s.len(),
    ensures
        p <= i_consume_unicode_range(s, p).1 <= s.len(),
{
    let a = p + 2;
    lemma_hex_run_bound(s, a, 6);
    let digits = i_hex_run(s, a, 6);
    if digits < 6 {
        lemma_question_run_bound(s, a + digits, (6 - digits) as nat);
    }
    let questions = if digits < 6 { i_question_run(s, a + digits, (6 - digits) as nat) } else { 0 };
    let first_end = a + digits + questions;
    if questions == 0 && i_at(s, first_end) == 0x2D && i_hex_digit(i_at(s, first_end + 1)) {
        lemma_hex_run_bound(s, first_end + 1, 6);
    }
}

/// A token that is not the `<EOF-token>` ends within the stream, and no token ends
/// before it starts.
pub proof fn lemma_token_bound(s: Seq<int>, p: nat, unicode_ranges: bool)
    requires
        nonneg(s),
        p <= s.len(),
    ensures
        i_consume_token(s, p, unicode_ranges).1 >= p,
        i_consume_token(s, p, unicode_ranges).0 != ITok::Eof ==> i_consume_token(s, p, unicode_ranges).1 <= s.len(),
{
    let c = i_at(s, p);
    if p < s.len() {
        lemma_whitespace_end_bound(s, p);
        lemma_name_bound(s, p + 1);
        lemma_numeric_bound(s, p);
        lemma_ident_like_bound(s, p);
        if c == 0x22 || c == 0x27 {
            lemma_string_bound(s, p + 1, c);
        }
        if c == 0x55 || c == 0x75 {
            if unicode_ranges && i_starts_unicode_range(c, i_at(s, p + 1), i_at(s, p + 2)) {
                lemma_unicode_range_bound(s, p);
            }
        }
    }
}

} // verus!
