//! The equivalence of the independent parser ([`super::parse`]) with the spec
//! ([`crate::parser::spec`]), over the token streams the tokenizer makes (see
//! [`super::equiv_stream`] for what that is).
//!
//! Every theorem says that what the spec's algorithm returns, mapped by
//! [`super::equiv_map`], is what the independent one returns, and that both are at
//! the same index. The recursive algorithms are proven together, by induction on
//! how many tokens are left.

use super::equiv_base::*;
use super::equiv_bounds::*;
use super::equiv_map::*;
use super::equiv_stream::*;
use super::equiv_tokenizer::*;
use super::parse::*;
use super::*;
use crate::parser::spec as ps;
use crate::tokenizer::spec as t;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use group_parser_base;

/// The image of a list with one more item.
pub proof fn lemma_cvs_push(vs: Seq<ps::ComponentValue>, v: ps::ComponentValue)
    ensures
        cvs_of(vs.push(v)) =~= cvs_of(vs).push(cv_of(v)),
{
}

/// The mirror variant of an opening token.
pub proof fn lemma_mirror(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
        ps::is_open_bracket(ps::next_token(st, p as int)),
    ensures
        tok_of(ps::mirror(ps::next_token(st, p as int))) == i_mirror(i_next(lex_of(st), p)),
        plain(ps::mirror(ps::next_token(st, p as int))),
        ps::mirror(ps::next_token(st, p as int)) is CloseCurly || ps::mirror(ps::next_token(st, p as int)) is CloseSquare
            || ps::mirror(ps::next_token(st, p as int)) is CloseParen,
{
    lemma_is(st, p, t::Token::OpenCurly);
    lemma_is(st, p, t::Token::OpenSquare);
    lemma_is(st, p, t::Token::OpenParen);
}

/// §5.4.10, §5.4.11 and §5.4.12 are proven together: "consume a component value",
/// "consume a simple block" and "consume a function", each through its loop.
pub proof fn lemma_component_value_equal(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        ({
            let (v, q) = ps::consume_a_component_value(st, p as int);
            let (mv, mq) = i_consume_component_value(lex_of(st), p);
            &&& cv_of(v) == mv
            &&& q == mq as int
            &&& (!ps::is_empty(st, p as int) ==> q > p)
            &&& (p < n_of(st) ==> q <= n_of(st))
        }),
    decreases ps::items_left(st, p as int), 1nat,
{
    if !ps::is_empty(st, p as int) {
        crate::parser::termination::lemma_component_value_advances(st, p as int);
    }
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    if ps::is_open_bracket(item) {
        lemma_mirror(st, p);
        let assoc = match item {
            ps::ComponentValue::Token { token } => token,
            _ => t::Token::Eof,
        };
        assert(!ps::is_empty(st, p as int));
        assert(ps::discard_a_token(st, p as int) == p + 1);
        assert(ps::consume_a_simple_block(st, p as int) == ps::simple_block_loop(
            st,
            p as int + 1,
            ps::mirror(item),
            assoc,
            Seq::empty(),
        ));
        assert(tok_of(assoc) == i_next(lex_of(st), p));
        lemma_simple_block_loop_equal(st, p + 1, ps::mirror(item), assoc, Seq::empty());
        assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
    } else if ps::is_function_token(item) {
        assert(!ps::is_empty(st, p as int));
        assert(ps::consume_a_function(st, p as int) == ps::function_loop(
            st,
            p as int + 1,
            ps::token_value(item),
            Seq::empty(),
        ));
        lemma_function_loop_equal(st, p + 1, ps::token_value(item), Seq::empty());
        assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
    }
}

/// "Process input" of §5.4.11.
pub proof fn lemma_simple_block_loop_equal(
    st: ps::TokenStream,
    p: nat,
    ending: t::Token,
    assoc: t::Token,
    value: Seq<ps::ComponentValue>,
)
    requires
        shaped(st),
        ending is CloseCurly || ending is CloseSquare || ending is CloseParen,
    ensures
        ({
            let (v, q) = ps::simple_block_loop(st, p as int, ending, assoc, value);
            let (mv, mq) = i_simple_block_loop(lex_of(st), p, tok_of(ending), cvs_of(value));
            &&& cv_of(v) == ICv::Block(tok_of(assoc), mv)
            &&& q == mq as int
            &&& q >= p
            &&& (p <= n_of(st) ==> q <= n_of(st))
        }),
    decreases ps::items_left(st, p as int), 2nat,
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, ending);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, ending)) {
        lemma_component_value_equal(st, p);
        let (v, next) = ps::consume_a_component_value(st, p as int);
        assert(!ps::is_empty(st, p as int));
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mv, mq) = i_consume_component_value(lex_of(st), p);
        assert(fwd(p, mq) == next as nat);
        lemma_cvs_push(value, v);
        assert(cvs_of(value.push(v)) == cvs_of(value) + seq![mv]);
        lemma_simple_block_loop_equal(st, next as nat, ending, assoc, value.push(v));
    }
}

/// "Process input" of §5.4.12.
pub proof fn lemma_function_loop_equal(st: ps::TokenStream, p: nat, name: Seq<u32>, value: Seq<ps::ComponentValue>)
    requires
        shaped(st),
    ensures
        ({
            let (v, q) = ps::function_loop(st, p as int, name, value);
            let (mv, mq) = i_function_loop(lex_of(st), p, cvs_of(value));
            &&& cv_of(v) == ICv::Function(ints(name), mv)
            &&& q == mq as int
            &&& q >= p
            &&& (p <= n_of(st) ==> q <= n_of(st))
        }),
    decreases ps::items_left(st, p as int), 2nat,
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::CloseParen);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, t::Token::CloseParen)) {
        lemma_component_value_equal(st, p);
        let (v, next) = ps::consume_a_component_value(st, p as int);
        assert(!ps::is_empty(st, p as int));
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mv, mq) = i_consume_component_value(lex_of(st), p);
        assert(fwd(p, mq) == next as nat);
        lemma_cvs_push(value, v);
        assert(cvs_of(value.push(v)) == cvs_of(value) + seq![mv]);
        lemma_function_loop_equal(st, next as nat, name, value.push(v));
    }
}


// ---------------------------------------------------------------------
// §5.4.9 Consume a list of component values

/// The independent transcription's stop token.
pub open spec fn stop_of(stop: Option<t::Token>) -> Option<ITok> {
    match stop {
        Some(k) => Some(tok_of(k)),
        None => None,
    }
}

/// A stop token is a token with no value of its own.
pub open spec fn stop_ok(stop: Option<t::Token>) -> bool {
    match stop {
        Some(k) => plain(k),
        None => true,
    }
}

/// "Process input" of §5.4.9.
pub proof fn lemma_list_loop_equal(
    st: ps::TokenStream,
    p: nat,
    stop: Option<t::Token>,
    nested: bool,
    values: Seq<ps::ComponentValue>,
)
    requires
        shaped(st),
        stop_ok(stop),
    ensures
        ({
            let (vals, q) = ps::list_of_component_values_loop(st, p as int, stop, nested, values);
            let (mvals, mq) = i_consume_list_of_component_values(lex_of(st), p, stop_of(stop), nested, cvs_of(values));
            &&& cvs_of(vals) == mvals
            &&& q == mq as int
            &&& q >= p
            &&& (p <= n_of(st) ==> q <= n_of(st))
        }),
    decreases ps::items_left(st, p as int),
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::CloseCurly);
    if stop is Some {
        lemma_is(st, p, stop->Some_0);
    }
    if !(ps::is(item, t::Token::Eof) || ps::is_stop(item, stop)) {
        if ps::is(item, t::Token::CloseCurly) {
            if !nested {
                let (token, next) = ps::consume_a_token(st, p as int);
                assert(!ps::is_empty(st, p as int));
                assert(next == p + 1);
                lemma_cvs_push(values, token);
                assert(cvs_of(values.push(token)) == cvs_of(values) + seq![ICv::Token(ITok::CloseCurly)]);
                lemma_list_loop_equal(st, p + 1, stop, nested, values.push(token));
            }
        } else {
            lemma_component_value_equal(st, p);
            let (v, next) = ps::consume_a_component_value(st, p as int);
            assert(!ps::is_empty(st, p as int));
            assert(next > p);
            assert(ps::moved(p as int, next) == next);
            let (mv, mq) = i_consume_component_value(lex_of(st), p);
            assert(fwd(p, mq) == next as nat);
            lemma_cvs_push(values, v);
            assert(cvs_of(values.push(v)) == cvs_of(values) + seq![mv]);
            lemma_list_loop_equal(st, next as nat, stop, nested, values.push(v));
        }
    }
}

/// The loop of §5.4.9 only adds to the list it is given.
pub proof fn lemma_list_loop_extends(
    st: ps::TokenStream,
    p: nat,
    stop: Option<t::Token>,
    nested: bool,
    values: Seq<ps::ComponentValue>,
)
    requires
        shaped(st),
        stop_ok(stop),
    ensures
        ({
            let (vals, q) = ps::list_of_component_values_loop(st, p as int, stop, nested, values);
            &&& vals.len() >= values.len()
            &&& vals.subrange(0, values.len() as int) =~= values
        }),
    decreases ps::items_left(st, p as int),
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::CloseCurly);
    if stop is Some {
        lemma_is(st, p, stop->Some_0);
    }
    if !(ps::is(item, t::Token::Eof) || ps::is_stop(item, stop)) {
        if ps::is(item, t::Token::CloseCurly) {
            if !nested {
                let (token, next) = ps::consume_a_token(st, p as int);
                assert(!ps::is_empty(st, p as int));
                lemma_list_loop_extends(st, p + 1, stop, nested, values.push(token));
                assert(values.push(token).subrange(0, values.len() as int) =~= values);
            }
        } else {
            if !ps::is_empty(st, p as int) {
                crate::parser::termination::lemma_component_value_advances(st, p as int);
            }
            let (v, next) = ps::consume_a_component_value(st, p as int);
            assert(!ps::is_empty(st, p as int));
            assert(ps::moved(p as int, next) == next);
            lemma_list_loop_extends(st, next as nat, stop, nested, values.push(v));
            assert(values.push(v).subrange(0, values.len() as int) =~= values);
        }
    }
}

/// An item that is a token is one token.
pub proof fn lemma_cv_token_one(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        ps::consume_a_component_value(st, p as int).0 is Token ==> ps::consume_a_component_value(st, p as int).1
            == p + 1,
{
    assert(lex_of(st).len() == n_of(st));
    lemma_component_value_equal(st, p);
    let (v, q) = ps::consume_a_component_value(st, p as int);
    let (mv, mq) = i_consume_component_value(lex_of(st), p);
    if v is Token {
        assert(mv is Token);
        assert(mq == p + 1);
    }
}

/// Where the first `j` items of a list end: if what comes after them is only single
/// tokens, the rest of the list is as many tokens as it has items.
#[verifier::rlimit(200)]
pub proof fn lemma_list_skip(
    st: ps::TokenStream,
    p: nat,
    stop: Option<t::Token>,
    nested: bool,
    values: Seq<ps::ComponentValue>,
    j: nat,
)
    requires
        shaped(st),
        stop_ok(stop),
    ensures
        ({
            let (vals, q) = ps::list_of_component_values_loop(st, p as int, stop, nested, values);
            let m = vals.len() - values.len();
            (j <= m && (forall|k: int| j <= k < m ==> #[trigger] vals[values.len() + k] is Token)) ==> (
            i_skip_component_values(lex_of(st), p, j) + (m - j) == q)
        }),
    decreases ps::items_left(st, p as int),
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::CloseCurly);
    if stop is Some {
        lemma_is(st, p, stop->Some_0);
    }
    let (vals, q) = ps::list_of_component_values_loop(st, p as int, stop, nested, values);
    let m = vals.len() - values.len();
    if j <= m && (forall|k: int| j <= k < m ==> #[trigger] vals[values.len() + k] is Token) {
        if ps::is(item, t::Token::Eof) || ps::is_stop(item, stop) {
            assert(m == 0);
            assert(j == 0);
            assert(i_skip_component_values(lex_of(st), p, 0) == p);
        } else if ps::is(item, t::Token::CloseCurly) && nested {
            assert(m == 0);
            assert(j == 0);
            assert(i_skip_component_values(lex_of(st), p, 0) == p);
        } else {
            // One item is consumed here, at p.
            let (v, next) = if ps::is(item, t::Token::CloseCurly) {
                ps::consume_a_token(st, p as int)
            } else {
                ps::consume_a_component_value(st, p as int)
            };
            assert(!ps::is_empty(st, p as int));
            lemma_component_value_equal(st, p);
            crate::parser::termination::lemma_component_value_advances(st, p as int);
            let (mv, mq) = i_consume_component_value(lex_of(st), p);
            let (cvv, cvnext) = ps::consume_a_component_value(st, p as int);
            if ps::is(item, t::Token::CloseCurly) {
                assert(cvv == v && cvnext == next);
            }
            assert(cvnext > p);
            assert(fwd(p, mq) == cvnext as nat);
            let values2 = values.push(v);
            assert(ps::moved(p as int, cvnext) == cvnext);
            lemma_list_loop_extends(st, next as nat, stop, nested, values2);
            lemma_list_skip(st, next as nat, stop, nested, values2, if j == 0 { 0 } else { (j - 1) as nat });
            assert(m >= 1);
            assert(vals.subrange(0, values2.len() as int)[values.len() as int] == values2[values.len() as int]);
            assert(vals[values.len() as int] == v);
            if j == 0 {
                assert(vals[values.len() as int + 0] is Token);
                assert(v is Token);
                lemma_cv_token_one(st, p);
                assert(cvnext == p + 1);
                assert(forall|k: int| 0 <= k < m - 1 ==> #[trigger] vals[values2.len() + k] is Token) by {
                    assert forall|k: int| 0 <= k < m - 1 implies #[trigger] vals[values2.len() + k] is Token by {
                        assert(vals[values.len() + (k + 1)] is Token);
                    }
                }
            } else {
                assert(forall|k: int| j - 1 <= k < m - 1 ==> #[trigger] vals[values2.len() + k] is Token) by {
                    assert forall|k: int| j - 1 <= k < m - 1 implies #[trigger] vals[values2.len() + k] is Token by {
                        assert(vals[values.len() + (k + 1)] is Token);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The remnants of a bad declaration

/// §5.4.7 "consume the remnants of a bad declaration".
pub proof fn lemma_remnants_equal(st: ps::TokenStream, p: nat, nested: bool)
    requires
        shaped(st),
    ensures
        ps::consume_the_remnants_of_a_bad_declaration(st, p as int, nested) == i_consume_bad_declaration_remnants(
            lex_of(st),
            p,
            nested,
        ) as int,
        ps::consume_the_remnants_of_a_bad_declaration(st, p as int, nested) >= p,
        p <= n_of(st) ==> ps::consume_the_remnants_of_a_bad_declaration(st, p as int, nested) <= n_of(st),
    decreases ps::items_left(st, p as int),
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::Semicolon);
    lemma_is(st, p, t::Token::CloseCurly);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, t::Token::Semicolon)) {
        if ps::is(item, t::Token::CloseCurly) {
            if !nested {
                assert(!ps::is_empty(st, p as int));
                assert(ps::discard_a_token(st, p as int) == p + 1);
                lemma_remnants_equal(st, p + 1, nested);
            }
        } else {
            lemma_component_value_equal(st, p);
            let (_v, next) = ps::consume_a_component_value(st, p as int);
            assert(!ps::is_empty(st, p as int));
            assert(next > p);
            assert(ps::moved(p as int, next) == next);
            let (_mv, mq) = i_consume_component_value(lex_of(st), p);
            assert(fwd(p, mq) == next as nat);
            lemma_remnants_equal(st, next as nat, nested);
        }
    }
}


// ---------------------------------------------------------------------
// Helpers of §5.4.7 "consume a declaration"

/// A component value is a whitespace token exactly when its image is.
pub proof fn lemma_cv_of_ws(x: ps::ComponentValue)
    ensures
        (cv_of(x) == ICv::Token(ITok::Whitespace)) == (x == (ps::ComponentValue::Token { token: t::Token::Whitespace })),
{
    if let ps::ComponentValue::Token { token } = x {
        lemma_tok_of_plain(token, t::Token::Whitespace);
    }
}

/// "While the last item in the list is a whitespace token, remove that token."
pub proof fn lemma_strip_equal(v: Seq<ps::ComponentValue>)
    ensures
        cvs_of(ps::without_trailing_whitespace(v)) == i_strip_trailing_ws(cvs_of(v)),
    decreases v.len(),
{
    if v.len() > 0 {
        lemma_cv_of_ws(v.last());
        if ps::is_whitespace_token(v.last()) {
            lemma_strip_equal(v.drop_last());
            assert(cvs_of(v.drop_last()) =~= cvs_of(v).subrange(0, cvs_of(v).len() - 1));
        }
    }
}

/// A list without its trailing whitespace is its prefix of that length.
pub proof fn lemma_strip_is_prefix(v: Seq<ICv>)
    ensures
        i_strip_trailing_ws(v) =~= v.subrange(0, i_strip_trailing_ws(v).len() as int),
        i_strip_trailing_ws(v).len() <= v.len(),
        forall|k: int| i_strip_trailing_ws(v).len() <= k < v.len() ==> #[trigger] v[k] == ICv::Token(ITok::Whitespace),
    decreases v.len(),
{
    if v.len() > 0 && i_is_ws(v[v.len() - 1]) {
        lemma_strip_is_prefix(v.subrange(0, v.len() - 1));
        let w = v.subrange(0, v.len() - 1);
        assert(i_strip_trailing_ws(v) == i_strip_trailing_ws(w));
        assert(w.subrange(0, i_strip_trailing_ws(w).len() as int) =~= v.subrange(0, i_strip_trailing_ws(w).len() as int));
        assert forall|k: int| i_strip_trailing_ws(v).len() <= k < v.len() implies #[trigger] v[k]
            == ICv::Token(ITok::Whitespace) by {
            if k < v.len() - 1 {
                assert(w[k] == v[k]);
            }
        }
    } else {
        assert(v.subrange(0, v.len() as int) =~= v);
    }
}

/// The index of the last item that is not whitespace, one more.
pub proof fn lemma_last_non_whitespace(v: Seq<ps::ComponentValue>, end: int)
    requires
        0 <= end <= v.len(),
    ensures
        ps::last_non_whitespace(v, end) + 1 == i_strip_trailing_ws(cvs_of(v).subrange(0, end)).len(),
        ps::last_non_whitespace(v, end) < end,
    decreases end,
{
    if end > 0 {
        lemma_cv_of_ws(v[end - 1]);
        let w = cvs_of(v).subrange(0, end);
        assert(w[end - 1] == cv_of(v[end - 1]));
        if ps::is_whitespace_token(v[end - 1]) {
            lemma_last_non_whitespace(v, end - 1);
            assert(w.subrange(0, end - 1) =~= cvs_of(v).subrange(0, end - 1));
        }
    }
}

/// `cvs_of` of a part and of a concatenation.
pub proof fn lemma_cvs_subrange(v: Seq<ps::ComponentValue>, a: int, b: int)
    requires
        0 <= a <= b <= v.len(),
    ensures
        cvs_of(v.subrange(a, b)) =~= cvs_of(v).subrange(a, b),
{
}

/// `cvs_of` of a concatenation.
pub proof fn lemma_cvs_add(x: Seq<ps::ComponentValue>, y: Seq<ps::ComponentValue>)
    ensures
        cvs_of(x + y) =~= cvs_of(x) + cvs_of(y),
{
}

/// An ASCII case-insensitive match is the same on the two sides.
pub proof fn lemma_ci_match(x: Seq<u32>, lower: Seq<u32>)
    ensures
        ps::ascii_case_insensitive_match(x, lower) == i_ci_match(ints(x), ints(lower)),
{
    if x.len() == lower.len() {
        lemma_matches_from(x, lower, 0);
        assert(ints(x).len() == x.len());
    }
}

/// `matches_from` is a statement about every code point from there on.
pub proof fn lemma_matches_from(x: Seq<u32>, lower: Seq<u32>, i: int)
    requires
        x.len() == lower.len(),
        0 <= i,
    ensures
        ps::matches_from(x, lower, i) == (forall|k: int|
            i <= k < x.len() ==> i_ascii_lower(ints(x)[k]) == #[trigger] ints(lower)[k]),
    decreases x.len() - i,
{
    if i < x.len() {
        lemma_matches_from(x, lower, i + 1);
        assert(ints(x)[i] == x[i] as int);
        assert(ints(lower)[i] == lower[i] as int);
        assert(i_ascii_lower(ints(x)[i]) == (ps::ascii_lowercase(x[i]) as int));
    }
}

/// "important" is the same string on both sides.
pub proof fn lemma_important_string()
    ensures
        ints(ps::important_string()) =~= seq![0x69 as int, 0x6D, 0x70, 0x6F, 0x72, 0x74, 0x61, 0x6E, 0x74],
        ints(ps::unicode_range_string()) =~= seq![
            0x75 as int, 0x6E, 0x69, 0x63, 0x6F, 0x64, 0x65, 0x2D, 0x72, 0x61, 0x6E, 0x67, 0x65,
        ],
{
}

/// "If the last two non-whitespace items are "!" and "important"".
#[verifier::rlimit(400)]
pub proof fn lemma_important_equal(list: Seq<ps::ComponentValue>)
    ensures
        ({
            let (value_s, important_s) = match ps::important_at(list) {
                Some((first, second)) => (list.remove(second).remove(first), true),
                None => (list, false),
            };
            let (taken, important) = i_take_important(cvs_of(list));
            &&& cvs_of(value_s) =~= taken
            &&& important_s == important
        }),
{
    let v = cvs_of(list);
    let len = list.len() as int;
    lemma_last_non_whitespace(list, len);
    assert(v.subrange(0, len) =~= v);
    let second = ps::last_non_whitespace(list, len);
    let ia = i_strip_trailing_ws(v).len();
    assert(second + 1 == ia);
    lemma_strip_is_prefix(v);
    let a = i_strip_trailing_ws(v);
    if ia > 0 {
        assert(0 <= second < len);
        lemma_last_non_whitespace(list, second);
        let first = ps::last_non_whitespace(list, second);
        assert(first < second);
        let imp: nat = (ia - 1) as nat;
        assert(a.subrange(0, imp as int) =~= v.subrange(0, second));
        let ib = i_strip_trailing_ws(a.subrange(0, imp as int)).len();
        assert(first + 1 == ib);
        lemma_important_string();
        if first >= 0 {
            lemma_ci_match(ps::token_value(list[second]), ps::important_string());
            lemma_cv_of_ws(list[second]);
            assert(a[imp as int] == v[second]);
            assert(cv_of(list[first]) == v[first]);
            // The pieces of the result.
            if ps::important_at(list) is Some {
                assert(list.remove(second).remove(first) =~= list.subrange(0, first) + list.subrange(first + 1, second)
                    + list.subrange(second + 1, len));
                lemma_cvs_add(list.subrange(0, first) + list.subrange(first + 1, second), list.subrange(second + 1, len));
                lemma_cvs_add(list.subrange(0, first), list.subrange(first + 1, second));
                lemma_cvs_subrange(list, 0, first);
                lemma_cvs_subrange(list, first + 1, second);
                lemma_cvs_subrange(list, second + 1, len);
            }
        }
    }
}

/// "a custom property name string".
pub proof fn lemma_custom_name(name: Seq<u32>)
    ensures
        ps::is_custom_property_name_string(name) == i_custom_property_name(ints(name)),
{
}

/// Where a `{}-block` is, in the image.
pub proof fn lemma_curly_equal(v: Seq<ps::ComponentValue>)
    ensures
        ps::has_curly_block_and_another(v) == i_curly_block_with_others(cvs_of(v)),
{
    lemma_has_curly_iff(v, 0);
    assert forall|k: int| 0 <= k < v.len() implies i_is_curly_block(cvs_of(v)[k]) == ps::is_curly_block(v[k]) by {
        lemma_curly_image(v[k]);
    }
    assert forall|k: int| 0 <= k < v.len() implies i_is_ws(cvs_of(v)[k]) == ps::is_whitespace_token(v[k]) by {
        lemma_cv_of_ws(v[k]);
    }
    if ps::has_curly_block_and_another(v) {
        let i = choose|i: int| 0 <= i < v.len() && ps::is_curly_block(v[i]);
        lemma_count_other(v, 0, i);
        let j = choose|j: int| 0 <= j < v.len() && j != i && !ps::is_whitespace_token(v[j]);
        assert(i_is_curly_block(cvs_of(v)[i]) && !i_is_ws(cvs_of(v)[j]));
    }
    if i_curly_block_with_others(cvs_of(v)) {
        let (i, j) = choose|i: int, j: int|
            0 <= i < v.len() && 0 <= j < v.len() && i != j && i_is_curly_block(cvs_of(v)[i]) && !i_is_ws(cvs_of(v)[j]);
        assert(ps::is_curly_block(v[i]));
        assert(!ps::is_whitespace_token(v[i]));
        lemma_count_two(v, 0, i, j);
    }
}

/// A `{}-block` has the same image test.
pub proof fn lemma_curly_image(x: ps::ComponentValue)
    ensures
        i_is_curly_block(cv_of(x)) == ps::is_curly_block(x),
{
    if let ps::ComponentValue::SimpleBlock { associated_token, value } = x {
        lemma_tok_of_plain(associated_token, t::Token::OpenCurly);
    }
}

/// `has_curly_block` from `i` on is whether any item from there on is one.
pub proof fn lemma_has_curly_iff(v: Seq<ps::ComponentValue>, i: int)
    requires
        0 <= i,
    ensures
        ps::has_curly_block(v, i) == (exists|k: int| i <= k < v.len() && ps::is_curly_block(v[k])),
    decreases v.len() - i,
{
    if i < v.len() {
        lemma_has_curly_iff(v, i + 1);
    }
}

/// At least two items are not whitespace when `i` and `j` are two of them.
pub proof fn lemma_count_two(v: Seq<ps::ComponentValue>, k: int, i: int, j: int)
    requires
        0 <= k,
        k <= i < v.len(),
        k <= j < v.len(),
        i != j,
        !ps::is_whitespace_token(v[i]),
        !ps::is_whitespace_token(v[j]),
    ensures
        ps::non_whitespace_count(v, k) >= 2,
    decreases v.len() - k,
{
    if k < v.len() {
        if ps::is_whitespace_token(v[k]) {
            lemma_count_two(v, k + 1, i, j);
        } else if i == k {
            lemma_count_one(v, k + 1, j);
        } else if j == k {
            lemma_count_one(v, k + 1, i);
        } else {
            lemma_count_two(v, k + 1, i, j);
        }
    }
}

/// At least one item is not whitespace when `i` is one.
pub proof fn lemma_count_one(v: Seq<ps::ComponentValue>, k: int, i: int)
    requires
        0 <= k,
        k <= i < v.len(),
        !ps::is_whitespace_token(v[i]),
    ensures
        ps::non_whitespace_count(v, k) >= 1,
    decreases v.len() - k,
{
    if k < v.len() {
        if k < i {
            lemma_count_one(v, k + 1, i);
        }
    }
}

/// When two or more items are not whitespace, one other than `i` is.
pub proof fn lemma_count_other(v: Seq<ps::ComponentValue>, k: int, i: int)
    requires
        0 <= k,
        k <= i < v.len(),
        ps::non_whitespace_count(v, k) >= 2,
        !ps::is_whitespace_token(v[i]),
    ensures
        exists|j: int| k <= j < v.len() && j != i && !ps::is_whitespace_token(v[j]),
    decreases v.len() - k,
{
    if k < v.len() {
        if ps::is_whitespace_token(v[k]) {
            lemma_count_other(v, k + 1, i);
        } else if k == i {
            // The rest has one more.
            lemma_count_some(v, k + 1);
        } else {
            assert(!ps::is_whitespace_token(v[k]));
        }
    }
}

/// When one or more items from `k` on are not whitespace, one is.
pub proof fn lemma_count_some(v: Seq<ps::ComponentValue>, k: int)
    requires
        0 <= k,
        ps::non_whitespace_count(v, k) >= 1,
    ensures
        exists|j: int| k <= j < v.len() && !ps::is_whitespace_token(v[j]),
    decreases v.len() - k,
{
    if k < v.len() {
        if ps::is_whitespace_token(v[k]) {
            lemma_count_some(v, k + 1);
        }
    }
}

/// Two spans of the stream: the start of one is not past the end of a later one.
pub proof fn lemma_spans_monotone(st: ps::TokenStream, a: int, b: int)
    requires
        shaped(st),
        0 <= a <= b < n_of(st),
    ensures
        st.source->Some_0.spans[a].start <= st.source->Some_0.spans[b].end,
    decreases b - a,
{
    if a < b {
        lemma_spans_monotone(st, a + 1, b);
    }
}

/// "the segment of the original source text string corresponding to the tokens".
pub proof fn lemma_segment_equal(st: ps::TokenStream, a: nat, b: nat)
    requires
        shaped(st),
        b <= n_of(st),
    ensures
        ps::segment(st, a as int, b as int) is Some,
        ints(ps::segment(st, a as int, b as int)->Some_0) == i_text_of(lex_of(st), src_of(st), a, b),
{
    assert(lex_of(st).len() == n_of(st));
    if a < b {
        lemma_spans_monotone(st, a as int, b as int - 1);
        let text = st.source->Some_0.text;
        let x = st.source->Some_0.spans[a as int].start;
        let y = st.source->Some_0.spans[b as int - 1].end;
        assert(0 <= st.source->Some_0.spans[a as int].start);
        assert(st.source->Some_0.spans[b as int - 1].end <= text.len());
        assert(st.source->Some_0.spans[a as int].end <= text.len());
        assert(0 <= x <= y <= text.len());
        lemma_ints_subrange(text, x, y);
    } else {
        assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
    }
}

} // verus!
