//! The equivalence of the independent parser ([`super::parse`]) with the spec
//! ([`crate::parser::spec`]), over the token streams the tokenizer makes (see
//! [`super::equiv_stream`] for what that is).
//!
//! Every theorem says that what the spec's algorithm returns, mapped by
//! [`super::equiv_map`], is what the independent one returns, and that both are at
//! the same index. The recursive algorithms are proven together, by induction on
//! how many tokens are left.

#[cfg(verus_only)]
use super::equiv_base::*;
#[cfg(verus_only)]
use super::equiv_bounds::*;
#[cfg(verus_only)]
use super::equiv_map::*;
#[cfg(verus_only)]
use super::equiv_stream::*;
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

broadcast use super::equiv_stream::lemma_next, super::equiv_stream::lemma_is, super::equiv_stream::lemma_is_empty,
    super::equiv_stream::lemma_class_function, super::equiv_stream::lemma_class_at_keyword,
    super::equiv_stream::lemma_class_ident, super::equiv_stream::lemma_class_open_bracket,
    super::equiv_stream::lemma_discard;

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
        assert(0 <= st.source->Some_0.spans[b as int - 1].start);
        assert(st.source->Some_0.spans[b as int - 1].end <= text.len());
        assert(st.source->Some_0.spans[a as int].end <= text.len());
        assert(0 <= x <= y <= text.len());
        lemma_ints_subrange(text, x, y);
    } else {
        assert(ints(Seq::<u32>::empty()) =~= Seq::<int>::empty());
    }
}


// ---------------------------------------------------------------------
// Streams made from strings

/// The stream the spec makes of a string is the independent tokenizer's.
pub proof fn lemma_token_stream_shaped(s: Seq<u32>, unicode_ranges_allowed: bool)
    requires
        valid(s),
    ensures
        shaped(ps::token_stream(s, unicode_ranges_allowed)),
        lex_of(ps::token_stream(s, unicode_ranges_allowed)) =~= i_tokenize(ints(s), unicode_ranges_allowed),
        src_of(ps::token_stream(s, unicode_ranges_allowed)) =~= ints(s),
{
    let st = ps::token_stream(s, unicode_ranges_allowed);
    let tokens = t::tokenize_with(s, unicode_ranges_allowed);
    let lexes = i_tokenize(ints(s), unicode_ranges_allowed);
    theorem_tokenize_equals(s, unicode_ranges_allowed);
    lemma_spans_loop_equal(s, 0, unicode_ranges_allowed, Seq::empty());
    lemma_tokenize_wellformed(s, 0, unicode_ranges_allowed);
    let spans = ps::spans_loop(s, 0, unicode_ranges_allowed, Seq::empty());
    assert(st.tokens =~= ps::as_items(tokens));
    assert(tokens.len() == lexes.len() + 1);
    assert(spans.len() == lexes.len() + 1);
    assert(st.tokens.len() == tokens.len());
    assert forall|i: int| 0 <= i < st.tokens.len() implies #[trigger] st.tokens[i] is Token by {
        assert(st.tokens[i] == (ps::ComponentValue::Token { token: tokens[i] }));
    }
    // The last token is the EOF token, and no other is.
    let ts = tok_seq_of(tokens);
    assert(ts =~= toks_of(lexes) + seq![ITok::Eof]);
    assert(ts[tokens.len() - 1] == tok_of(tokens[tokens.len() - 1]));
    assert((toks_of(lexes) + seq![ITok::Eof])[lexes.len() as int] == ITok::Eof);
    assert(tok_of(tokens[tokens.len() - 1]) == ITok::Eof);
    lemma_tok_of_plain(tokens[tokens.len() - 1], t::Token::Eof);
    assert forall|i: int| 0 <= i < st.tokens.len() - 1 implies !(#[trigger] tok_at(st, i) is Eof) by {
        assert(ts[i] == tok_of(tokens[i]));
        assert((toks_of(lexes) + seq![ITok::Eof])[i] == lexes[i].tok);
        assert(tok_of(tokens[i]) == lexes[i].tok);
        assert(lexes[i].tok != ITok::Eof);
        assert(tok_at(st, i) == tokens[i]);
    }
    assert forall|i: int| 0 <= i < st.tokens.len() - 1 implies 0 <= #[trigger] st.source->Some_0.spans[i].start
        <= st.source->Some_0.spans[i].end <= st.source->Some_0.text.len() by {
        assert(spans[i] == (ps::Span { start: lexes[i].start as int, end: lexes[i].end as int }));
    }
    assert forall|i: int| 0 <= i && i + 1 < st.tokens.len() - 1 implies #[trigger] st.source->Some_0.spans[i].end
        <= st.source->Some_0.spans[i + 1].start by {
        assert(spans[i] == (ps::Span { start: lexes[i].start as int, end: lexes[i].end as int }));
        assert(spans[i + 1] == (ps::Span { start: lexes[i + 1].start as int, end: lexes[i + 1].end as int }));
    }
    assert(lex_of(st) =~= lexes) by {
        assert(lex_of(st).len() == lexes.len());
        assert forall|i: int| 0 <= i < lexes.len() implies lex_of(st)[i] == lexes[i] by {
            assert(ts[i] == tok_of(tokens[i]));
            assert((toks_of(lexes) + seq![ITok::Eof])[i] == lexes[i].tok);
            assert(tok_of(tokens[i]) == lexes[i].tok);
            assert(spans[i] == (ps::Span { start: lexes[i].start as int, end: lexes[i].end as int }));
        }
    }
}

/// Stripping a list that ends in whitespace.
pub proof fn lemma_strip_append_ws(x: Seq<ICv>, w: Seq<ICv>)
    requires
        forall|k: int| 0 <= k < w.len() ==> #[trigger] w[k] == ICv::Token(ITok::Whitespace),
    ensures
        i_strip_trailing_ws(x + w) == i_strip_trailing_ws(x),
    decreases w.len(),
{
    if w.len() > 0 {
        let w2 = w.subrange(0, w.len() - 1);
        assert((x + w).subrange(0, (x + w).len() - 1) =~= x + w2);
        assert(w[w.len() - 1] == ICv::Token(ITok::Whitespace));
        assert((x + w)[(x + w).len() - 1] == w[w.len() - 1]);
        assert forall|k: int| 0 <= k < w2.len() implies #[trigger] w2[k] == ICv::Token(ITok::Whitespace) by {
            assert(w2[k] == w[k]);
        }
        lemma_strip_append_ws(x, w2);
    } else {
        assert(x + w =~= x);
    }
}

/// What comes after the value of a declaration, in the list it was made from, is single
/// tokens: the whitespace, and the "!" and "important" that were taken.
#[verifier::rlimit(400)]
pub proof fn lemma_declaration_tail(list: Seq<ps::ComponentValue>)
    ensures
        ({
            let (taken, _flag) = match ps::important_at(list) {
                Some((first, second)) => (list.remove(second).remove(first), true),
                None => (list, false),
            };
            let value = ps::without_trailing_whitespace(taken);
            forall|k: int| value.len() <= k < list.len() ==> #[trigger] list[k] is Token
        }),
{
    lemma_important_equal(list);
    let v = cvs_of(list);
    let len = list.len() as int;
    lemma_last_non_whitespace(list, len);
    assert(v.subrange(0, len) =~= v);
    let (taken, flag) = match ps::important_at(list) {
        Some((first, second)) => (list.remove(second).remove(first), true),
        None => (list, false),
    };
    lemma_strip_equal(taken);
    let value = ps::without_trailing_whitespace(taken);
    match ps::important_at(list) {
        None => {
            lemma_strip_is_prefix(v);
            assert(cvs_of(taken) == v);
            assert forall|k: int| value.len() <= k < list.len() implies #[trigger] list[k] is Token by {
                assert(v[k] == ICv::Token(ITok::Whitespace));
                lemma_cv_of_ws(list[k]);
            }
        },
        Some((first, second)) => {
            let ia = i_strip_trailing_ws(v).len();
            assert(second + 1 == ia);
            lemma_strip_is_prefix(v);
            assert(0 <= second < len);
            lemma_last_non_whitespace(list, second);
            assert(first < second);
            let w = v.subrange(0, second);
            lemma_strip_is_prefix(w);
            let ib = i_strip_trailing_ws(w).len();
            assert(first + 1 == ib);
            // The items after "!" are whitespace, but "important".
            let head = v.subrange(0, first);
            let ws1 = v.subrange(first + 1, second);
            let ws2 = v.subrange(second + 1, len);
            assert(forall|k: int| 0 <= k < ws1.len() ==> #[trigger] ws1[k] == ICv::Token(ITok::Whitespace)) by {
                assert forall|k: int| 0 <= k < ws1.len() implies #[trigger] ws1[k] == ICv::Token(ITok::Whitespace) by {
                    assert(ws1[k] == v[first + 1 + k]);
                    assert(w[first + 1 + k] == v[first + 1 + k]);
                }
            }
            assert(forall|k: int| 0 <= k < ws2.len() ==> #[trigger] ws2[k] == ICv::Token(ITok::Whitespace)) by {
                assert forall|k: int| 0 <= k < ws2.len() implies #[trigger] ws2[k] == ICv::Token(ITok::Whitespace) by {
                    assert(ws2[k] == v[second + 1 + k]);
                }
            }
            assert(cvs_of(taken) =~= head + (ws1 + ws2)) by {
                assert(taken =~= list.subrange(0, first) + list.subrange(first + 1, second) + list.subrange(second + 1, len));
                lemma_cvs_add(list.subrange(0, first) + list.subrange(first + 1, second), list.subrange(second + 1, len));
                lemma_cvs_add(list.subrange(0, first), list.subrange(first + 1, second));
                lemma_cvs_subrange(list, 0, first);
                lemma_cvs_subrange(list, first + 1, second);
                lemma_cvs_subrange(list, second + 1, len);
            }
            assert(forall|k: int| 0 <= k < (ws1 + ws2).len() ==> #[trigger] (ws1 + ws2)[k] == ICv::Token(ITok::Whitespace))
                by {
                assert forall|k: int| 0 <= k < (ws1 + ws2).len() implies #[trigger] (ws1 + ws2)[k]
                    == ICv::Token(ITok::Whitespace) by {
                    if k < ws1.len() {
                        assert((ws1 + ws2)[k] == ws1[k]);
                    } else {
                        assert((ws1 + ws2)[k] == ws2[k - ws1.len()]);
                    }
                }
            }
            lemma_strip_append_ws(head, ws1 + ws2);
            lemma_strip_is_prefix(head);
            assert(cvs_of(value) == i_strip_trailing_ws(cvs_of(taken)));
            assert(value.len() == i_strip_trailing_ws(head).len());
            assert forall|k: int| value.len() <= k < list.len() implies #[trigger] list[k] is Token by {
                lemma_cv_of_ws(list[k]);
                if k < first {
                    assert(head[k] == v[k]);
                    assert(v[k] == ICv::Token(ITok::Whitespace));
                } else if k == first {
                } else if k < second {
                    assert(ws1[k - first - 1] == v[k]);
                } else if k == second {
                } else {
                    assert(ws2[k - second - 1] == v[k]);
                }
            }
        },
    }
}



// ---------------------------------------------------------------------
// §5.4.7 Consume a declaration

/// A declaration, if there is one.
pub open spec fn opt_decl_of(d: Option<ps::Declaration>) -> Option<IDecl> {
    match d {
        Some(x) => Some(decl_of(x)),
        None => None,
    }
}

/// "Discard whitespace" stays within the stream.
pub proof fn lemma_discard_whitespace_bound(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        p <= i_discard_whitespace(lex_of(st), p) <= n_of(st),
    decreases ps::items_left(st, p as int),
{
    assert(lex_of(st).len() == n_of(st));
    if i_next(lex_of(st), p) == ITok::Whitespace {
        lemma_discard_whitespace_bound(st, p + 1);
    }
}

/// A part of a string of code points is one.
pub proof fn lemma_valid_subrange(s: Seq<u32>, a: int, b: int)
    requires
        valid(s),
        0 <= a <= b <= s.len(),
    ensures
        valid(s.subrange(a, b)),
{
    assert forall|i: int| 0 <= i < s.subrange(a, b).len() implies #[trigger] s.subrange(a, b)[i] <= 0x10FFFF by {
        assert(s.subrange(a, b)[i] == s[a + i]);
    }
}

/// The unicode-range value of a segment of a stream.
pub proof fn lemma_unicode_range_value_equal(st: ps::TokenStream, a: nat, b: nat)
    requires
        shaped(st),
        b <= n_of(st),
    ensures
        cvs_of(ps::consume_the_value_of_a_unicode_range_descriptor(ps::segment(st, a as int, b as int)->Some_0))
            == i_consume_unicode_range_value(i_text_of(lex_of(st), src_of(st), a, b)),
{
    lemma_segment_equal(st, a, b);
    let text = ps::segment(st, a as int, b as int)->Some_0;
    assert(valid(text)) by {
        if a < b {
            lemma_spans_monotone(st, a as int, b as int - 1);
            lemma_valid_subrange(
                st.source->Some_0.text,
                st.source->Some_0.spans[a as int].start,
                st.source->Some_0.spans[b as int - 1].end,
            );
        } else {
            assert(text =~= Seq::<u32>::empty());
        }
    }
    let st2 = ps::token_stream(text, true);
    lemma_token_stream_shaped(text, true);
    lemma_list_loop_equal(st2, 0, None, false, Seq::empty());
    assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
}

/// Steps 5 to 7 of §5.4.7 and where the value ends, as both transcriptions have them.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_declaration_value_equal(st: ps::TokenStream, vs: nat, nested: bool)
    requires
        shaped(st),
        vs <= n_of(st),
    ensures
        ({
            let (list, end) = ps::consume_a_list_of_component_values(st, vs as int, Some(t::Token::Semicolon), nested);
            let (listed, mend) = i_consume_list_of_component_values(
                lex_of(st),
                vs,
                Some(ITok::Semicolon),
                nested,
                seq![],
            );
            let (value0, important) = match ps::important_at(list) {
                Some((first, second)) => (list.remove(second).remove(first), true),
                None => (list, false),
            };
            let (taken, mimportant) = i_take_important(listed);
            let value = ps::without_trailing_whitespace(value0);
            let mvalue = i_strip_trailing_ws(taken);
            let value_end = end - (list.len() - value.len());
            &&& cvs_of(list) == listed
            &&& end == mend as int
            &&& vs <= end <= n_of(st)
            &&& important == mimportant
            &&& cvs_of(value) == mvalue
            &&& 0 <= value_end <= end
            &&& i_skip_component_values(lex_of(st), vs, mvalue.len()) == value_end as nat
        }),
{
    lemma_list_loop_equal(st, vs, Some(t::Token::Semicolon), nested, Seq::empty());
    assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
    let (list, end) = ps::consume_a_list_of_component_values(st, vs as int, Some(t::Token::Semicolon), nested);
    assert(ps::list_of_component_values_loop(st, vs as int, Some(t::Token::Semicolon), nested, Seq::empty())
        == (list, end));
    let (listed, mend) = i_consume_list_of_component_values(
        lex_of(st),
        vs,
        Some(ITok::Semicolon),
        nested,
        seq![],
    );
    lemma_important_equal(list);
    let (value0, important) = match ps::important_at(list) {
        Some((first, second)) => (list.remove(second).remove(first), true),
        None => (list, false),
    };
    let (taken, mimportant) = i_take_important(listed);
    assert(cvs_of(value0) == taken);
    lemma_strip_equal(value0);
    let value = ps::without_trailing_whitespace(value0);
    let mvalue = i_strip_trailing_ws(taken);
    assert(cvs_of(value) == mvalue);
    lemma_strip_len(value0);
    lemma_remove_len(list);
    lemma_declaration_tail(list);
    lemma_list_skip(st, vs, Some(t::Token::Semicolon), nested, Seq::empty(), value.len());
    lemma_list_loop_extends(st, vs, Some(t::Token::Semicolon), nested, Seq::empty());
    assert(value.len() == mvalue.len());
}

/// Taking "!important" out of a list does not make it longer.
pub proof fn lemma_remove_len(list: Seq<ps::ComponentValue>)
    ensures
        ({
            let value0 = match ps::important_at(list) {
                Some((first, second)) => list.remove(second).remove(first),
                None => list,
            };
            value0.len() <= list.len()
        }),
{
    if let Some((first, second)) = ps::important_at(list) {
        lemma_last_non_whitespace_len(list);
        assert(0 <= first);
        assert(first < second);
        assert(second < list.len());
        assert(list.remove(second).len() == list.len() - 1);
    }
}

/// The last two non-whitespace items are items of the list.
pub proof fn lemma_last_non_whitespace_len(list: Seq<ps::ComponentValue>)
    ensures
        ({
            let second = ps::last_non_whitespace(list, list.len() as int);
            let first = ps::last_non_whitespace(list, second);
            &&& second < list.len()
            &&& first >= 0 ==> (0 <= first < second)
        }),
{
    lemma_last_non_whitespace(list, list.len() as int);
    let second = ps::last_non_whitespace(list, list.len() as int);
    if second >= 0 {
        lemma_last_non_whitespace(list, second);
    } else {
        assert(ps::last_non_whitespace(list, second) == -1);
    }
}

/// §5.4.7 "consume a declaration".
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_declaration_equal(st: ps::TokenStream, p: nat, nested: bool)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        ({
            let (d, q) = ps::consume_a_declaration(st, p as int, nested);
            let (md, mq) = i_consume_declaration(lex_of(st), src_of(st), p, nested);
            &&& opt_decl_of(d) == md
            &&& q == mq as int
            &&& q >= p
            &&& q <= n_of(st)
            &&& (!ps::is_empty(st, p as int) && !(nested && ps::is(ps::next_token(st, p as int), t::Token::CloseCurly))
                ==> q > p)
        }),
{
    assert(lex_of(st).len() == n_of(st));
    let item = ps::next_token(st, p as int);
    lemma_is(st, p, t::Token::CloseCurly);
    crate::parser::termination::lemma_remnants_forward(st, p as int, nested);
    lemma_remnants_equal(st, p, nested);
    if ps::is_ident(item) {
        let (token, after_name) = ps::consume_a_token(st, p as int);
        assert(!ps::is_empty(st, p as int));
        assert(after_name == p + 1);
        lemma_discard_whitespace(st, p + 1);
        lemma_discard_whitespace_bound(st, p + 1);
        let after_whitespace = ps::discard_whitespace(st, after_name);
        let aw = after_whitespace as nat;
        lemma_is(st, aw, t::Token::Colon);
        lemma_remnants_equal(st, aw, nested);
        crate::parser::termination::lemma_remnants_forward(st, aw as int, nested);
        if ps::is(ps::next_token(st, after_whitespace), t::Token::Colon) {
            lemma_is_empty(st, aw);
            let after_colon = ps::discard_a_token(st, after_whitespace);
            assert(after_colon == aw + 1);
            lemma_discard_whitespace(st, aw + 1);
            lemma_discard_whitespace_bound(st, aw + 1);
            let start = ps::discard_whitespace(st, after_colon);
            let vs = start as nat;
            lemma_declaration_value_equal(st, vs, nested);
            lemma_declaration_value_finish(st, vs, nested, ps::token_value(token));
        }
    }
}

/// Steps 8 and 9 of §5.4.7, given the value of the earlier steps.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_declaration_value_finish(st: ps::TokenStream, vs: nat, nested: bool, name: Seq<u32>)
    requires
        shaped(st),
        vs <= n_of(st),
    ensures
        ({
            let (d, q) = ps::declaration_value(st, vs as int, nested, name);
            let (list, end) = ps::consume_a_list_of_component_values(st, vs as int, Some(t::Token::Semicolon), nested);
            let (listed, mend) = i_consume_list_of_component_values(
                lex_of(st),
                vs,
                Some(ITok::Semicolon),
                nested,
                seq![],
            );
            let (taken, mimportant) = i_take_important(listed);
            let mvalue = i_strip_trailing_ws(taken);
            let mend2 = i_skip_component_values(lex_of(st), vs, mvalue.len());
            let md: Option<IDecl> = if i_custom_property_name(ints(name)) {
                Some(IDecl {
                    name: ints(name),
                    value: mvalue,
                    important: mimportant,
                    original_text: Some(i_text_of(lex_of(st), src_of(st), vs, mend2)),
                })
            } else if i_curly_block_with_others(mvalue) {
                None
            } else {
                Some(IDecl {
                    name: ints(name),
                    value: if i_ci_match(ints(name), seq![
                        0x75 as int, 0x6E, 0x69, 0x63, 0x6F, 0x64, 0x65, 0x2D, 0x72, 0x61, 0x6E, 0x67, 0x65,
                    ]) {
                        i_consume_unicode_range_value(i_text_of(lex_of(st), src_of(st), vs, mend))
                    } else {
                        mvalue
                    },
                    important: mimportant,
                    original_text: None,
                })
            };
            &&& opt_decl_of(d) == md
            &&& q == end
        }),
{
    lemma_declaration_value_equal(st, vs, nested);
    let (list, end) = ps::consume_a_list_of_component_values(st, vs as int, Some(t::Token::Semicolon), nested);
    let (value0, important) = match ps::important_at(list) {
        Some((first, second)) => (list.remove(second).remove(first), true),
        None => (list, false),
    };
    let value = ps::without_trailing_whitespace(value0);
    let value_end = end - (list.len() - value.len());
    lemma_custom_name(name);
    lemma_curly_equal(value);
    lemma_important_string();
    lemma_ci_match(name, ps::unicode_range_string());
    if ps::is_custom_property_name_string(name) {
        lemma_segment_equal(st, vs, value_end as nat);
    } else if ps::has_curly_block_and_another(value) {
    } else if ps::ascii_case_insensitive_match(name, ps::unicode_range_string()) {
        lemma_unicode_range_value_equal(st, vs, end as nat);
    }
}

/// Stripping does not make a list longer.
pub proof fn lemma_strip_len(v: Seq<ps::ComponentValue>)
    ensures
        ps::without_trailing_whitespace(v).len() <= v.len(),
    decreases v.len(),
{
    if v.len() > 0 && ps::is_whitespace_token(v.last()) {
        lemma_strip_len(v.drop_last());
    }
}


// ---------------------------------------------------------------------
// Helpers of §5.4.2 to §5.4.6

/// The index of the first value that is not whitespace.
pub proof fn lemma_first_non_ws(v: Seq<ps::ComponentValue>, k: int)
    requires
        0 <= k,
    ensures
        match i_first_non_ws(cvs_of(v), k as nat) {
            Some(i) => ps::first_non_whitespace(v, k) == i as int && i < v.len() && !ps::is_whitespace_token(v[i as int]),
            None => ps::first_non_whitespace(v, k) == v.len(),
        },
    decreases v.len() - k,
{
    if k < v.len() {
        lemma_cv_of_ws(v[k]);
        if ps::is_whitespace_token(v[k]) {
            lemma_first_non_ws(v, k + 1);
        }
    }
}

/// An `<ident-token>` among the values.
pub proof fn lemma_cv_of_ident(x: ps::ComponentValue)
    ensures
        ps::is_ident(x) == (cv_of(x) is Token && cv_of(x)->Token_0 is Ident),
        ps::is_ident(x) ==> ints(ps::token_value(x)) == cv_of(x)->Token_0->Ident_0,
{
}

/// A `<colon-token>` among the values.
pub proof fn lemma_cv_of_colon(x: ps::ComponentValue)
    ensures
        ps::is(x, t::Token::Colon) == (cv_of(x) == ICv::Token(ITok::Colon)),
{
    if let ps::ComponentValue::Token { token } = x {
        lemma_tok_of_plain(token, t::Token::Colon);
    }
}

/// "the first two non-whitespace values of the prelude are an ident that starts with "--"
/// and a colon".
pub proof fn lemma_prelude_custom(prelude: Seq<ps::ComponentValue>)
    ensures
        ps::prelude_looks_like_a_custom_property(prelude) == i_prelude_is_custom_property(cvs_of(prelude)),
{
    lemma_first_non_ws(prelude, 0);
    let first = ps::first_non_whitespace(prelude, 0);
    if first < prelude.len() {
        lemma_cv_of_ident(prelude[first]);
        lemma_first_non_ws(prelude, first + 1);
        let second = ps::first_non_whitespace(prelude, first + 1);
        if second < prelude.len() {
            lemma_cv_of_colon(prelude[second]);
        }
        if ps::is_ident(prelude[first]) {
            lemma_custom_name(ps::token_value(prelude[first]));
        }
    }
}

/// The child rules of a rule, as the independent transcription lists them.
pub proof fn lemma_child_rules(items: Seq<ps::BlockItem>)
    ensures
        rules_of(ps::child_rules_of(items)) =~= i_child_rules(items_of(items)),
    decreases items.len(),
{
    if items.len() > 0 {
        let rest = items.subrange(1, items.len() as int);
        lemma_child_rules(rest);
        assert(items_of(items).subrange(1, items.len() as int) =~= items_of(rest));
        let cr = ps::child_rules_of(items);
        assert(ps::child_rules_of(rest) =~= cr.subrange(1, cr.len() as int));
        assert(rules_of(cr) =~= seq![rule_of(cr[0])] + rules_of(cr.subrange(1, cr.len() as int)));
        assert(rest =~= items.drop_first());
    }
}

/// The rule of §5.4.3 once "consume a block" gave `items`.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_qualified_rule_from(prelude: Seq<ps::ComponentValue>, items: Seq<ps::BlockItem>)
    ensures
        ({
            let mi = items_of(items);
            let first_is_decls = mi.len() > 0 && mi[0] is Decls;
            let decls = if first_is_decls { mi[0]->Decls_0 } else { seq![] };
            let rest = if first_is_decls { mi.subrange(1, mi.len() as int) } else { mi };
            rule_of(ps::qualified_rule_from(prelude, items)) == (IRule::QualifiedRule {
                prelude: cvs_of(prelude),
                decls,
                children: i_child_rules(rest),
            })
        }),
{
    let mi = items_of(items);
    assert(mi.len() == items.len());
    if items.len() > 0 {
        assert(mi[0] == item_of(items[0]));
    }
    if items.len() > 0 && items[0] is Declarations {
        let rest = items.drop_first();
        lemma_child_rules(rest);
        assert(rules_of(ps::child_rules_of(rest)) == i_child_rules(items_of(rest)));
        assert(items_of(rest) =~= mi.subrange(1, mi.len() as int));
        assert(items_of(rest) == mi.subrange(1, mi.len() as int));
        assert(mi[0] is Decls);
        assert(mi[0]->Decls_0 == decls_of(items[0]->declarations));
        let q = ps::qualified_rule_from(prelude, items);
        assert(q == (ps::Rule::QualifiedRule {
            prelude,
            declarations: items[0]->declarations,
            child_rules: ps::child_rules_of(rest),
        }));
        assert(rule_of(q) == (IRule::QualifiedRule {
            prelude: cvs_of(prelude),
            decls: decls_of(items[0]->declarations),
            children: rules_of(ps::child_rules_of(rest)),
        }));
        assert(mi.subrange(1, mi.len() as int) == items_of(rest));
    } else {
        lemma_child_rules(items);
        assert(rules_of(ps::child_rules_of(items)) == i_child_rules(items_of(items)));
        assert(!(mi.len() > 0 && mi[0] is Decls));
        let q = ps::qualified_rule_from(prelude, items);
        assert(q == (ps::Rule::QualifiedRule {
            prelude,
            declarations: Seq::empty(),
            child_rules: ps::child_rules_of(items),
        }));
        assert(rule_of(q) == (IRule::QualifiedRule {
            prelude: cvs_of(prelude),
            decls: decls_of(Seq::<ps::Declaration>::empty()),
            children: rules_of(ps::child_rules_of(items)),
        }));
        assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
    }
}

/// `push` is `+` of a one-item list.
pub proof fn lemma_push_is_add<A>(s: Seq<A>, x: A)
    ensures
        s.push(x) == s + seq![x],
{
    assert(s.push(x) =~= s + seq![x]);
}

/// `items_of` and `decls_of` of a list with one more.
pub proof fn lemma_items_push(xs: Seq<ps::BlockItem>, x: ps::BlockItem)
    ensures
        items_of(xs.push(x)) =~= items_of(xs).push(item_of(x)),
{
}

/// `decls_of` of a list with one more.
pub proof fn lemma_decls_push(xs: Seq<ps::Declaration>, x: ps::Declaration)
    ensures
        decls_of(xs.push(x)) =~= decls_of(xs).push(decl_of(x)),
{
}

/// "If decls is not empty, append it to rules".
pub proof fn lemma_with_declarations(rules: Seq<ps::BlockItem>, decls: Seq<ps::Declaration>)
    ensures
        items_of(ps::with_declarations(rules, decls)) =~= (if decls_of(decls).len() > 0 {
            items_of(rules) + seq![IItem::Decls(decls_of(decls))]
        } else {
            items_of(rules)
        }),
{
    if decls.len() > 0 {
        lemma_items_push(rules, ps::BlockItem::Declarations { declarations: decls });
    }
}

// ---------------------------------------------------------------------
// §5.4.2 to §5.4.6, proven together

/// §5.4.5 "consume a block", from its `<{-token>`.
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub proof fn lemma_block_equal(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
        p <= n_of(st),
        ps::is(ps::next_token(st, p as int), t::Token::OpenCurly),
    ensures
        ({
            let (items, next) = ps::consume_a_block(st, p as int);
            let (mitems, mnext) = i_consume_block_rest(lex_of(st), src_of(st), p + 1);
            &&& items_of(items) == mitems
            &&& next == mnext as int
            &&& p + 1 <= next <= n_of(st)
        }),
    decreases ps::items_left(st, p as int), 0nat,
{
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::OpenCurly);
    assert(!ps::is_empty(st, p as int)) by {
        lemma_is_empty(st, p);
    }
    assert(ps::discard_a_token(st, p as int) == p + 1);
    lemma_contents_loop_equal(st, p + 1, Seq::empty(), Seq::empty());
    let (rules, next) = ps::consume_a_blocks_contents(st, p as int + 1);
    assert(ps::blocks_contents_loop(st, p as int + 1, Seq::empty(), Seq::empty()) == (rules, next));
    assert(items_of(Seq::<ps::BlockItem>::empty()) =~= Seq::<IItem>::empty());
    assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
    lemma_discard(st, next as nat);
    lemma_is_empty(st, next as nat);
}

/// "Process input" of §5.4.3 "consume an at-rule", after its keyword.
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_at_rule_loop_equal(
    st: ps::TokenStream,
    p: nat,
    nested: bool,
    name: Seq<u32>,
    prelude: Seq<ps::ComponentValue>,
)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        ({
            let (r, q) = ps::at_rule_loop(st, p as int, nested, name, prelude);
            let (mr, mq) = i_at_rule_process(lex_of(st), src_of(st), p, nested, ints(name), cvs_of(prelude));
            &&& opt_rule_of(r) == mr
            &&& q == mq as int
            &&& q >= p
            &&& q <= n_of(st)
        }),
    decreases ps::items_left(st, p as int), 1nat,
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::Semicolon);
    lemma_is(st, p, t::Token::CloseCurly);
    lemma_is(st, p, t::Token::OpenCurly);
    if ps::is(item, t::Token::Semicolon) || ps::is(item, t::Token::Eof) {
    } else if ps::is(item, t::Token::CloseCurly) {
        if !nested {
            let (token, next) = ps::consume_a_token(st, p as int);
            assert(!ps::is_empty(st, p as int));
            assert(next == p + 1);
            lemma_cvs_push(prelude, token);
            assert(cvs_of(prelude.push(token)) == cvs_of(prelude) + seq![ICv::Token(ITok::CloseCurly)]);
            lemma_at_rule_loop_equal(st, p + 1, nested, name, prelude.push(token));
        }
    } else if ps::is(item, t::Token::OpenCurly) {
        lemma_block_equal(st, p);
        let (items, next) = ps::consume_a_block(st, p as int);
        assert(rule_of(ps::Rule::AtRule { name, prelude, child_rules: Some(items) }) == (IRule::AtRule {
            name: ints(name),
            prelude: cvs_of(prelude),
            block: Some(items_of(items)),
        }));
    } else {
        lemma_component_value_equal(st, p);
        let (v, next) = ps::consume_a_component_value(st, p as int);
        assert(!ps::is_empty(st, p as int));
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mv, mq) = i_consume_component_value(lex_of(st), p);
        assert(fwd(p, mq) == next as nat);
        lemma_cvs_push(prelude, v);
        assert(cvs_of(prelude.push(v)) == cvs_of(prelude) + seq![mv]);
        lemma_at_rule_loop_equal(st, next as nat, nested, name, prelude.push(v));
    }
}

/// "Process input" of §5.4.4 "consume a qualified rule".
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_qualified_rule_loop_equal(
    st: ps::TokenStream,
    p: nat,
    stop: Option<t::Token>,
    nested: bool,
    prelude: Seq<ps::ComponentValue>,
)
    requires
        shaped(st),
        stop_ok(stop),
        p <= n_of(st),
    ensures
        ({
            let (r, q) = ps::qualified_rule_loop(st, p as int, stop, nested, prelude);
            let (mr, mq) = i_consume_qualified_rule(lex_of(st), src_of(st), p, stop_of(stop), nested, cvs_of(prelude));
            &&& qres_of(r) == mr
            &&& q == mq as int
            &&& q >= p
            &&& q <= n_of(st)
        }),
    decreases ps::items_left(st, p as int), 1nat,
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::CloseCurly);
    lemma_is(st, p, t::Token::OpenCurly);
    if stop is Some {
        lemma_is(st, p, stop->Some_0);
    }
    if ps::is(item, t::Token::Eof) || ps::is_stop(item, stop) {
    } else if ps::is(item, t::Token::CloseCurly) {
        if !nested {
            let (token, next) = ps::consume_a_token(st, p as int);
            assert(!ps::is_empty(st, p as int));
            assert(next == p + 1);
            lemma_cvs_push(prelude, token);
            assert(cvs_of(prelude.push(token)) == cvs_of(prelude) + seq![ICv::Token(ITok::CloseCurly)]);
            lemma_qualified_rule_loop_equal(st, p + 1, stop, nested, prelude.push(token));
        }
    } else if ps::is(item, t::Token::OpenCurly) {
        lemma_prelude_custom(prelude);
        lemma_block_equal(st, p);
        lemma_remnants_equal(st, p, true);
        let (child_rules, next) = ps::consume_a_block(st, p as int);
        if !ps::prelude_looks_like_a_custom_property(prelude) {
            lemma_qualified_rule_from(prelude, child_rules);
        }
    } else {
        lemma_component_value_equal(st, p);
        let (v, next) = ps::consume_a_component_value(st, p as int);
        assert(!ps::is_empty(st, p as int));
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mv, mq) = i_consume_component_value(lex_of(st), p);
        assert(fwd(p, mq) == next as nat);
        lemma_cvs_push(prelude, v);
        assert(cvs_of(prelude.push(v)) == cvs_of(prelude) + seq![mv]);
        lemma_qualified_rule_loop_equal(st, next as nat, stop, nested, prelude.push(v));
    }
}

/// "Process input" of §5.4.6 "consume a block's contents".
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_contents_loop_equal(
    st: ps::TokenStream,
    p: nat,
    rules: Seq<ps::BlockItem>,
    decls: Seq<ps::Declaration>,
)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        ({
            let (rs, q) = ps::blocks_contents_loop(st, p as int, rules, decls);
            let (mrs, mq) = i_consume_block_contents(lex_of(st), src_of(st), p, items_of(rules), decls_of(decls));
            &&& items_of(rs) == mrs
            &&& q == mq as int
            &&& q >= p
            &&& q <= n_of(st)
        }),
    decreases ps::items_left(st, p as int), 3nat,
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Whitespace);
    lemma_is(st, p, t::Token::Semicolon);
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::CloseCurly);
    lemma_with_declarations(rules, decls);
    assert(items_of(ps::with_declarations(rules, decls)) == (if decls_of(decls).len() > 0 {
        items_of(rules) + seq![IItem::Decls(decls_of(decls))]
    } else {
        items_of(rules)
    }));
    if ps::is(item, t::Token::Whitespace) || ps::is(item, t::Token::Semicolon) {
        assert(!ps::is_empty(st, p as int));
        assert(ps::discard_a_token(st, p as int) == p + 1);
        lemma_contents_loop_equal(st, p + 1, rules, decls);
    } else if ps::is(item, t::Token::Eof) || ps::is(item, t::Token::CloseCurly) {
    } else if ps::is_at_keyword(item) {
        let flushed = ps::with_declarations(rules, decls);
        assert(!ps::is_empty(st, p as int));
        crate::parser::termination::lemma_at_rule_advances(st, p as int, true);
        assert(ps::consume_an_at_rule(st, p as int, true) == ps::at_rule_loop(
            st,
            p as int + 1,
            true,
            ps::token_value(item),
            Seq::empty(),
        ));
        lemma_at_rule_loop_equal(st, p + 1, true, ps::token_value(item), Seq::empty());
        assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
        let (rule, next) = ps::consume_an_at_rule(st, p as int, true);
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mrule, mnext) = i_at_rule_process(lex_of(st), src_of(st), p + 1, true, ints(ps::token_value(item)), seq![]);
        assert(fwd(p, mnext) == next as nat);
        match rule {
            Some(r) => {
                lemma_items_push(flushed, ps::BlockItem::Rule { rule: r });
                lemma_push_is_add(items_of(flushed), item_of(ps::BlockItem::Rule { rule: r }));
                assert(items_of(flushed.push(ps::BlockItem::Rule { rule: r })) == items_of(flushed).push(
                    item_of(ps::BlockItem::Rule { rule: r }),
                ));
                lemma_contents_loop_equal(st, next as nat, flushed.push(ps::BlockItem::Rule { rule: r }), Seq::empty());
                assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
            },
            None => {
                lemma_contents_loop_equal(st, next as nat, flushed, Seq::empty());
                assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
            },
        }
    } else {
        lemma_declaration_equal(st, p, true);
        let (decl, next) = ps::consume_a_declaration(st, p as int, true);
        match decl {
            Some(d) => {
                assert(next > p);
                assert(ps::moved(p as int, next) == next);
                let (md, mnext) = i_consume_declaration(lex_of(st), src_of(st), p, true);
                assert(fwd(p, mnext) == next as nat);
                lemma_decls_push(decls, d);
                lemma_push_is_add(decls_of(decls), decl_of(d));
                assert(decls_of(decls.push(d)) == decls_of(decls).push(decl_of(d)));
                lemma_contents_loop_equal(st, next as nat, rules, decls.push(d));
            },
            None => {
                assert(!ps::is_empty(st, p as int));
                crate::parser::termination::lemma_qualified_rule_forward(st, p as int, Some(t::Token::Semicolon), true, Seq::empty());
                lemma_is(st, p, t::Token::Semicolon);
                lemma_qualified_rule_loop_equal(st, p, Some(t::Token::Semicolon), true, Seq::empty());
                assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
                let (result, after_rule) = ps::consume_a_qualified_rule(st, p as int, Some(t::Token::Semicolon), true);
                assert(ps::qualified_rule_loop(st, p as int, Some(t::Token::Semicolon), true, Seq::empty())
                    == (result, after_rule));
                assert(after_rule > p);
                assert(ps::moved(p as int, after_rule) == after_rule);
                let (mres, mq2) = i_consume_qualified_rule(
                    lex_of(st),
                    src_of(st),
                    p,
                    Some(ITok::Semicolon),
                    true,
                    seq![],
                );
                assert(fwd(p, mq2) == after_rule as nat);
                match result {
                    ps::QualifiedRuleResult::Nothing => {
                        lemma_contents_loop_equal(st, after_rule as nat, rules, decls);
                    },
                    ps::QualifiedRuleResult::InvalidRuleError => {
                        lemma_contents_loop_equal(st, after_rule as nat, ps::with_declarations(rules, decls), Seq::empty());
                        assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
                    },
                    ps::QualifiedRuleResult::Rule { rule } => {
                        lemma_items_push(ps::with_declarations(rules, decls), ps::BlockItem::Rule { rule });
                        lemma_push_is_add(
                            items_of(ps::with_declarations(rules, decls)),
                            item_of(ps::BlockItem::Rule { rule }),
                        );
                        assert(items_of(ps::with_declarations(rules, decls).push(ps::BlockItem::Rule { rule }))
                            == items_of(ps::with_declarations(rules, decls)).push(item_of(ps::BlockItem::Rule { rule })));
                        lemma_contents_loop_equal(
                            st,
                            after_rule as nat,
                            ps::with_declarations(rules, decls).push(ps::BlockItem::Rule { rule }),
                            Seq::empty(),
                        );
                        assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
                    },
                }
            },
        }
    }
}


// ---------------------------------------------------------------------
// §5.4.1, §5.4.5: stylesheets and lists of declarations

/// `rules_of` of a list with one more.
pub proof fn lemma_rules_push(xs: Seq<ps::Rule>, x: ps::Rule)
    ensures
        rules_of(xs.push(x)) =~= rules_of(xs).push(rule_of(x)),
{
}

/// The loop of §5.4.1 "consume a stylesheet's contents".
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_stylesheet_loop_equal(st: ps::TokenStream, p: nat, rules: Seq<ps::Rule>)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        rules_of(ps::stylesheets_contents_loop(st, p as int, rules).0) == i_consume_stylesheet_contents(
            lex_of(st),
            src_of(st),
            p,
            rules_of(rules),
        ),
    decreases ps::items_left(st, p as int),
{
    let item = ps::next_token(st, p as int);
    assert(lex_of(st).len() == n_of(st));
    lemma_is(st, p, t::Token::Whitespace);
    lemma_is(st, p, t::Token::Eof);
    lemma_is(st, p, t::Token::Cdo);
    lemma_is(st, p, t::Token::Cdc);
    if ps::is(item, t::Token::Whitespace) {
        assert(!ps::is_empty(st, p as int));
        assert(ps::discard_a_token(st, p as int) == p + 1);
        lemma_stylesheet_loop_equal(st, p + 1, rules);
    } else if ps::is(item, t::Token::Eof) {
    } else if ps::is(item, t::Token::Cdo) || ps::is(item, t::Token::Cdc) {
        assert(!ps::is_empty(st, p as int));
        assert(ps::discard_a_token(st, p as int) == p + 1);
        lemma_stylesheet_loop_equal(st, p + 1, rules);
    } else if ps::is_at_keyword(item) {
        assert(!ps::is_empty(st, p as int));
        crate::parser::termination::lemma_at_rule_advances(st, p as int, false);
        assert(ps::consume_an_at_rule(st, p as int, false) == ps::at_rule_loop(
            st,
            p as int + 1,
            false,
            ps::token_value(item),
            Seq::empty(),
        ));
        lemma_at_rule_loop_equal(st, p + 1, false, ps::token_value(item), Seq::empty());
        assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
        let (rule, next) = ps::consume_an_at_rule(st, p as int, false);
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mrule, mnext) = i_at_rule_process(lex_of(st), src_of(st), p + 1, false, ints(ps::token_value(item)), seq![]);
        assert(fwd(p, mnext) == next as nat);
        match rule {
            Some(r) => {
                lemma_rules_push(rules, r);
                lemma_push_is_add(rules_of(rules), rule_of(r));
                assert(rules_of(rules.push(r)) == rules_of(rules).push(rule_of(r)));
                lemma_stylesheet_loop_equal(st, next as nat, rules.push(r));
            },
            None => {
                lemma_stylesheet_loop_equal(st, next as nat, rules);
            },
        }
    } else {
        assert(!ps::is_empty(st, p as int));
        crate::parser::termination::theorem_stylesheet_moves(st, p as int);
        lemma_qualified_rule_loop_equal(st, p, None, false, Seq::empty());
        assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
        let (result, next) = ps::consume_a_qualified_rule(st, p as int, None, false);
        assert(ps::qualified_rule_loop(st, p as int, None, false, Seq::empty()) == (result, next));
        assert(next > p);
        assert(ps::moved(p as int, next) == next);
        let (mres, mnext) = i_consume_qualified_rule(lex_of(st), src_of(st), p, None, false, seq![]);
        assert(fwd(p, mnext) == next as nat);
        match result {
            ps::QualifiedRuleResult::Rule { rule } => {
                lemma_rules_push(rules, rule);
                lemma_push_is_add(rules_of(rules), rule_of(rule));
                assert(rules_of(rules.push(rule)) == rules_of(rules).push(rule_of(rule)));
                lemma_stylesheet_loop_equal(st, next as nat, rules.push(rule));
            },
            _ => {
                lemma_stylesheet_loop_equal(st, next as nat, rules);
            },
        }
    }
}

/// The loop of §5.4.5 "parse a list of declarations".
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_declarations_loop_equal(st: ps::TokenStream, p: nat, decls: Seq<ps::Declaration>)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        decls_of(ps::list_of_declarations_loop(st, p as int, decls)) == i_declarations_loop(
            lex_of(st),
            src_of(st),
            p,
            decls_of(decls),
        ),
    decreases ps::items_left(st, p as int),
{
    assert(lex_of(st).len() == n_of(st));
    lemma_is_empty(st, p);
    if !ps::is_empty(st, p as int) {
        lemma_discard_whitespace(st, p);
        lemma_discard_whitespace_bound(st, p);
        crate::parser::termination::theorem_declarations_move(st, p as int);
        let start = ps::discard_whitespace(st, p as int);
        let q = start as nat;
        let item = ps::next_token(st, start);
        lemma_is(st, q, t::Token::Semicolon);
        if ps::is(item, t::Token::Semicolon) {
            lemma_is_empty(st, q);
            assert(ps::discard_a_token(st, start) == q + 1);
            assert(ps::moved(p as int, q as int + 1) == q as int + 1);
            lemma_declarations_loop_equal(st, q + 1, decls);
        } else if ps::is_at_keyword(item) {
            assert(!ps::is_empty(st, start));
            assert(ps::consume_an_at_rule(st, start, false) == ps::at_rule_loop(
                st,
                start + 1,
                false,
                ps::token_value(item),
                Seq::empty(),
            ));
            lemma_at_rule_loop_equal(st, q + 1, false, ps::token_value(item), Seq::empty());
            assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
            let (_rule, next) = ps::consume_an_at_rule(st, start, false);
            assert(next > p);
            assert(ps::moved(p as int, next) == next);
            let (_mrule, mnext) = i_at_rule_process(lex_of(st), src_of(st), q + 1, false, ints(ps::token_value(item)), seq![]);
            assert(fwd(p, mnext) == next as nat);
            lemma_declarations_loop_equal(st, next as nat, decls);
        } else {
            lemma_declaration_equal(st, q, false);
            let (decl, next) = ps::consume_a_declaration(st, start, false);
            assert(next > p);
            assert(ps::moved(p as int, next) == next);
            let (_md, mnext) = i_consume_declaration(lex_of(st), src_of(st), q, false);
            assert(fwd(p, mnext) == next as nat);
            match decl {
                Some(d) => {
                    lemma_decls_push(decls, d);
                    lemma_push_is_add(decls_of(decls), decl_of(d));
                    assert(decls_of(decls.push(d)) == decls_of(decls).push(decl_of(d)));
                    lemma_declarations_loop_equal(st, next as nat, decls.push(d));
                },
                None => {
                    lemma_declarations_loop_equal(st, next as nat, decls);
                },
            }
        }
    }
}

/// The loop of §5.4.10 "parse a comma-separated list of component values".
#[verifier::spinoff_prover]
#[verifier::rlimit(300)]
pub proof fn lemma_comma_loop_equal(st: ps::TokenStream, p: nat, groups: Seq<Seq<ps::ComponentValue>>)
    requires
        shaped(st),
        p <= n_of(st),
    ensures
        groups_of(ps::comma_separated_list_loop(st, p as int, groups)) == i_comma_groups_loop(
            lex_of(st),
            p,
            groups_of(groups),
        ),
    decreases ps::items_left(st, p as int),
{
    assert(lex_of(st).len() == n_of(st));
    lemma_is_empty(st, p);
    if !ps::is_empty(st, p as int) {
        lemma_list_loop_equal(st, p, Some(t::Token::Comma), false, Seq::empty());
        assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
        crate::parser::termination::theorem_comma_list_moves(st, p as int);
        let (list, next) = ps::consume_a_list_of_component_values(st, p as int, Some(t::Token::Comma), false);
        assert(ps::list_of_component_values_loop(st, p as int, Some(t::Token::Comma), false, Seq::empty())
            == (list, next));
        lemma_discard(st, next as nat);
        assert(ps::discard_a_token(st, next) > p);
        assert(ps::moved(p as int, ps::discard_a_token(st, next)) == ps::discard_a_token(st, next));
        let (mlist, mnext) = i_consume_list_of_component_values(lex_of(st), p, Some(ITok::Comma), false, seq![]);
        assert(fwd(p, i_discard(lex_of(st), mnext)) == ps::discard_a_token(st, next) as nat);
        assert(groups_of(groups.push(list)) =~= groups_of(groups).push(cvs_of(list)));
        assert(groups_of(groups.push(list)) == groups_of(groups).push(cvs_of(list)));
        lemma_push_is_add(groups_of(groups), cvs_of(list));
        assert(next <= n_of(st));
        lemma_comma_loop_equal(st, ps::discard_a_token(st, next) as nat, groups.push(list));
    }
}

/// A list of lists of component values.
pub open spec fn groups_of(gs: Seq<Seq<ps::ComponentValue>>) -> Seq<Seq<ICv>> {
    Seq::new(gs.len(), |i: int| cvs_of(gs[i]))
}



// ---------------------------------------------------------------------
// §5.4.1 "normalize into a token stream" and the entry points

/// "The input is a stream of code points": what an entry point is given.
pub open spec fn code_points(input: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < input.len() ==> #[trigger] input[i] <= 0x10FFFF
}

/// §5.4.1 "normalize into a token stream" of a string: "filter code points from input,
/// tokenize the result".
pub proof fn lemma_normalize(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        ({
            let (st, index) = ps::normalize(ps::Input::String { string: input });
            &&& index == 0
            &&& shaped(st)
            &&& lex_of(st) == i_normalize(ints(input)).0
            &&& src_of(st) == i_normalize(ints(input)).1
        }),
{
    let fs = t::filter_code_points(input);
    lemma_filter_valid(input);
    lemma_token_stream_shaped(fs, false);
    theorem_filter_equals(input);
    assert(ints(fs) == i_filter(ints(input)));
    let st = ps::token_stream(fs, false);
    assert(lex_of(st) == i_tokenize(ints(fs), false));
    assert(src_of(st) == ints(fs));
}

/// §5.3.3 "parse a stylesheet's contents".
pub proof fn theorem_parse_stylesheet_contents_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        rules_of(ps::parse_a_stylesheets_contents(ps::Input::String { string: input })) == i_parse_stylesheet_contents(
            ints(input),
        ),
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    lemma_stylesheet_loop_equal(st, 0, Seq::empty());
    assert(rules_of(Seq::<ps::Rule>::empty()) =~= Seq::<IRule>::empty());
}

/// §5.3.2 "parse a stylesheet": its rules are those of "parse a stylesheet's contents".
pub proof fn theorem_parse_stylesheet_equals(input: Seq<u32>, location: Option<Seq<u32>>)
    requires
        code_points(input),
    ensures
        rules_of(ps::parse_a_stylesheet(ps::Input::String { string: input }, location).rules)
            == i_parse_stylesheet_contents(ints(input)),
{
    theorem_parse_stylesheet_contents_equals(input);
}

/// §5.3.4 "parse a list of declarations".
pub proof fn theorem_parse_list_of_declarations_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        decls_of(ps::parse_a_list_of_declarations(ps::Input::String { string: input })) == i_parse_list_of_declarations(
            ints(input),
        ),
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    lemma_declarations_loop_equal(st, 0, Seq::empty());
    assert(decls_of(Seq::<ps::Declaration>::empty()) =~= Seq::<IDecl>::empty());
}

/// §5.3.5 "parse a rule".
#[verifier::rlimit(400)]
pub proof fn theorem_parse_rule_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        match ps::parse_a_rule(ps::Input::String { string: input }) {
            Some(r) => i_parse_rule(ints(input)) == IParsed::Value(rule_of(r)),
            None => i_parse_rule(ints(input)) == IParsed::<IRule>::SyntaxError,
        },
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    assert(lex_of(st).len() == n_of(st));
    lemma_discard_whitespace(st, 0);
    lemma_discard_whitespace_bound(st, 0);
    let start = ps::discard_whitespace(st, 0);
    let p = start as nat;
    lemma_is_empty(st, p);
    if !ps::is_empty(st, start) {
        if ps::is_at_keyword(ps::next_token(st, start)) {
            assert(ps::consume_an_at_rule(st, start, false) == ps::at_rule_loop(
                st,
                start + 1,
                false,
                ps::token_value(ps::next_token(st, start)),
                Seq::empty(),
            ));
            lemma_at_rule_loop_equal(st, p + 1, false, ps::token_value(ps::next_token(st, start)), Seq::empty());
            assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
            let (rule, next) = ps::consume_an_at_rule(st, start, false);
            lemma_discard_whitespace(st, next as nat);
            lemma_is_empty(st, ps::discard_whitespace(st, next) as nat);
            lemma_discard_whitespace_bound(st, next as nat);
        } else {
            lemma_qualified_rule_loop_equal(st, p, None, false, Seq::empty());
            assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
            let (result, next) = ps::consume_a_qualified_rule(st, start, None, false);
            assert(ps::qualified_rule_loop(st, start, None, false, Seq::empty()) == (result, next));
            lemma_discard_whitespace(st, next as nat);
            lemma_is_empty(st, ps::discard_whitespace(st, next) as nat);
            lemma_discard_whitespace_bound(st, next as nat);
        }
    }
}

/// §5.3.6 "parse a declaration".
pub proof fn theorem_parse_declaration_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        match ps::parse_a_declaration(ps::Input::String { string: input }) {
            Some(d) => i_parse_declaration(ints(input)) == IParsed::Value(decl_of(d)),
            None => i_parse_declaration(ints(input)) == IParsed::<IDecl>::SyntaxError,
        },
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    assert(lex_of(st).len() == n_of(st));
    lemma_discard_whitespace(st, 0);
    lemma_discard_whitespace_bound(st, 0);
    let start = ps::discard_whitespace(st, 0);
    lemma_is_empty(st, start as nat);
    if !ps::is_empty(st, start) {
        lemma_declaration_equal(st, start as nat, false);
        let (decl, next) = ps::consume_a_declaration(st, start, false);
        lemma_discard_whitespace(st, next as nat);
        lemma_is_empty(st, ps::discard_whitespace(st, next) as nat);
    }
}

/// §5.3.7 "parse a component value".
pub proof fn theorem_parse_component_value_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        match ps::parse_a_component_value(ps::Input::String { string: input }) {
            Some(v) => i_parse_component_value(ints(input)) == IParsed::Value(cv_of(v)),
            None => i_parse_component_value(ints(input)) == IParsed::<ICv>::SyntaxError,
        },
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    assert(lex_of(st).len() == n_of(st));
    lemma_discard_whitespace(st, 0);
    lemma_discard_whitespace_bound(st, 0);
    let start = ps::discard_whitespace(st, 0);
    lemma_is_empty(st, start as nat);
    if !ps::is_empty(st, start) {
        lemma_component_value_equal(st, start as nat);
        let (value, next) = ps::consume_a_component_value(st, start);
        lemma_discard_whitespace(st, next as nat);
        lemma_is_empty(st, ps::discard_whitespace(st, next) as nat);
    }
}

/// §5.3.8 "parse a list of component values".
pub proof fn theorem_parse_list_of_component_values_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        cvs_of(ps::parse_a_list_of_component_values(ps::Input::String { string: input }))
            == i_parse_list_of_component_values(ints(input)),
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    lemma_list_loop_equal(st, 0, None, false, Seq::empty());
    assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
}

/// §5.3.9 "parse a comma-separated list of component values".
pub proof fn theorem_parse_comma_separated_list_equals(input: Seq<u32>)
    requires
        code_points(input),
    ensures
        groups_of(ps::parse_a_comma_separated_list_of_component_values(ps::Input::String { string: input }))
            == i_parse_comma_separated_list_of_component_values(ints(input)),
{
    lemma_normalize(input);
    let (st, index) = ps::normalize(ps::Input::String { string: input });
    lemma_comma_loop_equal(st, 0, Seq::empty());
    assert(groups_of(Seq::<Seq<ps::ComponentValue>>::empty()) =~= Seq::<Seq<ICv>>::empty());
}

} // verus!
