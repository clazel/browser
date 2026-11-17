//! The independent transcription of the entry points on a list of tokens
//! ([`super::hooks::i_tokens_parse_component_value`] and its two siblings) is the spec's
//! ([`crate::parser::spec`]) for "a list of CSS tokens and/or component values" that
//! holds tokens only and no `<EOF-token>`.
//!
//! The spec reads such a list as a stream with no `<EOF-token>` at its end (every read
//! past the end gives one). [`stream_with_eof`] is the same stream with the
//! `<EOF-token>` and a source text that has no code points, which is the shape that
//! [`super::equiv_stream::shaped`] wants, so the proofs of [`super::equiv_parser`] apply
//! to it; [`lemma_ext_cv`] and its siblings say that every algorithm of the spec
//! gives the same on both, since each reads the stream only through its next token.

#[cfg(verus_only)]
use super::equiv_base::*;
#[cfg(verus_only)]
use super::equiv_hooks::*;
#[cfg(verus_only)]
use super::equiv_map::*;
#[cfg(verus_only)]
use super::equiv_parser::*;
#[cfg(verus_only)]
use super::equiv_stream::*;
#[cfg(verus_only)]
use super::equiv_tokenizer::*;
#[cfg(verus_only)]
use super::hooks::*;
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

/// A list of tokens that has no `<EOF-token>`.
pub open spec fn no_eof(ts: Seq<t::Token>) -> bool {
    forall|i: int| 0 <= i < ts.len() ==> !((#[trigger] ts[i]) is Eof)
}

/// The independent transcription's tokens for a list of the spec's.
pub open spec fn itoks(ts: Seq<t::Token>) -> Seq<ITok> {
    Seq::new(ts.len(), |i: int| tok_of(ts[i]))
}

/// The stream that "normalize" makes of a list of tokens.
pub open spec fn tokens_stream(ts: Seq<t::Token>) -> ps::TokenStream {
    ps::TokenStream { tokens: ps::as_items(ts), source: None }
}

/// The same stream with an `<EOF-token>` at its end and a source text of no code points.
pub open spec fn stream_with_eof(ts: Seq<t::Token>) -> ps::TokenStream {
    ps::TokenStream {
        tokens: ps::as_items(ts).push(ps::ComponentValue::Token { token: t::Token::Eof }),
        source: Some(
            ps::SourceText {
                text: Seq::empty(),
                spans: Seq::new(ts.len() + 1, |i: int| ps::Span { start: 0, end: 0 }),
            },
        ),
    }
}

/// Two streams give the same next token everywhere.
pub open spec fn same_next(a: ps::TokenStream, b: ps::TokenStream) -> bool {
    forall|i: int| #[trigger] ps::next_token(a, i) == ps::next_token(b, i)
}

/// The two streams of a list of tokens without an `<EOF-token>` have the same next tokens.
pub proof fn lemma_same_next(ts: Seq<t::Token>)
    requires
        no_eof(ts),
    ensures
        same_next(tokens_stream(ts), stream_with_eof(ts)),
        shaped(stream_with_eof(ts)),
        lex_of(stream_with_eof(ts)) == i_lex_tokens(itoks(ts)),
        src_of(stream_with_eof(ts)) == Seq::<int>::empty(),
{
    let a = tokens_stream(ts);
    let b = stream_with_eof(ts);
    assert forall|i: int| #[trigger] ps::next_token(a, i) == ps::next_token(b, i) by {
        if 0 <= i < ts.len() {
            assert(ps::as_items(ts).push(ps::ComponentValue::Token { token: t::Token::Eof })[i] == ps::as_items(ts)[i]);
        } else if i == ts.len() {
            assert(b.tokens[i] == (ps::ComponentValue::Token { token: t::Token::Eof }));
        }
    }
    assert(b.tokens.len() == ts.len() + 1);
    assert forall|i: int| 0 <= i < b.tokens.len() implies #[trigger] b.tokens[i] is Token by {
        if i < ts.len() {
            assert(b.tokens[i] == ps::as_items(ts)[i]);
        }
    }
    assert(tok_at(b, b.tokens.len() - 1) is Eof);
    assert forall|i: int| 0 <= i < b.tokens.len() - 1 implies !(#[trigger] tok_at(b, i) is Eof) by {
        assert(b.tokens[i] == ps::as_items(ts)[i]);
    }
    assert(n_of(b) == ts.len());
    assert(lex_of(b) =~= i_lex_tokens(itoks(ts))) by {
        assert forall|i: int| 0 <= i < ts.len() implies lex_of(b)[i] == i_lex_tokens(itoks(ts))[i] by {
            assert(b.tokens[i] == ps::as_items(ts)[i]);
        }
    }
    assert(src_of(b) =~= Seq::<int>::empty());
}

/// "discard a token" and "empty" of two streams that give the same next tokens.
pub proof fn lemma_ext_basic(a: ps::TokenStream, b: ps::TokenStream, p: int)
    requires
        same_next(a, b),
    ensures
        ps::is_empty(a, p) == ps::is_empty(b, p),
        ps::discard_a_token(a, p) == ps::discard_a_token(b, p),
        ps::consume_a_token(a, p) == ps::consume_a_token(b, p),
{
}

/// "discard whitespace" of two streams that give the same next tokens, from `p` on.
pub proof fn lemma_ext_dw(a: ps::TokenStream, b: ps::TokenStream, p: int)
    requires
        same_next(a, b),
        no_eof_items(a),
    ensures
        ps::discard_whitespace(a, p) == ps::discard_whitespace(b, p),
    decreases ps::items_left(a, p),
{
    lemma_ext_basic(a, b, p);
    if ps::is(ps::next_token(a, p), t::Token::Whitespace) {
        assert(p < a.tokens.len());
        lemma_ext_dw(a, b, ps::discard_a_token(a, p));
    }
}

/// A stream with no `<EOF-token>` item: reading one at an index in the list is not at its end.
pub open spec fn no_eof_items(a: ps::TokenStream) -> bool {
    forall|i: int| 0 <= i < a.tokens.len() ==> !ps::is(#[trigger] a.tokens[i], t::Token::Eof)
}

/// "consume a component value" of two streams that give the same next tokens.
pub proof fn lemma_ext_cv(a: ps::TokenStream, b: ps::TokenStream, p: int)
    requires
        same_next(a, b),
        no_eof_items(a),
    ensures
        ps::consume_a_component_value(a, p) == ps::consume_a_component_value(b, p),
    decreases ps::items_left(a, p), 1nat,
{
    let item = ps::next_token(a, p);
    lemma_ext_basic(a, b, p);
    if ps::is_open_bracket(item) {
        lemma_ext_sb(a, b, p);
    } else if ps::is_function_token(item) {
        lemma_ext_fn(a, b, p);
    }
}

/// "consume a simple block" of two streams that give the same next tokens.
pub proof fn lemma_ext_sb(a: ps::TokenStream, b: ps::TokenStream, p: int)
    requires
        same_next(a, b),
        no_eof_items(a),
        ps::is_open_bracket(ps::next_token(a, p)),
    ensures
        ps::consume_a_simple_block(a, p) == ps::consume_a_simple_block(b, p),
    decreases ps::items_left(a, p), 0nat,
{
    let item = ps::next_token(a, p);
    let assoc = match item {
        ps::ComponentValue::Token { token } => token,
        _ => t::Token::Eof,
    };
    lemma_ext_basic(a, b, p);
    assert(p < a.tokens.len());
    lemma_ext_sbl(a, b, ps::discard_a_token(a, p), ps::mirror(item), assoc, Seq::empty());
}

/// The loop of "consume a simple block" of two streams that give the same next tokens.
pub proof fn lemma_ext_sbl(
    a: ps::TokenStream,
    b: ps::TokenStream,
    index: int,
    ending: t::Token,
    assoc: t::Token,
    value: Seq<ps::ComponentValue>,
)
    requires
        same_next(a, b),
        no_eof_items(a),
    ensures
        ps::simple_block_loop(a, index, ending, assoc, value) == ps::simple_block_loop(b, index, ending, assoc, value),
    decreases ps::items_left(a, index), 2nat,
{
    let item = ps::next_token(a, index);
    lemma_ext_basic(a, b, index);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, ending)) {
        assert(index < a.tokens.len());
        lemma_ext_cv(a, b, index);
        let (cv, next) = ps::consume_a_component_value(a, index);
        lemma_ext_sbl(a, b, ps::moved(index, next), ending, assoc, value.push(cv));
    }
}

/// "consume a function" of two streams that give the same next tokens.
pub proof fn lemma_ext_fn(a: ps::TokenStream, b: ps::TokenStream, p: int)
    requires
        same_next(a, b),
        no_eof_items(a),
        ps::is_function_token(ps::next_token(a, p)),
    ensures
        ps::consume_a_function(a, p) == ps::consume_a_function(b, p),
    decreases ps::items_left(a, p), 0nat,
{
    lemma_ext_basic(a, b, p);
    let (token, next) = ps::consume_a_token(a, p);
    assert(p < a.tokens.len());
    lemma_ext_fl(a, b, next, ps::token_value(token), Seq::empty());
}

/// The loop of "consume a function" of two streams that give the same next tokens.
pub proof fn lemma_ext_fl(
    a: ps::TokenStream,
    b: ps::TokenStream,
    index: int,
    name: Seq<u32>,
    value: Seq<ps::ComponentValue>,
)
    requires
        same_next(a, b),
        no_eof_items(a),
    ensures
        ps::function_loop(a, index, name, value) == ps::function_loop(b, index, name, value),
    decreases ps::items_left(a, index), 2nat,
{
    let item = ps::next_token(a, index);
    lemma_ext_basic(a, b, index);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, t::Token::CloseParen)) {
        assert(index < a.tokens.len());
        lemma_ext_cv(a, b, index);
        let (cv, next) = ps::consume_a_component_value(a, index);
        lemma_ext_fl(a, b, ps::moved(index, next), name, value.push(cv));
    }
}

/// "consume a list of component values" of two streams that give the same next tokens.
pub proof fn lemma_ext_list(
    a: ps::TokenStream,
    b: ps::TokenStream,
    index: int,
    stop: Option<t::Token>,
    nested: bool,
    values: Seq<ps::ComponentValue>,
)
    requires
        same_next(a, b),
        no_eof_items(a),
    ensures
        ps::list_of_component_values_loop(a, index, stop, nested, values) == ps::list_of_component_values_loop(
            b,
            index,
            stop,
            nested,
            values,
        ),
    decreases ps::items_left(a, index),
{
    let item = ps::next_token(a, index);
    lemma_ext_basic(a, b, index);
    if !(ps::is(item, t::Token::Eof) || ps::is_stop(item, stop)) {
        assert(index < a.tokens.len());
        if ps::is(item, t::Token::CloseCurly) {
            if !nested {
                let (token, next) = ps::consume_a_token(a, index);
                lemma_ext_list(a, b, next, stop, nested, values.push(token));
            }
        } else {
            lemma_ext_cv(a, b, index);
            let (cv, next) = ps::consume_a_component_value(a, index);
            lemma_ext_list(a, b, ps::moved(index, next), stop, nested, values.push(cv));
        }
    }
}

/// The loop of "parse a comma-separated list of component values" of two streams that
/// give the same next tokens.
pub proof fn lemma_ext_comma(
    a: ps::TokenStream,
    b: ps::TokenStream,
    index: int,
    groups: Seq<Seq<ps::ComponentValue>>,
)
    requires
        same_next(a, b),
        no_eof_items(a),
    ensures
        ps::comma_separated_list_loop(a, index, groups) == ps::comma_separated_list_loop(b, index, groups),
    decreases ps::items_left(a, index),
{
    lemma_ext_basic(a, b, index);
    if !ps::is_empty(a, index) {
        assert(index < a.tokens.len());
        lemma_ext_list(a, b, index, Some(t::Token::Comma), false, Seq::empty());
        let (list, next) = ps::consume_a_list_of_component_values(a, index, Some(t::Token::Comma), false);
        lemma_ext_basic(a, b, next);
        lemma_ext_comma(a, b, ps::moved(index, ps::discard_a_token(a, next)), groups.push(list));
    }
}

/// §5.3.7 "parse a component value" of a list of tokens.
pub proof fn theorem_tokens_parse_component_value(ts: Seq<t::Token>)
    requires
        no_eof(ts),
    ensures
        match ps::parse_a_component_value(ps::Input::List { list: ps::as_items(ts) }) {
            Some(v) => i_tokens_parse_component_value(itoks(ts)) == IParsed::Value(cv_of(v)),
            None => i_tokens_parse_component_value(itoks(ts)) == IParsed::<ICv>::SyntaxError,
        },
{
    lemma_same_next(ts);
    let a = tokens_stream(ts);
    let b = stream_with_eof(ts);
    assert(no_eof_items(a)) by {
        assert forall|i: int| 0 <= i < a.tokens.len() implies !ps::is(#[trigger] a.tokens[i], t::Token::Eof) by {
            assert(a.tokens[i] == ps::as_items(ts)[i]);
        }
    }
    lemma_ext_dw(a, b, 0);
    lemma_ext_basic(a, b, 0);
    assert(lex_of(b) == i_lex_tokens(itoks(ts)));
    lemma_discard_whitespace(b, 0);
    lemma_discard_whitespace_bound(b, 0);
    let start = ps::discard_whitespace(a, 0);
    lemma_ext_basic(a, b, start);
    lemma_is_empty(b, start as nat);
    if !ps::is_empty(a, start) {
        lemma_ext_cv(a, b, start);
        lemma_component_value_equal(b, start as nat);
        let (value, next) = ps::consume_a_component_value(a, start);
        lemma_ext_dw(a, b, next);
        lemma_ext_basic(a, b, ps::discard_whitespace(a, next));
        lemma_discard_whitespace(b, next as nat);
        lemma_is_empty(b, ps::discard_whitespace(b, next) as nat);
    }
}

/// §5.3.8 "parse a list of component values" of a list of tokens.
pub proof fn theorem_tokens_parse_list_of_component_values(ts: Seq<t::Token>)
    requires
        no_eof(ts),
    ensures
        cvs_of(ps::parse_a_list_of_component_values(ps::Input::List { list: ps::as_items(ts) }))
            == i_tokens_parse_list_of_component_values(itoks(ts)),
{
    lemma_same_next(ts);
    let a = tokens_stream(ts);
    let b = stream_with_eof(ts);
    assert(no_eof_items(a)) by {
        assert forall|i: int| 0 <= i < a.tokens.len() implies !ps::is(#[trigger] a.tokens[i], t::Token::Eof) by {
            assert(a.tokens[i] == ps::as_items(ts)[i]);
        }
    }
    lemma_ext_list(a, b, 0, None, false, Seq::empty());
    lemma_list_loop_equal(b, 0, None, false, Seq::empty());
    assert(cvs_of(Seq::<ps::ComponentValue>::empty()) =~= Seq::<ICv>::empty());
}

/// §5.3.9 "parse a comma-separated list of component values" of a list of tokens.
pub proof fn theorem_tokens_parse_comma_separated_list(ts: Seq<t::Token>)
    requires
        no_eof(ts),
    ensures
        groups_of(ps::parse_a_comma_separated_list_of_component_values(ps::Input::List { list: ps::as_items(ts) }))
            == i_tokens_parse_comma_separated_list_of_component_values(itoks(ts)),
{
    lemma_same_next(ts);
    let a = tokens_stream(ts);
    let b = stream_with_eof(ts);
    assert(no_eof_items(a)) by {
        assert forall|i: int| 0 <= i < a.tokens.len() implies !ps::is(#[trigger] a.tokens[i], t::Token::Eof) by {
            assert(a.tokens[i] == ps::as_items(ts)[i]);
        }
    }
    lemma_ext_comma(a, b, 0, Seq::empty());
    lemma_comma_loop_equal(b, 0, Seq::empty());
    assert(groups_of(Seq::<Seq<ps::ComponentValue>>::empty()) =~= Seq::<Seq<ICv>>::empty());
}

} // verus!
