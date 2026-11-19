//! The stream the independent parser reads, and the base facts the equivalence of the independent parser ([`super::parse`]) with the spec
//! ([`crate::parser::spec`]), over the token streams the tokenizer makes.
//!
//! A spec stream that [`shaped`] says came from a tokenizer (all items tokens,
//! the `<EOF-token>` last, a source text with a span for each) is read as the
//! independent transcription's stream by [`lex_of`] and [`src_of`]. Every theorem
//! says that what the spec's algorithm returns, mapped by [`super::equiv_map`], is
//! what the independent one returns, and that both are at the same index.

#[cfg(verus_only)]
use super::equiv_base::*;
#[cfg(verus_only)]
use super::equiv_bounds::*;
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
// The stream

/// The token of an item of a stream (the `<EOF-token>` for anything else).
pub open spec fn tok_at(st: ps::TokenStream, i: int) -> t::Token {
    match st.tokens[i] {
        ps::ComponentValue::Token { token } => token,
        _ => t::Token::Eof,
    }
}

/// How many tokens the stream has before its `<EOF-token>`.
pub open spec fn n_of(st: ps::TokenStream) -> nat {
    if st.tokens.len() > 0 { (st.tokens.len() - 1) as nat } else { 0 }
}

/// A stream the tokenizer made: tokens and then an `<EOF-token>`, with a source text
/// and the positions of each.
pub open spec fn shaped(st: ps::TokenStream) -> bool {
    &&& st.tokens.len() >= 1
    &&& forall|i: int| 0 <= i < st.tokens.len() ==> #[trigger] st.tokens[i] is Token
    &&& tok_at(st, st.tokens.len() - 1) is Eof
    &&& forall|i: int| 0 <= i < st.tokens.len() - 1 ==> !(#[trigger] tok_at(st, i) is Eof)
    &&& st.source is Some
    &&& st.source->Some_0.spans.len() == st.tokens.len()
    &&& valid(st.source->Some_0.text)
    &&& forall|i: int|
        0 <= i < st.tokens.len() - 1 ==> 0 <= #[trigger] st.source->Some_0.spans[i].start
            <= st.source->Some_0.spans[i].end <= st.source->Some_0.text.len()
    &&& forall|i: int|
        0 <= i && i + 1 < st.tokens.len() - 1 ==> #[trigger] st.source->Some_0.spans[i].end
            <= st.source->Some_0.spans[i + 1].start
}

/// The stream as the independent transcription's tokens.
pub open spec fn lex_of(st: ps::TokenStream) -> Seq<Lex> {
    Seq::new(
        n_of(st),
        |i: int|
            Lex {
                tok: tok_of(tok_at(st, i)),
                start: st.source->Some_0.spans[i].start as nat,
                end: st.source->Some_0.spans[i].end as nat,
            },
    )
}

/// The stream's source text as the independent transcription's.
pub open spec fn src_of(st: ps::TokenStream) -> Seq<int> {
    match st.source {
        Some(source) => ints(source.text),
        None => seq![],
    }
}

/// The token a stream has at an index.
pub open spec fn tk(st: ps::TokenStream, p: int) -> t::Token {
    if 0 <= p < st.tokens.len() { tok_at(st, p) } else { t::Token::Eof }
}

/// The tokens that are the same in both transcriptions: no value but a code point.
pub open spec fn plain(k: t::Token) -> bool {
    match k {
        t::Token::Delim { .. } => true,
        t::Token::Whitespace => true,
        t::Token::Cdo => true,
        t::Token::Cdc => true,
        t::Token::Colon => true,
        t::Token::Semicolon => true,
        t::Token::Comma => true,
        t::Token::OpenSquare => true,
        t::Token::CloseSquare => true,
        t::Token::OpenParen => true,
        t::Token::CloseParen => true,
        t::Token::OpenCurly => true,
        t::Token::CloseCurly => true,
        t::Token::Eof => true,
        _ => false,
    }
}

/// A plain token is the only one of its image.
pub proof fn lemma_tok_of_plain(a: t::Token, b: t::Token)
    requires
        plain(b),
    ensures
        (tok_of(a) == tok_of(b)) == (a == b),
{
}

/// The independent transcription's next token is the image of the spec's.
pub broadcast proof fn lemma_next(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::next_token(st, p as int) == (ps::ComponentValue::Token { token: tk(st, p as int) }),
        tok_of(tk(st, p as int)) == i_next(lex_of(st), p),
{
    assert(lex_of(st).len() == n_of(st));
}

/// "is" a plain token.
pub broadcast proof fn lemma_is(st: ps::TokenStream, p: nat, k: t::Token)
    requires
        shaped(st),
        plain(k),
    ensures
        #[trigger] ps::is(ps::next_token(st, p as int), k) == (i_next(lex_of(st), p) == tok_of(k)),
{
    lemma_next(st, p);
    lemma_tok_of_plain(tk(st, p as int), k);
}

/// "empty".
pub broadcast proof fn lemma_is_empty(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::is_empty(st, p as int) == i_empty(lex_of(st), p),
{
    lemma_next(st, p);
    lemma_is(st, p, t::Token::Eof);
    assert(lex_of(st).len() == n_of(st));
    if p < n_of(st) {
        assert(!(tok_at(st, p as int) is Eof));
        assert(tok_of(tok_at(st, p as int)) != ITok::Eof);
    }
}

/// The classes of the next token.
pub broadcast proof fn lemma_class_function(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::is_function_token(ps::next_token(st, p as int)) == (i_next(lex_of(st), p) is Function),
        ps::is_function_token(ps::next_token(st, p as int)) ==> ints(ps::token_value(ps::next_token(st, p as int)))
            == i_next(lex_of(st), p)->Function_0,
{
    lemma_next(st, p);
}

/// The classes of the next token.
pub broadcast proof fn lemma_class_at_keyword(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::is_at_keyword(ps::next_token(st, p as int)) == (i_next(lex_of(st), p) is AtKeyword),
        ps::is_at_keyword(ps::next_token(st, p as int)) ==> ints(ps::token_value(ps::next_token(st, p as int)))
            == i_next(lex_of(st), p)->AtKeyword_0,
{
    lemma_next(st, p);
}

/// The classes of the next token.
pub broadcast proof fn lemma_class_ident(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::is_ident(ps::next_token(st, p as int)) == (i_next(lex_of(st), p) is Ident),
        ps::is_ident(ps::next_token(st, p as int)) ==> ints(ps::token_value(ps::next_token(st, p as int)))
            == i_next(lex_of(st), p)->Ident_0,
{
    lemma_next(st, p);
}

/// "open bracket".
pub broadcast proof fn lemma_class_open_bracket(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::is_open_bracket(ps::next_token(st, p as int)) == (i_next(lex_of(st), p) == ITok::OpenCurly
            || i_next(lex_of(st), p) == ITok::OpenSquare || i_next(lex_of(st), p) == ITok::OpenParen),
{
    lemma_is(st, p, t::Token::OpenCurly);
    lemma_is(st, p, t::Token::OpenSquare);
    lemma_is(st, p, t::Token::OpenParen);
}

/// "consume a token" and "discard a token".
pub broadcast proof fn lemma_discard(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        #[trigger] ps::discard_a_token(st, p as int) == i_discard(lex_of(st), p) as int,
{
    lemma_is_empty(st, p);
}

/// "discard whitespace".
pub proof fn lemma_discard_whitespace(st: ps::TokenStream, p: nat)
    requires
        shaped(st),
    ensures
        ps::discard_whitespace(st, p as int) == i_discard_whitespace(lex_of(st), p) as int,
    decreases ps::items_left(st, p as int),
{
    lemma_is(st, p, t::Token::Whitespace);
    lemma_next(st, p);
    if ps::is(ps::next_token(st, p as int), t::Token::Whitespace) {
        lemma_is_empty(st, p);
        assert(!ps::is_empty(st, p as int));
        lemma_discard_whitespace(st, p + 1);
    }
}


} // verus!
