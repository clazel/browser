//! What every output of the parser is made of, proven once for the facts that the
//! equivalence of the hooks ([`super::equiv_hooks`]) and
//! [`crate::parser::contract::output_preserved`] both need: a component value that
//! [`good`] has, at every depth, no `<function-token>`, `<{-token>`, `<(-token>` or
//! `<[-token>` among its tokens (§5.2's note: they are consumed into functions and
//! simple blocks), and only numbers that [`super::equiv_anb::int_ok`] accepts.
//!
//! The proofs follow the recursion of the spec's "consume a component value", "consume
//! a simple block", "consume a function" and "consume a list of component values", by
//! how many items of the stream are left.

#[cfg(verus_only)]
use super::equiv_anb::*;
#[cfg(verus_only)]
use super::*;
#[cfg(verus_only)]
use crate::parser::spec as ps;
#[cfg(verus_only)]
use crate::tokenizer::spec as t;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A token that is none of the four that never reach an output nor the `<EOF-token>`, and
/// has [`tok_ok`] numbers.
pub open spec fn good_tok(k: t::Token) -> bool {
    !(k is Function || k is OpenCurly || k is OpenParen || k is OpenSquare || k is Eof) && tok_ok(k)
}

/// A component value that is [`good`], at every depth.
pub open spec fn good(x: ps::ComponentValue) -> bool
    decreases x, 0nat,
{
    match x {
        ps::ComponentValue::Token { token } => good_tok(token),
        ps::ComponentValue::Function { value, .. } => all_good(value, value.len()),
        ps::ComponentValue::SimpleBlock { value, .. } => all_good(value, value.len()),
    }
}

/// [`good`] for the first `n` of `values`.
pub open spec fn all_good(values: Seq<ps::ComponentValue>, n: nat) -> bool
    decreases values, n,
{
    n == 0 || n > values.len() || (all_good(values, (n - 1) as nat) && good(values[n - 1]))
}

/// A stream all of whose items are tokens with [`tok_ok`] numbers.
pub open spec fn stream_ok(st: ps::TokenStream) -> bool {
    forall|i: int|
        0 <= i < st.tokens.len() ==> (#[trigger] st.tokens[i] is Token && tok_ok(st.tokens[i]->Token_token))
}

/// Pushing a good item on a good list gives a good list.
pub proof fn lemma_all_good_prefix(values: Seq<ps::ComponentValue>, x: ps::ComponentValue, n: nat)
    requires
        n <= values.len(),
    ensures
        all_good(values.push(x), n) == all_good(values, n),
    decreases n,
{
    if n > 0 {
        lemma_all_good_prefix(values, x, (n - 1) as nat);
        assert(values.push(x)[(n - 1) as int] == values[(n - 1) as int]);
    }
}

/// The list with a good item pushed.
pub proof fn lemma_all_good_push(values: Seq<ps::ComponentValue>, x: ps::ComponentValue)
    requires
        all_good(values, values.len()),
        good(x),
    ensures
        all_good(values.push(x), values.push(x).len()),
{
    lemma_all_good_prefix(values, x, values.len());
    assert(values.push(x)[values.len() as int] == x);
}

/// "Consume a component value" gives a good one.
pub proof fn lemma_cv_good(st: ps::TokenStream, p: int)
    requires
        stream_ok(st),
        !ps::is(ps::next_token(st, p), t::Token::Eof),
    ensures
        good(ps::consume_a_component_value(st, p).0),
    decreases ps::items_left(st, p), 1nat,
{
    let item = ps::next_token(st, p);
    if ps::is_open_bracket(item) {
        lemma_sb_good(st, p);
    } else if ps::is_function_token(item) {
        lemma_fn_good(st, p);
    }
}

/// "Consume a simple block" gives a good one.
pub proof fn lemma_sb_good(st: ps::TokenStream, p: int)
    requires
        stream_ok(st),
        ps::is_open_bracket(ps::next_token(st, p)),
    ensures
        good(ps::consume_a_simple_block(st, p).0),
    decreases ps::items_left(st, p), 0nat,
{
    let item = ps::next_token(st, p);
    let assoc = match item {
        ps::ComponentValue::Token { token } => token,
        _ => t::Token::Eof,
    };
    assert(!ps::is_empty(st, p));
    lemma_sbl_good(st, ps::discard_a_token(st, p), ps::mirror(item), assoc, Seq::empty());
}

/// The loop of "consume a simple block" gives a good one.
pub proof fn lemma_sbl_good(
    st: ps::TokenStream,
    index: int,
    ending: t::Token,
    assoc: t::Token,
    value: Seq<ps::ComponentValue>,
)
    requires
        stream_ok(st),
        all_good(value, value.len()),
    ensures
        good(ps::simple_block_loop(st, index, ending, assoc, value).0),
    decreases ps::items_left(st, index), 2nat,
{
    let item = ps::next_token(st, index);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, ending)) {
        lemma_cv_good(st, index);
        let (cv, next) = ps::consume_a_component_value(st, index);
        lemma_all_good_push(value, cv);
        assert(index < st.tokens.len());
        lemma_sbl_good(st, ps::moved(index, next), ending, assoc, value.push(cv));
    }
}

/// "Consume a function" gives a good one.
pub proof fn lemma_fn_good(st: ps::TokenStream, p: int)
    requires
        stream_ok(st),
        ps::is_function_token(ps::next_token(st, p)),
    ensures
        good(ps::consume_a_function(st, p).0),
    decreases ps::items_left(st, p), 0nat,
{
    let (token, next) = ps::consume_a_token(st, p);
    assert(!ps::is_empty(st, p));
    lemma_fl_good(st, next, ps::token_value(token), Seq::empty());
}

/// The loop of "consume a function" gives a good one.
pub proof fn lemma_fl_good(st: ps::TokenStream, index: int, name: Seq<u32>, value: Seq<ps::ComponentValue>)
    requires
        stream_ok(st),
        all_good(value, value.len()),
    ensures
        good(ps::function_loop(st, index, name, value).0),
    decreases ps::items_left(st, index), 2nat,
{
    let item = ps::next_token(st, index);
    if !(ps::is(item, t::Token::Eof) || ps::is(item, t::Token::CloseParen)) {
        lemma_cv_good(st, index);
        let (cv, next) = ps::consume_a_component_value(st, index);
        lemma_all_good_push(value, cv);
        assert(index < st.tokens.len());
        lemma_fl_good(st, ps::moved(index, next), name, value.push(cv));
    }
}

/// "Consume a list of component values" gives a good list.
pub proof fn lemma_list_good(
    st: ps::TokenStream,
    index: int,
    stop: Option<t::Token>,
    nested: bool,
    values: Seq<ps::ComponentValue>,
)
    requires
        stream_ok(st),
        all_good(values, values.len()),
    ensures
        ({
            let r = ps::list_of_component_values_loop(st, index, stop, nested, values).0;
            all_good(r, r.len())
        }),
    decreases ps::items_left(st, index),
{
    let item = ps::next_token(st, index);
    if !(ps::is(item, t::Token::Eof) || ps::is_stop(item, stop)) {
        if ps::is(item, t::Token::CloseCurly) {
            if !nested {
                let (token, next) = ps::consume_a_token(st, index);
                assert(good(token));
                lemma_all_good_push(values, token);
                assert(index < st.tokens.len());
                lemma_list_good(st, next, stop, nested, values.push(token));
            }
        } else {
            lemma_cv_good(st, index);
            let (cv, next) = ps::consume_a_component_value(st, index);
            lemma_all_good_push(values, cv);
            assert(index < st.tokens.len());
            lemma_list_good(st, ps::moved(index, next), stop, nested, values.push(cv));
        }
    }
}

/// The stream of a string, tokenized, is [`stream_ok`].
pub proof fn lemma_string_stream_ok(string: Seq<u32>, u: bool)
    ensures
        stream_ok(ps::token_stream(string, u)),
{
    super::equiv_anb::lemma_tokenize_ok(string, 0, u, Seq::empty());
    let toks = t::tokenize_with(string, u);
    assert(ps::token_stream(string, u).tokens == ps::as_items(toks));
    assert forall|i: int| 0 <= i < ps::token_stream(string, u).tokens.len() implies (
        #[trigger] ps::token_stream(string, u).tokens[i] is Token && tok_ok(
        ps::token_stream(string, u).tokens[i]->Token_token)) by {
        assert(ps::as_items(toks)[i] == (ps::ComponentValue::Token { token: toks[i] }));
    }
}

/// A good value has only the preserved tokens, and a good list is a [`preserved`] one.
pub proof fn lemma_good_preserved(x: ps::ComponentValue)
    requires
        good(x),
    ensures
        crate::parser::contract::preserved_only(x),
    decreases x, 0nat,
{
    match x {
        ps::ComponentValue::Token { .. } => {},
        ps::ComponentValue::Function { value, .. } => lemma_all_good_preserved(value, value.len()),
        ps::ComponentValue::SimpleBlock { value, .. } => lemma_all_good_preserved(value, value.len()),
    }
}

/// [`lemma_good_preserved`] for the first `n` of a list.
pub proof fn lemma_all_good_preserved(values: Seq<ps::ComponentValue>, n: nat)
    requires
        all_good(values, n),
    ensures
        crate::parser::contract::all_preserved(values, n),
    decreases values, n,
{
    if n > 0 && n <= values.len() {
        lemma_all_good_preserved(values, (n - 1) as nat);
        lemma_good_preserved(values[(n - 1) as int]);
    }
}

/// A good item of a list is [`item_ok`].
pub proof fn lemma_all_good_item_ok(values: Seq<ps::ComponentValue>)
    requires
        all_good(values, values.len()),
    ensures
        cvs_ok(values),
{
    assert forall|i: int| 0 <= i < values.len() implies #[trigger] item_ok(values[i]) by {
        lemma_all_good_at(values, values.len(), i);
    }
}

/// Each of the first `n` items of a good list is good.
pub proof fn lemma_all_good_at(values: Seq<ps::ComponentValue>, n: nat, i: int)
    requires
        all_good(values, n),
        0 <= i < n,
        n <= values.len(),
    ensures
        good(values[i]),
    decreases n,
{
    if i < n - 1 {
        lemma_all_good_at(values, (n - 1) as nat, i);
    }
}

/// The lists of "parse a comma-separated list of component values" are good lists.
pub proof fn lemma_comma_good(st: ps::TokenStream, index: int, groups: Seq<Seq<ps::ComponentValue>>)
    requires
        stream_ok(st),
        forall|i: int| 0 <= i < groups.len() ==> all_good(#[trigger] groups[i], groups[i].len()),
    ensures
        ({
            let r = ps::comma_separated_list_loop(st, index, groups);
            forall|i: int| 0 <= i < r.len() ==> all_good(#[trigger] r[i], r[i].len())
        }),
    decreases ps::items_left(st, index),
{
    if !ps::is_empty(st, index) {
        let (list, next) = ps::consume_a_list_of_component_values(st, index, Some(t::Token::Comma), false);
        lemma_list_good(st, index, Some(t::Token::Comma), false, Seq::empty());
        let pushed = groups.push(list);
        assert forall|i: int| 0 <= i < pushed.len() implies all_good(#[trigger] pushed[i], pushed[i].len()) by {
            if i < groups.len() {
                assert(pushed[i] == groups[i]);
            } else {
                assert(pushed[i] == list);
            }
        }
        assert(index < st.tokens.len());
        lemma_comma_good(st, ps::moved(index, ps::discard_a_token(st, next)), pushed);
        assert(ps::comma_separated_list_loop(st, index, groups) == ps::comma_separated_list_loop(
            st,
            ps::moved(index, ps::discard_a_token(st, next)),
            pushed,
        ));
    } else {
        assert(ps::comma_separated_list_loop(st, index, groups) == groups);
    }
}

/// The list "parse a list of component values" returns of a string is good.
pub proof fn lemma_parse_list_good(string: Seq<u32>)
    ensures
        ({
            let v = ps::parse_a_list_of_component_values(ps::Input::String { string });
            all_good(v, v.len())
        }),
{
    let (stream, index) = ps::normalize(ps::Input::String { string });
    lemma_string_stream_ok(t::filter_code_points(string), false);
    assert(stream == ps::token_stream(t::filter_code_points(string), false));
    lemma_list_good(stream, 0, None, false, Seq::empty());
}

/// The lists "parse a comma-separated list of component values" returns of a string are
/// good.
pub proof fn lemma_parse_groups_good(string: Seq<u32>)
    ensures
        ({
            let r = ps::parse_a_comma_separated_list_of_component_values(ps::Input::String { string });
            forall|i: int| 0 <= i < r.len() ==> all_good(#[trigger] r[i], r[i].len())
        }),
{
    let (stream, index) = ps::normalize(ps::Input::String { string });
    lemma_string_stream_ok(t::filter_code_points(string), false);
    assert(stream == ps::token_stream(t::filter_code_points(string), false));
    lemma_comma_good(stream, 0, Seq::empty());
}

} // verus!
