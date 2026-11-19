//! Proofs of the theorems that [`super::contract`] states and [`super::lemmas`] does not
//! prove. Each is proven for the statement as `contract.rs` has it, for every input
//! string, with no added assumption. The README of the crate says which of the
//! planned theorems are proven here.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::independent::equiv_good::*;

verus! {

/// `theorem_output_preserved`: §5.2's note, "never appear in any parser output". No
/// `<function-token>`, `<{-token>`, `<(-token>` or `<[-token>` is in the list "parse a list
/// of component values" returns, however deep in functions and simple blocks.
pub proof fn theorem_output_preserved(string: Seq<u32>)
    ensures
        output_preserved(string),
{
    let (stream, index) = normalize(Input::String { string });
    lemma_string_stream_ok(filter_code_points(string), false);
    assert(stream == token_stream(filter_code_points(string), false));
    lemma_list_good(stream, 0, None, false, Seq::empty());
    let values = parse_a_list_of_component_values(Input::String { string });
    lemma_all_good_preserved(values, values.len());
}

/// `theorem_block_ends_agree`: "consume a block" and "consume a simple block" end at the same
/// index, for every token stream, whatever its items. See [`super::blocks`].
pub proof fn theorem_block_ends_agree(input: TokenStream, index: int)
    ensures
        block_ends_agree(input, index),
{
    if is(next_token(input, index), Token::OpenCurly) {
        super::blocks::lemma_block_agrees(input, index);
    }
}

/// `theorem_parse_bounded`: the output's component values number at most the code points of
/// the input, so at most those and one. See [`super::bounded`], which counts the code points
/// each part of the output was read from, and the unicode-range values, read a second time,
/// from the text they had in the first.
pub proof fn theorem_parse_bounded(string: Seq<u32>)
    ensures
        parse_bounded(string),
{
    let filtered = filter_code_points(string);
    let stream = token_stream(filtered, false);
    super::bounded::lemma_stream_costed(filtered, false);
    super::bounded::lemma_stylesheet_bound(stream, 0, Seq::empty());
    let (rules, end) = stylesheets_contents_loop(stream, 0, Seq::empty());
    super::bounded::lemma_pos_in_text(stream, end);
    assert(rules_size(Seq::<Rule>::empty(), 0) == 0);
    assert(super::bounded::pos(stream, 0) == 0);
    assert(stream.source->Some_0.text == filtered);
}

// ------------------------------------------------------------------------------------
// theorem_value_end
// ------------------------------------------------------------------------------------

/// A simple block is what the loop of "consume a simple block" returns.
proof fn lemma_sbl_is_block(
    input: TokenStream,
    index: int,
    ending: Token,
    assoc: Token,
    value: Seq<ComponentValue>,
)
    ensures
        simple_block_loop(input, index, ending, assoc, value).0 is SimpleBlock,
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, ending)) {
        let (cv, next) = consume_a_component_value(input, index);
        assert(index < input.tokens.len());
        lemma_sbl_is_block(input, moved(index, next), ending, assoc, value.push(cv));
    }
}

/// A function is what the loop of "consume a function" returns.
proof fn lemma_fl_is_function(input: TokenStream, index: int, name: Seq<u32>, value: Seq<ComponentValue>)
    ensures
        function_loop(input, index, name, value).0 is Function,
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, Token::CloseParen)) {
        let (cv, next) = consume_a_component_value(input, index);
        assert(index < input.tokens.len());
        lemma_fl_is_function(input, moved(index, next), name, value.push(cv));
    }
}

/// "Consume a component value" gives a token only as "consume a token" does: the item at
/// the index, one step on.
proof fn lemma_cv_token_is_item(input: TokenStream, p: int)
    requires
        !is_empty(input, p),
    ensures
        consume_a_component_value(input, p).0 is Token ==> consume_a_component_value(input, p) == (
            input.tokens[p],
            p + 1,
        ),
{
    let item = next_token(input, p);
    assert(p < input.tokens.len());
    if is_open_bracket(item) {
        let assoc = match item {
            ComponentValue::Token { token } => token,
            _ => Token::Eof,
        };
        lemma_sbl_is_block(input, discard_a_token(input, p), mirror(item), assoc, Seq::empty());
    } else if is_function_token(item) {
        let (token, next) = consume_a_token(input, p);
        lemma_fl_is_function(input, next, token_value(token), Seq::empty());
    }
}

/// "Consume a component value" does not go past the end of a stream that is not empty,
/// nor do the loops of the simple block and the function from an index in the stream.
pub proof fn lemma_cv_within(input: TokenStream, p: int)
    requires
        0 <= p < input.tokens.len(),
    ensures
        consume_a_component_value(input, p).1 <= input.tokens.len(),
    decreases items_left(input, p), 1nat,
{
    let item = next_token(input, p);
    if is_open_bracket(item) {
        let assoc = match item {
            ComponentValue::Token { token } => token,
            _ => Token::Eof,
        };
        lemma_sbl_within(input, p + 1, mirror(item), assoc, Seq::empty());
    } else if is_function_token(item) {
        lemma_fl_within(input, p + 1, token_value(item), Seq::empty());
    }
}

/// The loop of "consume a simple block" does not go past the end of the stream.
proof fn lemma_sbl_within(
    input: TokenStream,
    index: int,
    ending: Token,
    assoc: Token,
    value: Seq<ComponentValue>,
)
    requires
        0 <= index <= input.tokens.len(),
    ensures
        simple_block_loop(input, index, ending, assoc, value).1 <= input.tokens.len(),
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, ending)) {
        assert(index < input.tokens.len());
        lemma_cv_within(input, index);
        crate::parser::termination::lemma_component_value_advances(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_sbl_within(input, moved(index, next), ending, assoc, value.push(cv));
    }
}

/// The loop of "consume a function" does not go past the end of the stream.
proof fn lemma_fl_within(input: TokenStream, index: int, name: Seq<u32>, value: Seq<ComponentValue>)
    requires
        0 <= index <= input.tokens.len(),
    ensures
        function_loop(input, index, name, value).1 <= input.tokens.len(),
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, Token::CloseParen)) {
        assert(index < input.tokens.len());
        lemma_cv_within(input, index);
        crate::parser::termination::lemma_component_value_advances(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_fl_within(input, moved(index, next), name, value.push(cv));
    }
}

/// The last `m` of `values` are tokens.
pub open spec fn tokens_at_end(values: Seq<ComponentValue>, m: int) -> bool {
    forall|k: int| values.len() - m <= k < values.len() ==> #[trigger] values[k] is Token
}

/// What the loop of "consume a list of component values" keeps as it goes: the tokens at
/// the end of what it has collected are the items of the stream before the index.
pub open spec fn exact_suffix(values: Seq<ComponentValue>, idx: int, tokens: Seq<ComponentValue>) -> bool {
    &&& 0 <= idx <= tokens.len()
    &&& forall|m: int|
        #![trigger tokens_at_end(values, m)]
        0 <= m <= values.len() && tokens_at_end(values, m) ==> (m <= idx && values.subrange(
            values.len() as int - m,
            values.len() as int,
        ) == tokens.subrange(idx - m, idx))
}

/// The loop of "consume a list of component values" keeps [`exact_suffix`].
proof fn lemma_list_exact(
    input: TokenStream,
    index: int,
    stop: Option<Token>,
    nested: bool,
    values: Seq<ComponentValue>,
)
    requires
        exact_suffix(values, index, input.tokens),
    ensures
        ({
            let (list, end) = list_of_component_values_loop(input, index, stop, nested, values);
            exact_suffix(list, end, input.tokens)
        }),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is_stop(item, stop)) {
        assert(index < input.tokens.len());
        let (x, next) = if is(item, Token::CloseCurly) && !nested {
            consume_a_token(input, index)
        } else {
            consume_a_component_value(input, index)
        };
        if is(item, Token::CloseCurly) {
            if !nested {
                lemma_step_exact(input, index, values, x, index + 1);
                lemma_list_exact(input, next, stop, nested, values.push(x));
            }
        } else {
            lemma_cv_token_is_item(input, index);
            lemma_cv_within(input, index);
            crate::parser::termination::lemma_component_value_advances(input, index);
            lemma_step_exact(input, index, values, x, moved(index, next));
            lemma_list_exact(input, moved(index, next), stop, nested, values.push(x));
        }
    }
}

/// One step: an item pushed, that is the item at the index, one step on, if it is a token;
/// or is not one and the index is in the stream.
proof fn lemma_step_exact(
    input: TokenStream,
    index: int,
    values: Seq<ComponentValue>,
    x: ComponentValue,
    after: int,
)
    requires
        exact_suffix(values, index, input.tokens),
        0 <= index < input.tokens.len(),
        index < after <= input.tokens.len(),
        x is Token ==> (x == input.tokens[index] && after == index + 1),
    ensures
        exact_suffix(values.push(x), after, input.tokens),
{
    let pushed = values.push(x);
    assert(pushed.len() == values.len() + 1);
    assert forall|m: int|
        #![trigger tokens_at_end(pushed, m)]
        0 <= m <= pushed.len() && tokens_at_end(pushed, m) implies (m <= after && pushed.subrange(
        pushed.len() as int - m,
        pushed.len() as int,
    ) == input.tokens.subrange(after - m, after)) by {
        if m == 0 {
            assert(pushed.subrange(pushed.len() as int, pushed.len() as int) =~= Seq::<ComponentValue>::empty());
            assert(input.tokens.subrange(after as int, after as int) =~= Seq::<ComponentValue>::empty());
        } else {
            assert(pushed[pushed.len() - 1] == x);
            assert(x is Token);
            assert forall|k: int| values.len() - (m - 1) <= k < values.len() implies #[trigger] values[k] is Token by {
                assert(pushed[k] == values[k]);
            }
            assert(tokens_at_end(values, m - 1));
            assert(0 <= m - 1 <= values.len());
            assert(m - 1 <= index);
            assert(pushed.subrange(pushed.len() as int - m, pushed.len() as int) =~= values.subrange(
                values.len() - (m - 1),
                values.len() as int,
            ).push(x)) by {
                assert forall|k: int| 0 <= k < m implies #[trigger] pushed.subrange(pushed.len() as int - m, pushed.len() as int)[k]
                    == values.subrange(values.len() - (m - 1), values.len() as int).push(x)[k] by {
                    if k < m - 1 {
                        assert(pushed[values.len() - (m - 1) + k] == values[values.len() - (m - 1) + k]);
                    }
                }
            }
            assert(input.tokens.subrange(after - m, after) =~= input.tokens.subrange(index - (m - 1), index).push(
                input.tokens[index],
            ));
        }
    }
}

/// `theorem_value_end`: the tokens at the end of the list that "consume a list of component
/// values" returns are the items of the stream before where it stopped. Stated in
/// `contract.rs` for every `start`; `subrange` has no meaning for a `start` outside the
/// stream, so this is proven for the starts inside it (`0 <= start <= input.tokens.len()`),
/// which is every start a parser has.
pub proof fn theorem_value_end(input: TokenStream, start: int, nested: bool, kept: int)
    requires
        0 <= start <= input.tokens.len(),
    ensures
        value_end_is_exact(input, start, nested, kept),
{
    assert(exact_suffix(Seq::<ComponentValue>::empty(), start, input.tokens)) by {
        assert forall|m: int|
            #![trigger tokens_at_end(Seq::<ComponentValue>::empty(), m)]
            0 <= m <= 0 && tokens_at_end(Seq::<ComponentValue>::empty(), m) implies (m <= start
            && Seq::<ComponentValue>::empty().subrange(0, 0) == input.tokens.subrange(start - m, start)) by {
            assert(Seq::<ComponentValue>::empty().subrange(0, 0) =~= Seq::<ComponentValue>::empty());
            assert(input.tokens.subrange(start, start) =~= Seq::<ComponentValue>::empty());
        }
    }
    lemma_list_exact(input, start, Some(Token::Semicolon), nested, Seq::empty());
    let (list, end) = consume_a_list_of_component_values(input, start, Some(Token::Semicolon), nested);
    if 0 <= kept <= list.len() && forall|k: int| kept <= k < list.len() ==> #[trigger] list[k] is Token {
        let m = list.len() - kept;
        assert(tokens_at_end(list, m));
    }
}

// ------------------------------------------------------------------------------------
// theorem_spans_in_order
// ------------------------------------------------------------------------------------

/// What [`spans_loop`] keeps as it goes: every span so far lies in the string, and each
/// starts where the one before it ended or later; the last ends at `pos`.
pub open spec fn spans_ok(input: Seq<u32>, spans: Seq<Span>, pos: int) -> bool {
    &&& 0 <= pos <= input.len()
    &&& spans.len() > 0 ==> spans.last().end == pos
    &&& forall|i: int|
        0 <= i < spans.len() ==> 0 <= #[trigger] spans[i].start <= spans[i].end <= input.len()
    &&& forall|i: int| 0 <= i && i + 1 < spans.len() ==> #[trigger] spans[i].end <= spans[i + 1].start
}

/// [`spans_loop`] keeps [`spans_ok`], for a string of any `u32`s.
proof fn lemma_spans_loop_ok(input: Seq<u32>, pos: int, flag: bool, spans: Seq<Span>)
    requires
        spans_ok(input, spans, pos),
    ensures
        ({
            let all = spans_loop(input, pos, flag, spans);
            &&& all.len() > spans.len()
            &&& forall|i: int| 0 <= i < all.len() ==> 0 <= #[trigger] all[i].start <= all[i].end <= input.len()
            &&& forall|i: int| 0 <= i && i + 1 < all.len() ==> #[trigger] all[i].end <= all[i + 1].start
        }),
    decreases remaining(input, pos),
{
    crate::tokenizer::termination::lemma_token_advances(input, pos, flag);
    crate::tokenizer::termination::lemma_comments_advance(input, pos);
    crate::tokenizer::lemmas::lemma_token_within(input, pos, flag);
    let (token, next) = read_a_token(input, pos, flag);
    let span = Span { start: consume_comments(input, pos), end: next };
    let pushed = spans.push(span);
    assert(span.start >= pos);
    assert(span.start <= span.end);
    assert(span.end <= input.len());
    assert(spans_ok(input, pushed, next)) by {
        assert forall|i: int| 0 <= i < pushed.len() implies 0 <= #[trigger] pushed[i].start
            <= pushed[i].end <= input.len() by {
            if i < spans.len() {
                assert(pushed[i] == spans[i]);
            }
        }
        assert forall|i: int| 0 <= i && i + 1 < pushed.len() implies #[trigger] pushed[i].end
            <= pushed[i + 1].start by {
            if i + 1 < spans.len() {
                assert(pushed[i] == spans[i]);
                assert(pushed[i + 1] == spans[i + 1]);
            } else {
                assert(pushed[i] == spans.last());
            }
        }
    }
    if !(token is Eof) {
        lemma_spans_loop_ok(input, next, flag, pushed);
    }
}

/// `theorem_spans_in_order`: for every string of `u32`s, not only code points. A code
/// point above U+10FFFF in the input is read as an ordinary one, and EOF (U+110000)
/// inside the input ends the tokens, with the EOF token's span, empty, where it stops.
pub proof fn theorem_spans_in_order(string: Seq<u32>, unicode_ranges_allowed: bool)
    ensures
        super::contract::spans_in_order(string, unicode_ranges_allowed),
{
    let empty = Seq::<Span>::empty();
    assert(spans_ok(string, empty, 0));
    lemma_spans_loop_ok(string, 0, unicode_ranges_allowed, empty);
    super::lemmas::lemma_spans_walk(string, 0, unicode_ranges_allowed, Seq::empty(), Seq::empty());
    let tokens = tokenize_with(string, unicode_ranges_allowed);
    let all = spans_loop(string, 0, unicode_ranges_allowed, empty);
    assert(all.len() == tokens.len());
    assert(token_stream(string, unicode_ranges_allowed).tokens.len() == tokens.len());
}

} // verus!
