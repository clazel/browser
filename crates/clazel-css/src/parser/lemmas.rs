//! Theorems about the parser's spec. They are evidence that the transcription is right, and
//! what the exec parser relies on, not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The loop of "consume a stylesheet's contents" ends only on an empty stream.
proof fn lemma_stylesheet_ends_empty(input: TokenStream, index: int, rules: Seq<Rule>)
    ensures
        is_empty(input, stylesheets_contents_loop(input, index, rules).1),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Whitespace) {
        lemma_stylesheet_ends_empty(input, discard_a_token(input, index), rules);
    } else if is(item, Token::Eof) {
    } else if is(item, Token::Cdo) || is(item, Token::Cdc) {
        lemma_stylesheet_ends_empty(input, discard_a_token(input, index), rules);
    } else if is_at_keyword(item) {
        let (rule, next) = consume_an_at_rule(input, index, false);
        match rule {
            Some(rule) => lemma_stylesheet_ends_empty(input, moved(index, next), rules.push(rule)),
            None => lemma_stylesheet_ends_empty(input, moved(index, next), rules),
        }
    } else {
        let (result, next) = consume_a_qualified_rule(input, index, None, false);
        match result {
            QualifiedRuleResult::Rule { rule } => lemma_stylesheet_ends_empty(
                input,
                moved(index, next),
                rules.push(rule),
            ),
            _ => lemma_stylesheet_ends_empty(input, moved(index, next), rules),
        }
    }
}

/// "Consume a list of component values" with no stop token ends only on an empty stream, if
/// it is not nested.
proof fn lemma_list_ends_empty(input: TokenStream, index: int, values: Seq<ComponentValue>)
    ensures
        is_empty(input, list_of_component_values_loop(input, index, None, false, values).1),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) {
    } else if is(item, Token::CloseCurly) {
        let (token, next) = consume_a_token(input, index);
        lemma_list_ends_empty(input, next, values.push(token));
    } else {
        let (value, next) = consume_a_component_value(input, index);
        lemma_list_ends_empty(input, moved(index, next), values.push(value));
    }
}

/// See [`super::contract::parse_total`].
pub proof fn theorem_parse_total(input: TokenStream, index: int)
    ensures
        super::contract::parse_total(input, index),
{
    lemma_stylesheet_ends_empty(input, index, Seq::empty());
    lemma_list_ends_empty(input, index, Seq::empty());
}

/// The loop of "consume a simple block" stops where [`super::contract::blocks_balanced`] says.
proof fn lemma_block_loop_balanced(
    input: TokenStream,
    index: int,
    ending_token: Token,
    associated_token: Token,
    value: Seq<ComponentValue>,
)
    ensures
        ({
            let end = simple_block_loop(input, index, ending_token, associated_token, value).1;
            is_empty(input, end) || (1 <= end <= input.tokens.len() && is(
                input.tokens[end - 1],
                ending_token,
            ))
        }),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, ending_token)) {
        let (component_value, next) = consume_a_component_value(input, index);
        lemma_block_loop_balanced(
            input,
            moved(index, next),
            ending_token,
            associated_token,
            value.push(component_value),
        );
    }
}

/// See [`super::contract::blocks_balanced`].
pub proof fn theorem_blocks_balanced(input: TokenStream, index: int)
    ensures
        super::contract::blocks_balanced(input, index),
{
    let item = next_token(input, index);
    if is_open_bracket(item) {
        let associated_token = match item {
            ComponentValue::Token { token } => token,
            _ => Token::Eof,
        };
        lemma_block_loop_balanced(
            input,
            discard_a_token(input, index),
            mirror(item),
            associated_token,
            Seq::empty(),
        );
    }
}

/// Span `i` is what reading at the end of span `i - 1` gives: token `i`, and its end.
pub open spec fn reads(
    input: Seq<u32>,
    flag: bool,
    spans: Seq<Span>,
    tokens: Seq<Token>,
    i: int,
) -> bool {
    read_a_token(
        input,
        if i <= 0 {
            0
        } else {
            spans[i - 1].end
        },
        flag,
    ) == (tokens[i], spans[i].end)
}

/// [`spans_loop`] and [`tokenize_loop`] walk together, one span for each token read.
proof fn lemma_spans_walk(
    input: Seq<u32>,
    pos: int,
    flag: bool,
    spans: Seq<Span>,
    tokens: Seq<Token>,
)
    requires
        spans.len() == tokens.len(),
        pos == if spans.len() == 0 {
            0
        } else {
            spans.last().end
        },
        forall|i: int| 0 <= i < spans.len() ==> #[trigger] reads(input, flag, spans, tokens, i),
    ensures
        ({
            let all_spans = spans_loop(input, pos, flag, spans);
            let all_tokens = tokenize_loop(input, pos, flag, tokens);
            &&& all_spans.len() == all_tokens.len()
            &&& forall|i: int|
                0 <= i < all_spans.len() ==> #[trigger] reads(
                    input,
                    flag,
                    all_spans,
                    all_tokens,
                    i,
                )
        }),
    decreases remaining(input, pos),
{
    crate::tokenizer::termination::lemma_token_advances(input, pos, flag);
    let (token, next) = read_a_token(input, pos, flag);
    let pushed = spans.push(Span { start: consume_comments(input, pos), end: next });
    let read = tokens.push(token);
    assert forall|i: int| 0 <= i < pushed.len() implies #[trigger] reads(
        input,
        flag,
        pushed,
        read,
        i,
    ) by {
        if i < spans.len() {
            assert(reads(input, flag, spans, tokens, i));
            assert(pushed[i] == spans[i]);
            assert(read[i] == tokens[i]);
            if i > 0 {
                assert(pushed[i - 1] == spans[i - 1]);
            }
        } else if i > 0 {
            assert(pushed[i - 1] == spans[i - 1]);
            assert(spans[i - 1] == spans.last());
        }
    }
    if !(token is Eof) {
        lemma_spans_walk(input, next, flag, pushed, read);
    }
}

/// See [`super::contract::reader_is_the_stream`].
pub proof fn theorem_reader(string: Seq<u32>, unicode_ranges_allowed: bool)
    ensures
        super::contract::reader_is_the_stream(string, unicode_ranges_allowed),
{
    lemma_spans_walk(string, 0, unicode_ranges_allowed, Seq::empty(), Seq::empty());
    let stream = token_stream(string, unicode_ranges_allowed);
    let source = stream.source.unwrap();
    let tokens = tokenize_with(string, unicode_ranges_allowed);
    assert forall|index: int| #[trigger] super::contract::reader_matches(
        string,
        unicode_ranges_allowed,
        index,
    ) by {
        if 0 <= index < stream.tokens.len() {
            assert(reads(string, unicode_ranges_allowed, source.spans, tokens, index));
        }
    }
}

} // verus!
