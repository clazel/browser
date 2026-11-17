//! Why the output of the parser holds at most as many component values as the input has
//! code points ([`super::contract::parse_bounded`]), proven in [`super::theorems`] from
//! these.
//!
//! Every position of a stream made from a string is a code point count: [`pos`] of an
//! index is where the tokens before it end. What a loop of the spec takes out of the
//! stream, from an index to the one it reaches, holds at most [`cost`] of that range
//! component values, since each token costs at least one code point, and the cost of
//! adjacent ranges adds up. The value of a unicode-range descriptor, which is read from
//! the text of the tokens again, holds at most as many values as that text has code
//! points, which is at most the cost of those tokens. So everything is stated of a stream
//! that is [`costed`], and the sum is the position of the end of the sheet, at most the
//! length of the string.

#[cfg(verus_only)]
use super::contract::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::termination::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Costs
// ------------------------------------------------------------------------------------

/// The code points before index `i` of the stream, up to the end of the token before it.
pub open spec fn pos(st: TokenStream, i: int) -> int {
    position_of(st.source->Some_0, i)
}

/// The code points from the end of the token before `a` to that of the token before `b`.
pub open spec fn cost(st: TokenStream, a: int, b: int) -> int {
    pos(st, b) - pos(st, a)
}

/// A stream made from a string: a span for each item, in order and inside the text, each
/// item a token, and each token but EOF ends after the one before it.
pub open spec fn costed(st: TokenStream) -> bool {
    &&& st.source is Some
    &&& st.source->Some_0.spans.len() == st.tokens.len()
    &&& forall|i: int| 0 <= i < st.tokens.len() ==> #[trigger] st.tokens[i] is Token
    &&& forall|i: int|
        0 <= i < st.tokens.len() ==> 0 <= #[trigger] st.source->Some_0.spans[i].start
            <= st.source->Some_0.spans[i].end <= st.source->Some_0.text.len()
    &&& forall|i: int|
        0 <= i && i + 1 < st.tokens.len() ==> #[trigger] st.source->Some_0.spans[i].end
            <= st.source->Some_0.spans[i + 1].start
    &&& forall|i: int|
        0 <= i < st.tokens.len() && !(is(#[trigger] st.tokens[i], Token::Eof)) ==> st.source->Some_0.spans[i].end
            > position_of(st.source->Some_0, i)
}

/// The spans of the stream of a string are in the text and in order.
proof fn lemma_stream_spans(string: Seq<u32>, flag: bool)
    ensures
        ({
            let st = token_stream(string, flag);
            let source = st.source->Some_0;
            &&& st.source is Some
            &&& source.spans.len() == st.tokens.len()
            &&& forall|i: int|
                0 <= i < st.tokens.len() ==> 0 <= #[trigger] source.spans[i].start
                    <= source.spans[i].end <= source.text.len()
            &&& forall|i: int|
                0 <= i && i + 1 < st.tokens.len() ==> #[trigger] source.spans[i].end
                    <= source.spans[i + 1].start
        }),
{
    super::theorems::theorem_spans_in_order(string, flag);
    let st = token_stream(string, flag);
    let source = st.source->Some_0;
    let all = st.source.unwrap().spans;
    assert(all == source.spans);
    assert(source.text == string);
    assert forall|i: int|
        0 <= i < st.tokens.len() implies 0 <= #[trigger] source.spans[i].start <= source.spans[i].end
        <= source.text.len() by {
        assert(0 <= all[i].start);
    }
    assert forall|i: int|
        0 <= i && i + 1 < st.tokens.len() implies #[trigger] source.spans[i].end
        <= source.spans[i + 1].start by {
        assert(0 <= all[i].start);
    }
}

/// Each token of the stream of a string but EOF ends after where it was read from.
proof fn lemma_stream_strict(string: Seq<u32>, flag: bool)
    ensures
        ({
            let st = token_stream(string, flag);
            let source = st.source->Some_0;
            &&& forall|i: int| 0 <= i < st.tokens.len() ==> #[trigger] st.tokens[i] is Token
            &&& forall|i: int|
                0 <= i < st.tokens.len() && !(is(#[trigger] st.tokens[i], Token::Eof))
                    ==> source.spans[i].end > position_of(source, i)
        }),
{
    super::lemmas::lemma_spans_walk(string, 0, flag, Seq::empty(), Seq::empty());
    let st = token_stream(string, flag);
    let tokens = tokenize_with(string, flag);
    let source = st.source->Some_0;
    assert forall|i: int| 0 <= i < st.tokens.len() implies #[trigger] st.tokens[i] is Token by {
        assert(st.tokens[i] == (ComponentValue::Token { token: tokens[i] }));
    }
    assert forall|i: int|
        0 <= i < st.tokens.len() && !(is(#[trigger] st.tokens[i], Token::Eof)) implies source.spans[i].end
        > position_of(source, i) by {
        assert(super::lemmas::reads(string, flag, source.spans, tokens, i));
        crate::tokenizer::termination::lemma_token_advances(string, position_of(source, i), flag);
        assert(st.tokens[i] == (ComponentValue::Token { token: tokens[i] }));
    }
}

/// The stream of every string is [`costed`], with unicode ranges allowed or not.
pub proof fn lemma_stream_costed(string: Seq<u32>, flag: bool)
    ensures
        costed(token_stream(string, flag)),
{
    lemma_stream_spans(string, flag);
    lemma_stream_strict(string, flag);
}

/// The positions of a [`costed`] stream do not go back.
pub proof fn lemma_pos_mono(st: TokenStream, i: int, j: int)
    requires
        costed(st),
        0 <= i <= j <= st.tokens.len(),
    ensures
        pos(st, i) <= pos(st, j),
    decreases j - i,
{
    if i < j {
        let source = st.source->Some_0;
        assert(pos(st, i) <= pos(st, i + 1)) by {
            assert(pos(st, i + 1) == source.spans[i].end);
            assert(0 <= source.spans[i].start <= source.spans[i].end);
            if i > 0 {
                assert(pos(st, i) == source.spans[i - 1].end);
                assert(source.spans[i - 1].end <= source.spans[i].start);
            }
        }
        lemma_pos_mono(st, i + 1, j);
    }
}

/// The position of an index is in the text.
pub proof fn lemma_pos_in_text(st: TokenStream, j: int)
    requires
        costed(st),
        0 <= j <= st.tokens.len(),
    ensures
        0 <= pos(st, j) <= st.source->Some_0.text.len(),
{
    if j > 0 {
        assert(pos(st, j) == st.source->Some_0.spans[j - 1].end);
        assert(0 <= st.source->Some_0.spans[j - 1].start);
        assert(st.source->Some_0.spans[j - 1].end <= st.source->Some_0.text.len());
    }
}

/// A token that is not EOF costs a code point.
pub proof fn lemma_token_costs(st: TokenStream, i: int)
    requires
        costed(st),
        0 <= i < st.tokens.len(),
        !(is(st.tokens[i], Token::Eof)),
    ensures
        cost(st, i, i + 1) >= 1,
{
    assert(pos(st, i + 1) == st.source->Some_0.spans[i].end);
}

/// A token that is the next one and is not EOF costs a code point, and is in the stream.
pub proof fn lemma_next_costs(st: TokenStream, i: int)
    requires
        costed(st),
        0 <= i <= st.tokens.len(),
        !is_empty(st, i),
    ensures
        i < st.tokens.len(),
        cost(st, i, i + 1) >= 1,
        value_size(next_token(st, i)) == 1,
{
    assert(i < st.tokens.len());
    lemma_token_costs(st, i);
}

// ------------------------------------------------------------------------------------
// Sizes of lists, with an item added or taken out
// ------------------------------------------------------------------------------------

/// The first `n` items' size does not change when one is added at the end.
proof fn lemma_values_size_prefix(values: Seq<ComponentValue>, x: ComponentValue, n: nat)
    requires
        n <= values.len(),
    ensures
        values_size(values.push(x), n) == values_size(values, n),
    decreases n,
{
    if n > 0 {
        lemma_values_size_prefix(values, x, (n - 1) as nat);
        assert(values.push(x)[(n - 1) as int] == values[(n - 1) as int]);
    }
}

/// What a list holds, and one more item.
pub proof fn lemma_values_size_push(values: Seq<ComponentValue>, x: ComponentValue)
    ensures
        values_size(values.push(x), values.push(x).len()) == values_size(values, values.len())
            + value_size(x),
{
    lemma_values_size_prefix(values, x, values.len());
    assert(values.push(x)[values.len() as int] == x);
}

/// [`lemma_values_size_prefix`] for declarations.
proof fn lemma_declarations_size_prefix(ds: Seq<Declaration>, x: Declaration, n: nat)
    requires
        n <= ds.len(),
    ensures
        declarations_size(ds.push(x), n) == declarations_size(ds, n),
    decreases n,
{
    if n > 0 {
        lemma_declarations_size_prefix(ds, x, (n - 1) as nat);
        assert(ds.push(x)[(n - 1) as int] == ds[(n - 1) as int]);
    }
}

/// What a list of declarations holds, and one more.
pub proof fn lemma_declarations_size_push(ds: Seq<Declaration>, x: Declaration)
    ensures
        declarations_size(ds.push(x), ds.push(x).len()) == declarations_size(ds, ds.len())
            + values_size(x.value, x.value.len()),
{
    lemma_declarations_size_prefix(ds, x, ds.len());
    assert(ds.push(x)[ds.len() as int] == x);
}

/// [`lemma_values_size_prefix`] for rules.
proof fn lemma_rules_size_prefix(rs: Seq<Rule>, x: Rule, n: nat)
    requires
        n <= rs.len(),
    ensures
        rules_size(rs.push(x), n) == rules_size(rs, n),
    decreases n,
{
    if n > 0 {
        lemma_rules_size_prefix(rs, x, (n - 1) as nat);
        assert(rs.push(x)[(n - 1) as int] == rs[(n - 1) as int]);
    }
}

/// What a list of rules holds, and one more.
pub proof fn lemma_rules_size_push(rs: Seq<Rule>, x: Rule)
    ensures
        rules_size(rs.push(x), rs.push(x).len()) == rules_size(rs, rs.len()) + rule_size(x),
{
    lemma_rules_size_prefix(rs, x, rs.len());
    assert(rs.push(x)[rs.len() as int] == x);
}

/// What an item of a block holds.
pub open spec fn item_size(item: BlockItem) -> nat {
    match item {
        BlockItem::Rule { rule } => rule_size(rule),
        BlockItem::Declarations { declarations } => declarations_size(
            declarations,
            declarations.len(),
        ),
    }
}

/// One more item of a block, as [`item_size`].
proof fn lemma_items_size_step(items: Seq<BlockItem>, n: nat)
    requires
        1 <= n <= items.len(),
    ensures
        items_size(items, n) == items_size(items, (n - 1) as nat) + item_size(items[(n - 1) as int]),
{
    match items[(n - 1) as int] {
        BlockItem::Rule { rule } => {},
        BlockItem::Declarations { declarations } => {},
    }
}

/// [`lemma_values_size_prefix`] for the items of a block.
proof fn lemma_items_size_prefix(items: Seq<BlockItem>, x: BlockItem, n: nat)
    requires
        n <= items.len(),
    ensures
        items_size(items.push(x), n) == items_size(items, n),
    decreases n,
{
    if n > 0 {
        lemma_items_size_prefix(items, x, (n - 1) as nat);
        assert(items.push(x)[(n - 1) as int] == items[(n - 1) as int]);
    }
}

/// What the items of a block hold, and one more.
pub proof fn lemma_items_size_push(items: Seq<BlockItem>, x: BlockItem)
    ensures
        items_size(items.push(x), items.push(x).len()) == items_size(items, items.len())
            + item_size(x),
{
    lemma_items_size_prefix(items, x, items.len());
    assert(items.push(x)[items.len() as int] == x);
}

/// The first `n` of `items` hold what the rules they become do.
proof fn lemma_child_rules_size(items: Seq<BlockItem>, n: nat)
    requires
        n <= items.len(),
    ensures
        rules_size(child_rules_of(items), n) == items_size(items, n),
    decreases n,
{
    if n > 0 {
        lemma_child_rules_size(items, (n - 1) as nat);
        lemma_items_size_step(items, n);
        match items[(n - 1) as int] {
            BlockItem::Rule { rule } => {
                assert(child_rules_of(items)[(n - 1) as int] == rule);
            },
            BlockItem::Declarations { declarations } => {
                assert(child_rules_of(items)[(n - 1) as int] == Rule::NestedDeclarationsRule {
                    declarations,
                });
                assert(rule_size(Rule::NestedDeclarationsRule { declarations })
                    == declarations_size(declarations, declarations.len()));
            },
        }
    }
}

/// The items of a block hold what the first does, and what the rest do.
proof fn lemma_items_size_split(items: Seq<BlockItem>, n: nat)
    requires
        1 <= n <= items.len(),
    ensures
        items_size(items, n) == item_size(items[0]) + items_size(items.drop_first(), (n - 1) as nat),
    decreases n,
{
    lemma_items_size_step(items, n);
    if n > 1 {
        lemma_items_size_split(items, (n - 1) as nat);
        assert(items.drop_first()[(n - 2) as int] == items[(n - 1) as int]);
        lemma_items_size_step(items.drop_first(), (n - 1) as nat);
    }
}

/// What a qualified rule made of a prelude and a block's items holds.
pub proof fn lemma_qualified_rule_size(prelude: Seq<ComponentValue>, items: Seq<BlockItem>)
    ensures
        rule_size(qualified_rule_from(prelude, items)) == values_size(prelude, prelude.len())
            + items_size(items, items.len()),
{
    if items.len() > 0 && items[0] is Declarations {
        lemma_items_size_split(items, items.len());
        lemma_child_rules_size(items.drop_first(), items.drop_first().len());
    } else {
        lemma_child_rules_size(items, items.len());
        assert(declarations_size(Seq::<Declaration>::empty(), 0) == 0);
    }
}

/// What `with_declarations` holds.
pub proof fn lemma_with_declarations_size(rules: Seq<BlockItem>, decls: Seq<Declaration>)
    ensures
        items_size(with_declarations(rules, decls), with_declarations(rules, decls).len())
            == items_size(rules, rules.len()) + declarations_size(decls, decls.len()),
{
    if decls.len() > 0 {
        lemma_items_size_push(rules, BlockItem::Declarations { declarations: decls });
    } else {
        assert(declarations_size(decls, 0) == 0);
    }
}

// ------------------------------------------------------------------------------------
// Component values and lists of them
// ------------------------------------------------------------------------------------

/// "Consume a component value" from a stream that is not empty holds at most what it took.
pub proof fn lemma_cv_bound(input: TokenStream, index: int)
    requires
        costed(input),
        0 <= index <= input.tokens.len(),
        !is_empty(input, index),
    ensures
        ({
            let (cv, next) = consume_a_component_value(input, index);
            index < next <= input.tokens.len() && value_size(cv) <= cost(input, index, next)
        }),
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    lemma_next_costs(input, index);
    lemma_component_value_advances(input, index);
    super::theorems::lemma_cv_within(input, index);
    if is_open_bracket(item) {
        let associated_token = match item {
            ComponentValue::Token { token } => token,
            _ => Token::Eof,
        };
        lemma_sbl_bound(input, index + 1, mirror(item), associated_token, Seq::empty());
        assert(values_size(Seq::<ComponentValue>::empty(), 0) == 0);
    } else if is_function_token(item) {
        lemma_fl_bound(input, index + 1, token_value(item), Seq::empty());
        assert(values_size(Seq::<ComponentValue>::empty(), 0) == 0);
    }
}

/// The loop of "consume a simple block" holds at most what it took, and one more.
pub proof fn lemma_sbl_bound(
    input: TokenStream,
    index: int,
    ending: Token,
    assoc: Token,
    value: Seq<ComponentValue>,
)
    requires
        costed(input),
        0 <= index <= input.tokens.len(),
    ensures
        ({
            let (cv, end) = simple_block_loop(input, index, ending, assoc, value);
            index <= end <= input.tokens.len() && value_size(cv) <= 1 + values_size(
                value,
                value.len(),
            ) + cost(input, index, end)
        }),
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is(item, ending) {
        lemma_pos_mono(input, index, discard_a_token(input, index));
        if !is_empty(input, index) {
            assert(index < input.tokens.len());
        }
    } else {
        lemma_cv_bound(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_values_size_push(value, cv);
        lemma_sbl_bound(input, next, ending, assoc, value.push(cv));
    }
}

/// The loop of "consume a function" holds at most what it took, and one more.
pub proof fn lemma_fl_bound(
    input: TokenStream,
    index: int,
    name: Seq<u32>,
    value: Seq<ComponentValue>,
)
    requires
        costed(input),
        0 <= index <= input.tokens.len(),
    ensures
        ({
            let (cv, end) = function_loop(input, index, name, value);
            index <= end <= input.tokens.len() && value_size(cv) <= 1 + values_size(
                value,
                value.len(),
            ) + cost(input, index, end)
        }),
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is(item, Token::CloseParen) {
        lemma_pos_mono(input, index, discard_a_token(input, index));
        if !is_empty(input, index) {
            assert(index < input.tokens.len());
        }
    } else {
        lemma_cv_bound(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_values_size_push(value, cv);
        lemma_fl_bound(input, next, name, value.push(cv));
    }
}

/// "Consume a list of component values" holds at most what it took, and what it began with.
pub proof fn lemma_list_bound(
    input: TokenStream,
    index: int,
    stop: Option<Token>,
    nested: bool,
    values: Seq<ComponentValue>,
)
    requires
        costed(input),
        0 <= index <= input.tokens.len(),
    ensures
        ({
            let (list, end) = list_of_component_values_loop(input, index, stop, nested, values);
            index <= end <= input.tokens.len() && values_size(list, list.len()) <= values_size(
                values,
                values.len(),
            ) + cost(input, index, end)
        }),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is_stop(item, stop) {
    } else if is(item, Token::CloseCurly) {
        if !nested {
            lemma_next_costs(input, index);
            let (token, next) = consume_a_token(input, index);
            lemma_values_size_push(values, token);
            lemma_list_bound(input, next, stop, nested, values.push(token));
        }
    } else {
        lemma_cv_bound(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_values_size_push(values, cv);
        lemma_list_bound(input, next, stop, nested, values.push(cv));
    }
}

// ------------------------------------------------------------------------------------
// Declarations
// ------------------------------------------------------------------------------------

/// Taking an item out of a list takes its size out of the list's.
proof fn lemma_values_size_remove(values: Seq<ComponentValue>, k: int, n: nat)
    requires
        0 <= k < values.len(),
        n <= values.len(),
    ensures
        n <= k ==> values_size(values.remove(k), n) == values_size(values, n),
        n > k ==> values_size(values.remove(k), (n - 1) as nat) + value_size(values[k])
            == values_size(values, n),
    decreases n,
{
    if n > 0 {
        lemma_values_size_remove(values, k, (n - 1) as nat);
        let removed = values.remove(k);
        if n <= k {
            assert(removed[(n - 1) as int] == values[(n - 1) as int]);
        } else if n > k + 1 {
            assert(removed[(n - 2) as int] == values[(n - 1) as int]);
        }
    }
}

/// The last non-whitespace item is before `end`, or there is none.
proof fn lemma_last_non_whitespace(value: Seq<ComponentValue>, end: int)
    ensures
        last_non_whitespace(value, end) >= -1,
        end > 0 ==> last_non_whitespace(value, end) < end,
        end <= 0 ==> last_non_whitespace(value, end) == -1,
    decreases end,
{
    if end > 0 && is_whitespace_token(value[end - 1]) {
        lemma_last_non_whitespace(value, end - 1);
    }
}

/// Step 6 of "consume a declaration" does not make the value larger.
proof fn lemma_important_size(list: Seq<ComponentValue>)
    ensures
        ({
            let value = match important_at(list) {
                Some((first, second)) => list.remove(second).remove(first),
                None => list,
            };
            values_size(value, value.len()) <= values_size(list, list.len())
        }),
{
    let len = list.len() as int;
    lemma_last_non_whitespace(list, len);
    let second = last_non_whitespace(list, len);
    lemma_last_non_whitespace(list, second);
    let first = last_non_whitespace(list, second);
    if let Some((f, s)) = important_at(list) {
        assert(f == first && s == second);
        assert(0 <= first < second < len);
        lemma_values_size_remove(list, second, list.len());
        let removed = list.remove(second);
        assert(removed.len() == len - 1);
        lemma_values_size_remove(removed, first, removed.len());
    }
}

/// The items of a list without its last keep their size.
proof fn lemma_values_size_drop_last(values: Seq<ComponentValue>, n: nat)
    requires
        values.len() > 0,
        n <= values.len() - 1,
    ensures
        values_size(values.drop_last(), n) == values_size(values, n),
    decreases n,
{
    if n > 0 {
        lemma_values_size_drop_last(values, (n - 1) as nat);
        assert(values.drop_last()[(n - 1) as int] == values[(n - 1) as int]);
    }
}

/// Step 7 of "consume a declaration" does not make the value larger.
proof fn lemma_trailing_size(value: Seq<ComponentValue>)
    ensures
        values_size(
            without_trailing_whitespace(value),
            without_trailing_whitespace(value).len(),
        ) <= values_size(value, value.len()),
    decreases value.len(),
{
    if value.len() > 0 && is_whitespace_token(value.last()) {
        lemma_trailing_size(value.drop_last());
        lemma_values_size_drop_last(value, (value.len() - 1) as nat);
    }
}

/// The value of a unicode-range descriptor holds at most as many component values as its
/// text has code points.
proof fn lemma_unicode_range_size(text: Seq<u32>)
    ensures
        ({
            let values = consume_the_value_of_a_unicode_range_descriptor(text);
            values_size(values, values.len()) <= text.len()
        }),
{
    let stream = token_stream(text, true);
    lemma_stream_costed(text, true);
    lemma_list_bound(stream, 0, None, false, Seq::empty());
    let end = list_of_component_values_loop(stream, 0, None, false, Seq::empty()).1;
    lemma_pos_in_text(stream, end);
    assert(values_size(Seq::<ComponentValue>::empty(), 0) == 0);
    assert(pos(stream, 0) == 0);
    assert(stream.source->Some_0.text == text);
}

/// The text of some tokens has at most as many code points as the range costs.
proof fn lemma_segment_len(input: TokenStream, start: int, end: int)
    requires
        costed(input),
        0 <= start <= end <= input.tokens.len(),
    ensures
        segment(input, start, end) is Some,
        segment(input, start, end)->Some_0.len() <= cost(input, start, end),
{
    let source = input.source->Some_0;
    if start < end {
        lemma_pos_mono(input, start + 1, end);
        assert(pos(input, start + 1) == source.spans[start].end);
        assert(pos(input, end) == source.spans[end - 1].end);
        assert(0 <= source.spans[start].start <= source.spans[start].end);
        assert(0 <= source.spans[end - 1].start <= source.spans[end - 1].end
            <= source.text.len());
        if start > 0 {
            assert(pos(input, start) == source.spans[start - 1].end);
            assert(source.spans[start - 1].end <= source.spans[start].start);
        }
        assert(source.spans[start].start <= source.spans[end - 1].end);
    }
}

/// Steps 5 to 9 of "consume a declaration" hold at most what they took.
proof fn lemma_declaration_value_bound(
    input: TokenStream,
    start: int,
    nested: bool,
    name: Seq<u32>,
)
    requires
        costed(input),
        0 <= start <= input.tokens.len(),
    ensures
        ({
            let (decl, end) = declaration_value(input, start, nested, name);
            start <= end <= input.tokens.len() && (decl is Some ==> values_size(
                decl->Some_0.value,
                decl->Some_0.value.len(),
            ) <= cost(input, start, end))
        }),
{
    lemma_list_bound(input, start, Some(Token::Semicolon), nested, Seq::empty());
    assert(values_size(Seq::<ComponentValue>::empty(), 0) == 0);
    let (list, end) = consume_a_list_of_component_values(
        input,
        start,
        Some(Token::Semicolon),
        nested,
    );
    lemma_important_size(list);
    let (value0, important) = match important_at(list) {
        Some((first, second)) => (list.remove(second).remove(first), true),
        None => (list, false),
    };
    lemma_trailing_size(value0);
    let value = without_trailing_whitespace(value0);
    lemma_segment_len(input, start, end);
    if !is_custom_property_name_string(name) && !has_curly_block_and_another(value)
        && ascii_case_insensitive_match(name, unicode_range_string()) {
        let text = segment(input, start, end)->Some_0;
        lemma_unicode_range_size(text);
    }
}

// ------------------------------------------------------------------------------------
// The rest of "consume a declaration"
// ------------------------------------------------------------------------------------

/// "Discard whitespace" stays in the stream.
proof fn lemma_whitespace_within(input: TokenStream, index: int)
    requires
        0 <= index <= input.tokens.len(),
    ensures
        index <= discard_whitespace(input, index) <= input.tokens.len(),
    decreases items_left(input, index),
{
    if is(next_token(input, index), Token::Whitespace) {
        assert(index < input.tokens.len());
        lemma_whitespace_within(input, index + 1);
    }
}

/// "Consume the remnants of a bad declaration" stays in the stream.
proof fn lemma_remnants_within(input: TokenStream, index: int, nested: bool)
    requires
        0 <= index <= input.tokens.len(),
    ensures
        index <= consume_the_remnants_of_a_bad_declaration(input, index, nested)
            <= input.tokens.len(),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is(item, Token::Semicolon) {
        if !is_empty(input, index) {
            assert(index < input.tokens.len());
        }
    } else if is(item, Token::CloseCurly) {
        if !nested {
            assert(index < input.tokens.len());
            lemma_remnants_within(input, index + 1, nested);
        }
    } else {
        assert(index < input.tokens.len());
        lemma_component_value_advances(input, index);
        super::theorems::lemma_cv_within(input, index);
        let (_, next) = consume_a_component_value(input, index);
        lemma_remnants_within(input, next, nested);
    }
}

/// "Consume a declaration" holds at most what it took.
pub proof fn lemma_declaration_bound(input: TokenStream, index: int, nested: bool)
    requires
        costed(input),
        0 <= index <= input.tokens.len(),
    ensures
        ({
            let (decl, end) = consume_a_declaration(input, index, nested);
            index <= end <= input.tokens.len() && (decl is Some ==> values_size(
                decl->Some_0.value,
                decl->Some_0.value.len(),
            ) <= cost(input, index, end))
        }),
{
    lemma_remnants_within(input, index, nested);
    if is_ident(next_token(input, index)) {
        assert(index < input.tokens.len());
        let after_name = index + 1;
        let after_whitespace = discard_whitespace(input, after_name);
        lemma_whitespace_within(input, after_name);
        lemma_remnants_within(input, after_whitespace, nested);
        if is(next_token(input, after_whitespace), Token::Colon) {
            assert(after_whitespace < input.tokens.len());
            let after_colon = discard_a_token(input, after_whitespace);
            let start = discard_whitespace(input, after_colon);
            lemma_whitespace_within(input, after_colon);
            lemma_declaration_value_bound(input, start, nested, token_value(next_token(input, index)));
            lemma_pos_mono(input, index, start);
        }
    }
}

} // verus!
