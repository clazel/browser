//! Why "consume a block" and "consume a simple block" end at the same index
//! ([`super::contract::block_ends_agree`]), proven in [`super::theorems`] from these.
//!
//! [`stop_of`] is where a loop that takes component values until a `}` or the end stops.
//! The loop of "consume a simple block" for `{` is exactly that; the loop of "consume a
//! block's contents" takes at-rules, declarations and qualified rules instead, and each of
//! them is shown to end where the loop of component values from the same index would, so
//! the two loops stop at the same index. Everything is stated of an arbitrary token
//! stream, whatever its items.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::termination::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Where a loop of "consume a component value" from `index` stops: at the `}` or the end
/// it reaches.
pub open spec fn stop_of(input: TokenStream, index: int) -> int
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is(item, Token::CloseCurly) {
        index
    } else {
        let (_, next) = consume_a_component_value(input, index);
        stop_of(input, moved(index, next))
    }
}

/// An item that "consume a component value" takes as one token: a token that opens
/// nothing.
pub open spec fn plain_item(item: ComponentValue) -> bool {
    item is Token && !is_open_bracket(item) && !is_function_token(item)
}

/// The loops of this crate step over a component value that is not `}` or the end: a loop
/// that goes on from there stops where [`stop_of`] does.
proof fn lemma_stop_cv(input: TokenStream, index: int)
    requires
        !is_empty(input, index),
        !(is(next_token(input, index), Token::CloseCurly)),
    ensures
        consume_a_component_value(input, index).1 > index,
        stop_of(input, index) == stop_of(input, consume_a_component_value(input, index).1),
{
    lemma_component_value_advances(input, index);
}

/// A token that opens nothing is one step.
proof fn lemma_stop_plain(input: TokenStream, index: int)
    requires
        !is_empty(input, index),
        !(is(next_token(input, index), Token::CloseCurly)),
        plain_item(next_token(input, index)),
    ensures
        stop_of(input, index) == stop_of(input, index + 1),
{
    lemma_stop_cv(input, index);
    assert(consume_a_component_value(input, index) == (next_token(input, index), index + 1));
}

/// Skipping whitespace does not change where the loop stops.
proof fn lemma_stop_whitespace(input: TokenStream, index: int)
    ensures
        stop_of(input, discard_whitespace(input, index)) == stop_of(input, index),
    decreases items_left(input, index),
{
    if is(next_token(input, index), Token::Whitespace) {
        assert(plain_item(next_token(input, index)));
        lemma_stop_plain(input, index);
        lemma_stop_whitespace(input, index + 1);
    }
}

/// The loop of "consume a simple block" for a `{` stops one past [`stop_of`], and a `}`
/// or the end are what it stops at.
proof fn lemma_simple_block_loop_end(
    input: TokenStream,
    index: int,
    associated_token: Token,
    value: Seq<ComponentValue>,
)
    ensures
        simple_block_loop(input, index, Token::CloseCurly, associated_token, value).1
            == discard_a_token(input, stop_of(input, index)),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, Token::CloseCurly)) {
        lemma_stop_cv(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_simple_block_loop_end(input, next, associated_token, value.push(cv));
    }
}

/// "Consume the remnants of a bad declaration", nested, ends where the loop of component
/// values would.
proof fn lemma_remnants_stop(input: TokenStream, index: int)
    ensures
        stop_of(input, consume_the_remnants_of_a_bad_declaration(input, index, true)) == stop_of(
            input,
            index,
        ),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) {
    } else if is(item, Token::Semicolon) {
        assert(plain_item(item));
        lemma_stop_plain(input, index);
    } else if is(item, Token::CloseCurly) {
    } else {
        lemma_stop_cv(input, index);
        let (_, next) = consume_a_component_value(input, index);
        lemma_remnants_stop(input, next);
    }
}

/// "Consume a list of component values", nested, with `;` as the stop token, ends where the
/// loop of component values would.
proof fn lemma_list_stop(input: TokenStream, index: int, values: Seq<ComponentValue>)
    ensures
        stop_of(
            input,
            list_of_component_values_loop(input, index, Some(Token::Semicolon), true, values).1,
        ) == stop_of(input, index),
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, Token::Semicolon) || is(item, Token::CloseCurly)) {
        lemma_stop_cv(input, index);
        let (cv, next) = consume_a_component_value(input, index);
        lemma_list_stop(input, next, values.push(cv));
    }
}

/// "Consume a declaration", nested, ends where the loop of component values would.
proof fn lemma_declaration_stop(input: TokenStream, index: int)
    ensures
        stop_of(input, consume_a_declaration(input, index, true).1) == stop_of(input, index),
{
    lemma_remnants_stop(input, index);
    if is_ident(next_token(input, index)) {
        assert(plain_item(next_token(input, index)));
        lemma_stop_plain(input, index);
        let after_name = index + 1;
        let after_whitespace = discard_whitespace(input, after_name);
        lemma_stop_whitespace(input, after_name);
        lemma_remnants_stop(input, after_whitespace);
        if is(next_token(input, after_whitespace), Token::Colon) {
            let after_colon = discard_a_token(input, after_whitespace);
            assert(plain_item(next_token(input, after_whitespace)));
            lemma_stop_plain(input, after_whitespace);
            let start = discard_whitespace(input, after_colon);
            lemma_stop_whitespace(input, after_colon);
            lemma_list_stop(input, start, Seq::empty());
        }
    }
}

/// The loop of "consume an at-rule", nested, ends where the loop of component values would,
/// if "consume a block" ends where "consume a simple block" does for every `{` from
/// `index` on.
proof fn lemma_at_rule_loop_stop(
    input: TokenStream,
    index: int,
    name: Seq<u32>,
    prelude: Seq<ComponentValue>,
)
    ensures
        stop_of(input, at_rule_loop(input, index, true, name, prelude).1) == stop_of(input, index),
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    if is(item, Token::Semicolon) {
        assert(plain_item(item));
        lemma_stop_plain(input, index);
    } else if is(item, Token::Eof) || is(item, Token::CloseCurly) {
    } else if is(item, Token::OpenCurly) {
        lemma_block_agrees(input, index);
        lemma_stop_cv(input, index);
    } else {
        lemma_stop_cv(input, index);
        let (value, next) = consume_a_component_value(input, index);
        lemma_at_rule_loop_stop(input, next, name, prelude.push(value));
    }
}

/// The loop of "consume a qualified rule", nested, with `;` as the stop token, ends where
/// the loop of component values would.
proof fn lemma_qualified_rule_loop_stop(
    input: TokenStream,
    index: int,
    prelude: Seq<ComponentValue>,
)
    ensures
        stop_of(
            input,
            qualified_rule_loop(input, index, Some(Token::Semicolon), true, prelude).1,
        ) == stop_of(input, index),
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is(item, Token::Semicolon) || is(item, Token::CloseCurly) {
    } else if is(item, Token::OpenCurly) {
        lemma_block_agrees(input, index);
        lemma_stop_cv(input, index);
        lemma_remnants_stop(input, index);
    } else {
        lemma_stop_cv(input, index);
        let (value, next) = consume_a_component_value(input, index);
        lemma_qualified_rule_loop_stop(input, next, prelude.push(value));
    }
}

/// The loop of "consume a block's contents" stops where the loop of component values does.
proof fn lemma_contents_stop(
    input: TokenStream,
    index: int,
    rules: Seq<BlockItem>,
    decls: Seq<Declaration>,
)
    ensures
        blocks_contents_loop(input, index, rules, decls).1 == stop_of(input, index),
    decreases items_left(input, index), 3nat,
{
    let item = next_token(input, index);
    if is(item, Token::Whitespace) || is(item, Token::Semicolon) {
        assert(plain_item(item));
        lemma_stop_plain(input, index);
        lemma_contents_stop(input, index + 1, rules, decls);
    } else if is(item, Token::Eof) || is(item, Token::CloseCurly) {
    } else if is_at_keyword(item) {
        let flushed = with_declarations(rules, decls);
        assert(plain_item(item));
        lemma_stop_plain(input, index);
        lemma_at_rule_advances(input, index, true);
        let (rule, next) = consume_an_at_rule(input, index, true);
        lemma_at_rule_loop_stop(input, index + 1, token_value(item), Seq::empty());
        match rule {
            Some(rule) => lemma_contents_stop(
                input,
                next,
                flushed.push(BlockItem::Rule { rule }),
                Seq::empty(),
            ),
            None => lemma_contents_stop(input, next, flushed, Seq::empty()),
        }
    } else {
        lemma_declaration_forward(input, index, true);
        lemma_declaration_stop(input, index);
        let (declaration, next) = consume_a_declaration(input, index, true);
        match declaration {
            Some(decl) => lemma_contents_stop(input, next, rules, decls.push(decl)),
            None => {
                lemma_qualified_rule_forward(
                    input,
                    index,
                    Some(Token::Semicolon),
                    true,
                    Seq::empty(),
                );
                lemma_qualified_rule_loop_stop(input, index, Seq::empty());
                let (result, after_rule) = consume_a_qualified_rule(
                    input,
                    index,
                    Some(Token::Semicolon),
                    true,
                );
                match result {
                    QualifiedRuleResult::Nothing => lemma_contents_stop(
                        input,
                        after_rule,
                        rules,
                        decls,
                    ),
                    QualifiedRuleResult::InvalidRuleError => lemma_contents_stop(
                        input,
                        after_rule,
                        with_declarations(rules, decls),
                        Seq::empty(),
                    ),
                    QualifiedRuleResult::Rule { rule } => lemma_contents_stop(
                        input,
                        after_rule,
                        with_declarations(rules, decls).push(BlockItem::Rule { rule }),
                        Seq::empty(),
                    ),
                }
            },
        }
    }
}

/// [`super::contract::block_ends_agree`], by induction on the items left.
pub proof fn lemma_block_agrees(input: TokenStream, index: int)
    requires
        is(next_token(input, index), Token::OpenCurly),
    ensures
        consume_a_block(input, index).1 == consume_a_simple_block(input, index).1,
    decreases items_left(input, index), 0nat,
{
    assert(index + 1 == discard_a_token(input, index));
    lemma_contents_stop(input, index + 1, Seq::empty(), Seq::empty());
    lemma_simple_block_loop_end(input, index + 1, Token::OpenCurly, Seq::empty());
}

} // verus!
