//! Why [`super::spec::moved`] gives back the index it was given: every loop of the spec
//! that goes on after a call has gone forward. The spec's modelling choices rest on this.
//!
//! Each lemma states how far one algorithm of the spec goes, which covers the `moved` of
//! every algorithm's own loop. The `theorem_` ones cover the call sites in the three loops
//! that no lemma here walks.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Discard whitespace" never goes back.
pub proof fn lemma_whitespace_forward(input: TokenStream, index: int)
    ensures
        discard_whitespace(input, index) >= index,
    decreases items_left(input, index),
{
    if is(next_token(input, index), Token::Whitespace) {
        lemma_whitespace_forward(input, discard_a_token(input, index));
    }
}

/// "Consume a component value" takes something from a stream that is not empty.
pub proof fn lemma_component_value_advances(input: TokenStream, index: int)
    requires
        !is_empty(input, index),
    ensures
        consume_a_component_value(input, index).1 > index,
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    if is_open_bracket(item) {
        let associated_token = match item {
            ComponentValue::Token { token } => token,
            _ => Token::Eof,
        };
        lemma_simple_block_forward(
            input,
            index + 1,
            mirror(item),
            associated_token,
            Seq::empty(),
        );
    } else if is_function_token(item) {
        lemma_function_forward(input, index + 1, token_value(item), Seq::empty());
    }
}

/// The loop of "consume a simple block" never goes back.
pub proof fn lemma_simple_block_forward(
    input: TokenStream,
    index: int,
    ending_token: Token,
    associated_token: Token,
    value: Seq<ComponentValue>,
)
    ensures
        simple_block_loop(input, index, ending_token, associated_token, value).1 >= index,
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, ending_token)) {
        lemma_component_value_advances(input, index);
        let (component_value, next) = consume_a_component_value(input, index);
        lemma_simple_block_forward(
            input,
            moved(index, next),
            ending_token,
            associated_token,
            value.push(component_value),
        );
    }
}

/// The loop of "consume a function" never goes back.
pub proof fn lemma_function_forward(
    input: TokenStream,
    index: int,
    name: Seq<u32>,
    value: Seq<ComponentValue>,
)
    ensures
        function_loop(input, index, name, value).1 >= index,
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    if !(is(item, Token::Eof) || is(item, Token::CloseParen)) {
        lemma_component_value_advances(input, index);
        let (component_value, next) = consume_a_component_value(input, index);
        lemma_function_forward(input, moved(index, next), name, value.push(component_value));
    }
}

/// "Consume a list of component values" never goes back.
pub proof fn lemma_list_forward(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
    values: Seq<ComponentValue>,
)
    ensures
        list_of_component_values_loop(input, index, stop_token, nested, values).1 >= index,
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is_stop(item, stop_token) {
    } else if is(item, Token::CloseCurly) {
        if !nested {
            let (token, next) = consume_a_token(input, index);
            lemma_list_forward(input, next, stop_token, nested, values.push(token));
        }
    } else {
        lemma_component_value_advances(input, index);
        let (value, next) = consume_a_component_value(input, index);
        lemma_list_forward(input, moved(index, next), stop_token, nested, values.push(value));
    }
}

/// "Consume the remnants of a bad declaration" never goes back, and goes forward from
/// anything but EOF and a `}` it stops at.
pub proof fn lemma_remnants_forward(input: TokenStream, index: int, nested: bool)
    ensures
        consume_the_remnants_of_a_bad_declaration(input, index, nested) >= index,
        !is_empty(input, index) && !(nested && is(next_token(input, index), Token::CloseCurly))
            ==> consume_the_remnants_of_a_bad_declaration(input, index, nested) > index,
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is(item, Token::Semicolon) {
    } else if is(item, Token::CloseCurly) {
        if !nested {
            lemma_remnants_forward(input, discard_a_token(input, index), nested);
        }
    } else {
        lemma_component_value_advances(input, index);
        let (_, next) = consume_a_component_value(input, index);
        lemma_remnants_forward(input, moved(index, next), nested);
    }
}

/// "Consume a declaration" never goes back, goes forward from anything but EOF and a `}` it
/// stops at, and has gone forward if it returns a declaration.
pub proof fn lemma_declaration_forward(input: TokenStream, index: int, nested: bool)
    ensures
        consume_a_declaration(input, index, nested).1 >= index,
        !is_empty(input, index) && !(nested && is(next_token(input, index), Token::CloseCurly))
            ==> consume_a_declaration(input, index, nested).1 > index,
{
    lemma_remnants_forward(input, index, nested);
    if is_ident(next_token(input, index)) {
        let (token, after_name) = consume_a_token(input, index);
        let after_whitespace = discard_whitespace(input, after_name);
        lemma_whitespace_forward(input, after_name);
        lemma_remnants_forward(input, after_whitespace, nested);
        if is(next_token(input, after_whitespace), Token::Colon) {
            let after_colon = discard_a_token(input, after_whitespace);
            let start = discard_whitespace(input, after_colon);
            lemma_whitespace_forward(input, after_colon);
            lemma_list_forward(input, start, Some(Token::Semicolon), nested, Seq::empty());
        }
    }
}

/// "Consume an at-rule" takes at least its at-keyword.
pub proof fn lemma_at_rule_advances(input: TokenStream, index: int, nested: bool)
    requires
        is_at_keyword(next_token(input, index)),
    ensures
        consume_an_at_rule(input, index, nested).1 > index,
    decreases items_left(input, index), 2nat,
{
    let (token, next) = consume_a_token(input, index);
    lemma_at_rule_forward(input, next, nested, token_value(token), Seq::empty());
}

/// The loop of "consume an at-rule" never goes back.
pub proof fn lemma_at_rule_forward(
    input: TokenStream,
    index: int,
    nested: bool,
    name: Seq<u32>,
    prelude: Seq<ComponentValue>,
)
    ensures
        at_rule_loop(input, index, nested, name, prelude).1 >= index,
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    if is(item, Token::Semicolon) || is(item, Token::Eof) {
    } else if is(item, Token::CloseCurly) {
        if !nested {
            let (token, next) = consume_a_token(input, index);
            lemma_at_rule_forward(input, next, nested, name, prelude.push(token));
        }
    } else if is(item, Token::OpenCurly) {
        lemma_block_advances(input, index);
    } else {
        lemma_component_value_advances(input, index);
        let (value, next) = consume_a_component_value(input, index);
        lemma_at_rule_forward(input, moved(index, next), nested, name, prelude.push(value));
    }
}

/// "Consume a qualified rule" never goes back, and goes forward from anything that does
/// not stop it at once.
pub proof fn lemma_qualified_rule_forward(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
    prelude: Seq<ComponentValue>,
)
    ensures
        qualified_rule_loop(input, index, stop_token, nested, prelude).1 >= index,
        !is_empty(input, index) && !is_stop(next_token(input, index), stop_token) && !(nested
            && is(next_token(input, index), Token::CloseCurly)) ==> qualified_rule_loop(
            input,
            index,
            stop_token,
            nested,
            prelude,
        ).1 > index,
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    if is(item, Token::Eof) || is_stop(item, stop_token) {
    } else if is(item, Token::CloseCurly) {
        if !nested {
            let (token, next) = consume_a_token(input, index);
            lemma_qualified_rule_forward(input, next, stop_token, nested, prelude.push(token));
        }
    } else if is(item, Token::OpenCurly) {
        lemma_block_advances(input, index);
        lemma_remnants_forward(input, index, true);
    } else {
        lemma_component_value_advances(input, index);
        let (value, next) = consume_a_component_value(input, index);
        lemma_qualified_rule_forward(
            input,
            moved(index, next),
            stop_token,
            nested,
            prelude.push(value),
        );
    }
}

/// "Consume a block" takes at least its `{`.
pub proof fn lemma_block_advances(input: TokenStream, index: int)
    requires
        is(next_token(input, index), Token::OpenCurly),
    ensures
        consume_a_block(input, index).1 > index,
    decreases items_left(input, index), 0nat,
{
    lemma_contents_forward(input, index + 1, Seq::empty(), Seq::empty());
    let (_, next) = consume_a_blocks_contents(input, index + 1);
    assert(discard_a_token(input, next) >= next);
}

/// The loop of "consume a block's contents" never goes back.
pub proof fn lemma_contents_forward(
    input: TokenStream,
    index: int,
    rules: Seq<BlockItem>,
    decls: Seq<Declaration>,
)
    ensures
        blocks_contents_loop(input, index, rules, decls).1 >= index,
    decreases items_left(input, index), 3nat,
{
    let item = next_token(input, index);
    if is(item, Token::Whitespace) || is(item, Token::Semicolon) {
        lemma_contents_forward(input, discard_a_token(input, index), rules, decls);
    } else if is(item, Token::Eof) || is(item, Token::CloseCurly) {
    } else if is_at_keyword(item) {
        let flushed = with_declarations(rules, decls);
        lemma_at_rule_advances(input, index, true);
        let (rule, next) = consume_an_at_rule(input, index, true);
        match rule {
            Some(rule) => lemma_contents_forward(
                input,
                moved(index, next),
                flushed.push(BlockItem::Rule { rule }),
                Seq::empty(),
            ),
            None => lemma_contents_forward(input, moved(index, next), flushed, Seq::empty()),
        }
    } else {
        lemma_declaration_forward(input, index, true);
        let (declaration, next) = consume_a_declaration(input, index, true);
        match declaration {
            Some(decl) => lemma_contents_forward(
                input,
                moved(index, next),
                rules,
                decls.push(decl),
            ),
            None => {
                lemma_qualified_rule_forward(
                    input,
                    index,
                    Some(Token::Semicolon),
                    true,
                    Seq::empty(),
                );
                let (result, after_rule) = consume_a_qualified_rule(
                    input,
                    index,
                    Some(Token::Semicolon),
                    true,
                );
                match result {
                    QualifiedRuleResult::Nothing => lemma_contents_forward(
                        input,
                        moved(index, after_rule),
                        rules,
                        decls,
                    ),
                    QualifiedRuleResult::InvalidRuleError => lemma_contents_forward(
                        input,
                        moved(index, after_rule),
                        with_declarations(rules, decls),
                        Seq::empty(),
                    ),
                    QualifiedRuleResult::Rule { rule } => lemma_contents_forward(
                        input,
                        moved(index, after_rule),
                        with_declarations(rules, decls).push(BlockItem::Rule { rule }),
                        Seq::empty(),
                    ),
                }
            },
        }
    }
}

/// The call sites in "consume a stylesheet's contents": it goes forward from anything that
/// reaches them.
pub proof fn theorem_stylesheet_moves(input: TokenStream, index: int)
    requires
        !is_empty(input, index),
    ensures
        is_at_keyword(next_token(input, index)) ==> consume_an_at_rule(input, index, false).1
            > index,
        !is_at_keyword(next_token(input, index)) ==> consume_a_qualified_rule(
            input,
            index,
            None,
            false,
        ).1 > index,
{
    if is_at_keyword(next_token(input, index)) {
        lemma_at_rule_advances(input, index, false);
    } else {
        lemma_qualified_rule_forward(input, index, None, false, Seq::empty());
    }
}

/// The call sites in "parse a list of declarations".
pub proof fn theorem_declarations_move(input: TokenStream, index: int)
    requires
        !is_empty(input, index),
    ensures
        ({
            let start = discard_whitespace(input, index);
            let item = next_token(input, start);
            &&& is(item, Token::Semicolon) ==> discard_a_token(input, start) > index
            &&& is_at_keyword(item) ==> consume_an_at_rule(input, start, false).1 > index
            &&& !(is(item, Token::Semicolon) || is_at_keyword(item)) ==> consume_a_declaration(
                input,
                start,
                false,
            ).1 > index
        }),
{
    let start = discard_whitespace(input, index);
    lemma_whitespace_forward(input, index);
    lemma_declaration_forward(input, start, false);
    if is_at_keyword(next_token(input, start)) {
        lemma_at_rule_advances(input, start, false);
    }
}

/// The call site in "parse a comma-separated list of component values".
pub proof fn theorem_comma_list_moves(input: TokenStream, index: int)
    requires
        !is_empty(input, index),
    ensures
        discard_a_token(
            input,
            consume_a_list_of_component_values(input, index, Some(Token::Comma), false).1,
        ) > index,
{
    let stop = Some(Token::Comma);
    let item = next_token(input, index);
    lemma_list_forward(input, index, stop, false, Seq::empty());
    if !is_stop(item, stop) {
        if is(item, Token::CloseCurly) {
            let (token, next) = consume_a_token(input, index);
            lemma_list_forward(input, next, stop, false, seq![token]);
            assert(Seq::<ComponentValue>::empty().push(token) =~= seq![token]);
        } else {
            lemma_component_value_advances(input, index);
            let (value, next) = consume_a_component_value(input, index);
            lemma_list_forward(input, moved(index, next), stop, false, seq![value]);
            assert(Seq::<ComponentValue>::empty().push(value) =~= seq![value]);
        }
    }
}

} // verus!
