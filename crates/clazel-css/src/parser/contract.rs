//! Contracts the executable parser is proven to meet, and the statements of the theorems
//! planned about the spec. Each entry point's `ensures` clause is one of these predicates,
//! so reading these and [`super::spec`] is enough to know what the implementation
//! guarantees.
//!
//! phase-5.md, under 5.3, says how the exec functions read tokens and what they cost, and
//! [`super::rows`] says what they build.
//!
//! Each statement below is a `spec fn`, because a `proof fn` with no proof is not allowed.
//! [`super::lemmas`] proves the ones that say so; the others are not proven.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Contracts of the exec parser
// ------------------------------------------------------------------------------------

/// The longest input the parser takes, 8 times `MAX_BODY`, 64 MiB. Positions and places in
/// the output arrays are `u32`, and a rule costs a few entries for each token it takes.
pub const MAX_PARSER_INPUT: usize = 0x2000_0000;

/// What the exec functions need of the input.
pub open spec fn parser_input_requires(input: Seq<u32>) -> bool {
    input.len() <= MAX_PARSER_INPUT
}

/// True if `pos` is where reading gives token `index` of `text`'s stream.
pub open spec fn at_index(text: Seq<u32>, flag: bool, index: int, pos: int) -> bool {
    let stream = token_stream(text, flag);
    0 <= index < stream.tokens.len() && pos == position_of(stream.source.unwrap(), index)
}

/// Contract for `parse_stylesheet(input, location)`.
pub open spec fn parse_stylesheet_ensures(
    input: Seq<u32>,
    location: Option<Seq<u32>>,
    sheet: Stylesheet,
) -> bool {
    sheet == parse_a_stylesheet(Input::String { string: input }, location)
}

/// Contract for `parse_stylesheet_contents(input)`.
pub open spec fn parse_stylesheet_contents_ensures(input: Seq<u32>, rules: Seq<Rule>) -> bool {
    rules == parse_a_stylesheets_contents(Input::String { string: input })
}

/// Contract for `parse_declaration_list(input)`.
pub open spec fn parse_declaration_list_ensures(
    input: Seq<u32>,
    declarations: Seq<Declaration>,
) -> bool {
    declarations == parse_a_list_of_declarations(Input::String { string: input })
}

/// Contract for `parse_rule(input)`.
pub open spec fn parse_rule_ensures(input: Seq<u32>, rule: Option<Rule>) -> bool {
    rule == parse_a_rule(Input::String { string: input })
}

/// Contract for `parse_declaration(input)`.
pub open spec fn parse_declaration_ensures(input: Seq<u32>, decl: Option<Declaration>) -> bool {
    decl == parse_a_declaration(Input::String { string: input })
}

/// Contract for `parse_component_value(input)`.
pub open spec fn parse_component_value_ensures(
    input: Seq<u32>,
    value: Option<ComponentValue>,
) -> bool {
    value == parse_a_component_value(Input::String { string: input })
}

/// Contract for `parse_component_values(input)`.
pub open spec fn parse_component_values_ensures(
    input: Seq<u32>,
    values: Seq<ComponentValue>,
) -> bool {
    values == parse_a_list_of_component_values(Input::String { string: input })
}

/// Contract for `parse_comma_separated_component_values(input)`.
pub open spec fn parse_comma_separated_ensures(
    input: Seq<u32>,
    groups: Seq<Seq<ComponentValue>>,
) -> bool {
    groups == parse_a_comma_separated_list_of_component_values(Input::String { string: input })
}

/// Contract for `a_n_plus_b(values)`.
pub open spec fn a_n_plus_b_ensures(
    values: Seq<ComponentValue>,
    result: Option<(int, int)>,
) -> bool {
    result == a_n_plus_b(values)
}

/// Contract for `serialize_a_n_plus_b(a, b)`.
pub open spec fn serialize_a_n_plus_b_ensures(a: int, b: int, output: Seq<u32>) -> bool {
    output == serialize_a_n_plus_b(a, b)
}

/// The position lockstep reading is at when `index` tokens have been read: the end of the
/// last one. The exec parser keeps this in place of `index`.
pub open spec fn position_of(source: SourceText, index: int) -> int {
    if index <= 0 {
        0
    } else {
        source.spans[index - 1].end
    }
}

/// The invariant of the exec parser's reader: reading at [`position_of`] gives the stream's
/// next token. So the parser needs no token list: "mark" is keeping a position, and "next
/// token" is a call of the tokenizer's `next_token`.
pub open spec fn reader_matches(
    string: Seq<u32>,
    unicode_ranges_allowed: bool,
    index: int,
) -> bool {
    let stream = token_stream(string, unicode_ranges_allowed);
    let source = stream.source.unwrap();
    0 <= index < stream.tokens.len() ==> {
        let (token, next) = read_a_token(
            string,
            position_of(source, index),
            unicode_ranges_allowed,
        );
        stream.tokens[index] == (ComponentValue::Token { token }) && next
            == source.spans[index].end
    }
}

// ------------------------------------------------------------------------------------
// Sizes, for the statements below
// ------------------------------------------------------------------------------------

/// How many component values `value` holds, itself and those inside it.
pub open spec fn value_size(value: ComponentValue) -> nat
    decreases value, 0nat,
{
    match value {
        ComponentValue::Token { .. } => 1,
        ComponentValue::Function { value, .. } => 1 + values_size(value, value.len()),
        ComponentValue::SimpleBlock { value, .. } => 1 + values_size(value, value.len()),
    }
}

/// How many component values the first `n` items of `values` hold.
pub open spec fn values_size(values: Seq<ComponentValue>, n: nat) -> nat
    decreases values, n,
{
    if n == 0 || n > values.len() {
        0
    } else {
        values_size(values, (n - 1) as nat) + value_size(values[n - 1])
    }
}

/// How many component values the first `n` of `declarations` hold.
pub open spec fn declarations_size(declarations: Seq<Declaration>, n: nat) -> nat
    decreases n,
{
    if n == 0 || n > declarations.len() {
        0
    } else {
        declarations_size(declarations, (n - 1) as nat) + values_size(
            declarations[n - 1].value,
            declarations[n - 1].value.len(),
        )
    }
}

/// How many component values `rule` holds.
pub open spec fn rule_size(rule: Rule) -> nat
    decreases rule, 0nat,
{
    match rule {
        Rule::AtRule { prelude, child_rules, .. } => values_size(prelude, prelude.len()) + match
            child_rules {
            Some(items) => items_size(items, items.len()),
            None => 0,
        },
        Rule::QualifiedRule { prelude, declarations, child_rules } => values_size(
            prelude,
            prelude.len(),
        ) + declarations_size(declarations, declarations.len()) + rules_size(
            child_rules,
            child_rules.len(),
        ),
        Rule::NestedDeclarationsRule { declarations } => declarations_size(
            declarations,
            declarations.len(),
        ),
    }
}

/// How many component values the first `n` of `rules` hold.
pub open spec fn rules_size(rules: Seq<Rule>, n: nat) -> nat
    decreases rules, n,
{
    if n == 0 || n > rules.len() {
        0
    } else {
        rules_size(rules, (n - 1) as nat) + rule_size(rules[n - 1])
    }
}

/// How many component values the first `n` of `items` hold.
pub open spec fn items_size(items: Seq<BlockItem>, n: nat) -> nat
    decreases items, n,
{
    if n == 0 || n > items.len() {
        0
    } else {
        items_size(items, (n - 1) as nat) + match items[n - 1] {
            BlockItem::Rule { rule } => rule_size(rule),
            BlockItem::Declarations { declarations } => declarations_size(
                declarations,
                declarations.len(),
            ),
        }
    }
}

// ------------------------------------------------------------------------------------
// Statements of the planned theorems
// ------------------------------------------------------------------------------------

/// `theorem_parse_total`: the text's notes, "always consumes the entire stream". That every
/// function here returns is what Verus's `decreases` already checked. Proven in
/// [`super::lemmas`].
pub open spec fn parse_total(input: TokenStream, index: int) -> bool {
    is_empty(input, consume_a_stylesheets_contents(input, index).1) && is_empty(
        input,
        consume_a_list_of_component_values(input, index, None, false).1,
    )
}

/// `theorem_blocks_balanced`: a simple block ends on its opening token's mirror or at EOF.
/// Proven in [`super::lemmas`].
pub open spec fn blocks_balanced(input: TokenStream, index: int) -> bool {
    is_open_bracket(next_token(input, index)) ==> {
        let end = consume_a_simple_block(input, index).1;
        is_empty(input, end) || (1 <= end <= input.tokens.len() && is(
            input.tokens[end - 1],
            mirror(next_token(input, index)),
        ))
    }
}

/// `theorem_parse_bounded`: the output's component values number at most the code points of
/// the input and one, so everything that walks the output is linear in the sheet. The plan
/// counted tokens; a unicode-range value is tokenized a second time, into other tokens,
/// so what bounds both is the code points. Not proven.
pub open spec fn parse_bounded(string: Seq<u32>) -> bool {
    let rules = parse_a_stylesheet(Input::String { string }, None).rules;
    rules_size(rules, rules.len()) <= filter_code_points(string).len() + 1
}

/// `theorem_block_ends_agree`: "consume a block" and "consume a simple block" end at the
/// same index, whatever the block holds, since everything inside a block's contents stops
/// before an unmatched `}`. The exec parser's table of closing positions rests on this:
/// it lets a declaration that is about to fail step over a block without reading it. Not
/// proven.
pub open spec fn block_ends_agree(input: TokenStream, index: int) -> bool {
    is(next_token(input, index), Token::OpenCurly) ==> consume_a_block(input, index).1
        == consume_a_simple_block(input, index).1
}

/// True if `value` holds no token that the text says never reaches an output: a
/// `<function-token>`, `<{-token>`, `<(-token>` or `<[-token>`.
pub open spec fn preserved_only(value: ComponentValue) -> bool
    decreases value, 0nat,
{
    match value {
        ComponentValue::Token { token } => !(token is Function || token is OpenCurly
            || token is OpenParen || token is OpenSquare),
        ComponentValue::Function { value, .. } => all_preserved(value, value.len()),
        ComponentValue::SimpleBlock { value, .. } => all_preserved(value, value.len()),
    }
}

/// [`preserved_only`] for the first `n` of `values`.
pub open spec fn all_preserved(values: Seq<ComponentValue>, n: nat) -> bool
    decreases values, n,
{
    n == 0 || n > values.len() || (all_preserved(values, (n - 1) as nat) && preserved_only(
        values[n - 1],
    ))
}

/// `theorem_output_preserved`: §5.2's note, "never appear in any parser output". Not
/// proven.
pub open spec fn output_preserved(string: Seq<u32>) -> bool {
    let values = parse_a_list_of_component_values(Input::String { string });
    all_preserved(values, values.len())
}

/// `theorem_reader`: [`reader_matches`] at every index. Proven in [`super::lemmas`].
pub open spec fn reader_is_the_stream(string: Seq<u32>, unicode_ranges_allowed: bool) -> bool {
    forall|index: int| #[trigger] reader_matches(string, unicode_ranges_allowed, index)
}

/// `theorem_spans_in_order`: a stream made from a string has one span per token, in order
/// and inside the string, so [`segment`]'s `subrange` is always of a real range. Not proven:
/// the tokenizer's exec `next_token` proves `next <= input.len()`, but no lemma states it of
/// the spec yet.
pub open spec fn spans_in_order(string: Seq<u32>, unicode_ranges_allowed: bool) -> bool {
    let stream = token_stream(string, unicode_ranges_allowed);
    let spans = stream.source.unwrap().spans;
    spans.len() == stream.tokens.len() && forall|i: int|
        0 <= i < spans.len() ==> 0 <= #[trigger] spans[i].start <= spans[i].end <= string.len()
            && (i + 1 < spans.len() ==> spans[i].end <= spans[i + 1].start)
}

/// `theorem_value_end`: what [`declaration_value`] relies on for `value_end`. If the items
/// of `list` from `kept` on are all tokens, each is one item of the stream, so the items
/// before `kept` end `list.len() - kept` before `end`. Not proven.
pub open spec fn value_end_is_exact(
    input: TokenStream,
    start: int,
    nested: bool,
    kept: int,
) -> bool {
    let (list, end) = consume_a_list_of_component_values(
        input,
        start,
        Some(Token::Semicolon),
        nested,
    );
    (0 <= kept <= list.len() && forall|k: int|
        kept <= k < list.len() ==> #[trigger] list[k] is Token) ==> list.subrange(
        kept,
        list.len() as int,
    ) == input.tokens.subrange(end - (list.len() - kept), end)
}

/// §9: "parsing the stylesheet must produce the same data structures as parsing,
/// serializing, and parsing again, except for consecutive <whitespace-token>s, which may be
/// collapsed into a single token". The text defines no serializer, so this is what one
/// `serialize` must satisfy, with [`needs_comment_between`] as the means. Whichever crate
/// serializes owes this; none does yet.
pub open spec fn serialization_round_trips(
    serialize: spec_fn(Seq<ComponentValue>) -> Seq<u32>,
    same_but_for_whitespace: spec_fn(Seq<ComponentValue>, Seq<ComponentValue>) -> bool,
    string: Seq<u32>,
) -> bool {
    let parsed = parse_a_list_of_component_values(Input::String { string });
    same_but_for_whitespace(
        parsed,
        parse_a_list_of_component_values(Input::String { string: serialize(parsed) }),
    )
}

} // verus!
