//! Executable-style specification of CSS parsing, transcribed from CSS Syntax Module
//! Level 3. Nothing here runs; it defines what "correct" means.
//!
//! Source: CSS Syntax Module Level 3, Editor's Draft, `css-syntax-3/Overview.bs` of
//! `w3c/csswg-drafts` at commit `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`
//! (2026-10-20), <https://drafts.csswg.org/css-syntax-3/>, the commit
//! [`crate::tokenizer::spec`] pins. Each function cites its section by anchor. The
//! algorithms are mostly unnumbered prose and definition lists, so a `// "…"` comment
//! quotes the branch it stands for, and `// N.` is used where the text numbers its steps.
//!
//! Modelling choices (each one a deliberate difference in form, never in meaning, except
//! the two marked **meaning**, which say what they change):
//! - A token stream's "index" is not a field. As in the tokenizer, each algorithm is a
//!   function of an unchanging [`TokenStream`] and an index, returning its result and the
//!   index after it. "Repeatedly", and "process", are a recursive function named for the
//!   algorithm with `_loop`, carrying what the text builds up.
//! - "Mark" and "restore a mark" have one user, "consume a block's contents", which never
//!   holds two marks, so "marked indexes" is a local: mark is keeping the index, restore
//!   is using it again, and discarding a mark is not using it.
//! - Parse errors change nothing about what is returned, so they are not modelled.
//! - An item of a stream is a [`ComponentValue`]. Its [`ComponentValue::Token`] holds any
//!   token, so that a list of "tokens and/or component values" is one type; a function
//!   token or an opening bracket there is a token not yet consumed, and
//!   [`super::contract::output_preserved`] states that none is left in any output.
//! - The EOF token is [`Token::Eof`], which the tokenizer pushes last and [`next_token`]
//!   gives past the end, so "empty" holds at the one as at the other.
//! - "The current context" is **meaning**: the text leaves it to other specifications,
//!   and this crate knows no grammars, so it parses as the "generic processor" of the
//!   implementation note in "consume a block's contents". [`rule_is_valid`] and
//!   [`declaration_is_valid`] are true, and the branches they guard are kept as the text
//!   has them. `clazel-style` drops what is invalid from the result. Two things differ
//!   from parsing with the context: what is dropped is dropped later, and a declaration
//!   that is invalid for its property, such as `color: {}`, stays a declaration here
//!   where the text would reparse it as a rule, fail, and take the "invalid rule error"
//!   branch, which would split the declarations around it into two lists. By the note in
//!   "consume a qualified rule" the tokens consumed are the same either way.
//! - The text's "original source text" is **meaning**: it is the string after "filter
//!   code points", since that is what positions index and what the tokenizer reads, so
//!   an original text has U+000A where the sheet had U+000D, and U+FFFD for U+0000.
//! - A token's text starts after the comments "consume a token" skips before it, so a
//!   comment before the first token of a value, or after the last, is not in the value's
//!   original text, and one between its tokens is.
//! - A stream made from a list has no source text ([`TokenStream::source`] is `None`), so
//!   [`consume_a_declaration`] gives such a declaration no original text and leaves a
//!   unicode-range value as it is. The text only reaches those steps from strings.
//! - "If |input| is a byte stream" in "parse a stylesheet" is not here: the input is a
//!   string or a stream, and decoding is the caller's.
//! - Each `parse_` function returns only its result. The text may hand one a stream that
//!   goes on being used, but none of its callers reads the stream afterwards.
//! - "Syntax error" and "failure" are `None`.
//! - [`moved`] appears wherever a loop goes on after a call that consumes something. A
//!   recursive function here cannot use what the same recursion returns to show that it
//!   ends, so the loop is given the index only if it went forward, and one more if not.
//!   It always went forward (proven in [`super::termination`]), so [`moved`] returns
//!   the index it was given.
//! - "Assert" is a `when` on a function's `decreases`: the function says nothing where
//!   the assertion is false.

pub use crate::tokenizer::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// §5.2 CSS Parsing Results
// ------------------------------------------------------------------------------------

/// §5.2 component value. "A component value is one of the preserved tokens, a function,
/// or a simple block."
pub ghost enum ComponentValue {
    /// A token. See the modelling choices.
    Token {
        /// The token.
        token: Token,
    },
    /// "A function has a name and a value consisting of a list of component values."
    Function {
        /// The name.
        name: Seq<u32>,
        /// The value.
        value: Seq<ComponentValue>,
    },
    /// "A simple block has an associated token … and a value consisting of a list of
    /// component values."
    SimpleBlock {
        /// The associated token: `<[-token>`, `<(-token>` or `<{-token>`.
        associated_token: Token,
        /// The value.
        value: Seq<ComponentValue>,
    },
}

/// §5.2 declaration.
pub ghost struct Declaration {
    /// "a name which is a string".
    pub name: Seq<u32>,
    /// "a value consisting of a list of component values".
    pub value: Seq<ComponentValue>,
    /// "an important flag which is initially unset".
    pub important: bool,
    /// "an optional original text which is a string".
    pub original_text: Option<Seq<u32>>,
}

/// §5.2 rule, and the nested declarations rule of "consume a qualified rule".
pub ghost enum Rule {
    /// "An at-rule has a name which is a string, a prelude consisting of a list of
    /// component values." `child_rules` is `None` for a statement at-rule, and the result
    /// of "consume a block" for a block at-rule: the text assigns it whole, and leaves
    /// what its lists of declarations become to the rule.
    AtRule {
        /// The name.
        name: Seq<u32>,
        /// The prelude.
        prelude: Seq<ComponentValue>,
        /// The child rules.
        child_rules: Option<Seq<BlockItem>>,
    },
    /// "A qualified rule has a prelude consisting of a list of component values, a list
    /// of declarations, and a list of child rules."
    QualifiedRule {
        /// The prelude.
        prelude: Seq<ComponentValue>,
        /// The declarations.
        declarations: Seq<Declaration>,
        /// The child rules.
        child_rules: Seq<Rule>,
    },
    /// A nested declarations rule [CSS-NESTING-1].
    NestedDeclarationsRule {
        /// The declarations.
        declarations: Seq<Declaration>,
    },
}

/// An item of the list "consume a block's contents" returns: "rules and lists of
/// declarations".
pub ghost enum BlockItem {
    /// A rule.
    Rule {
        /// The rule.
        rule: Rule,
    },
    /// A list of declarations.
    Declarations {
        /// The list.
        declarations: Seq<Declaration>,
    },
}

/// §5.2 stylesheet: "A stylesheet has a list of rules", and "parse a stylesheet" gives it
/// a location.
pub ghost struct Stylesheet {
    /// The location, or null.
    pub location: Option<Seq<u32>>,
    /// The rules.
    pub rules: Seq<Rule>,
}

/// What "consume a qualified rule" returns.
pub ghost enum QualifiedRuleResult {
    /// "Return nothing."
    Nothing,
    /// "an invalid rule error".
    InvalidRuleError,
    /// A rule.
    Rule {
        /// The rule.
        rule: Rule,
    },
}

// ------------------------------------------------------------------------------------
// §5.3 Token Streams
// ------------------------------------------------------------------------------------

/// Where one item of a stream made from a string lies in that string.
pub ghost struct Span {
    /// The position of its first code point, after any comments.
    pub start: int,
    /// The position after its last code point.
    pub end: int,
}

/// "the ability to reproduce the original text of declarations on demand".
pub ghost struct SourceText {
    /// The string the stream was tokenized from.
    pub text: Seq<u32>,
    /// One span for each item of the stream, in order.
    pub spans: Seq<Span>,
}

/// §5.3 token stream, without its "index" and "marked indexes" (modelling choices).
pub ghost struct TokenStream {
    /// "tokens": "A list of tokens and/or component values."
    pub tokens: Seq<ComponentValue>,
    /// The text they came from, if they came from a string.
    pub source: Option<SourceText>,
}

/// How many items are left at `index`, which is what falls as a recursive function of
/// this file moves on.
pub open spec fn items_left(input: TokenStream, index: int) -> nat {
    if index < input.tokens.len() {
        (input.tokens.len() - index) as nat
    } else {
        0
    }
}

/// True if `item` is exactly `token`.
pub open spec fn is(item: ComponentValue, token: Token) -> bool {
    item == (ComponentValue::Token { token })
}

/// True if `item` is `stop`, if there is one.
pub open spec fn is_stop(item: ComponentValue, stop: Option<Token>) -> bool {
    match stop {
        Some(token) => is(item, token),
        None => false,
    }
}

/// True for an `<at-keyword-token>`.
pub open spec fn is_at_keyword(item: ComponentValue) -> bool {
    match item {
        ComponentValue::Token { token: Token::AtKeyword { .. } } => true,
        _ => false,
    }
}

/// True for a `<function-token>`.
pub open spec fn is_function_token(item: ComponentValue) -> bool {
    match item {
        ComponentValue::Token { token: Token::Function { .. } } => true,
        _ => false,
    }
}

/// True for an `<ident-token>`.
pub open spec fn is_ident(item: ComponentValue) -> bool {
    match item {
        ComponentValue::Token { token: Token::Ident { .. } } => true,
        _ => false,
    }
}

/// The value of an `<ident-token>`, `<function-token>` or `<at-keyword-token>`.
pub open spec fn token_value(item: ComponentValue) -> Seq<u32> {
    match item {
        ComponentValue::Token { token: Token::Ident { value } } => value,
        ComponentValue::Token { token: Token::Function { value } } => value,
        ComponentValue::Token { token: Token::AtKeyword { value } } => value,
        _ => Seq::empty(),
    }
}

/// True for `<[-token>`, `<(-token>` or `<{-token>`.
pub open spec fn is_open_bracket(item: ComponentValue) -> bool {
    is(item, Token::OpenCurly) || is(item, Token::OpenSquare) || is(item, Token::OpenParen)
}

/// §5.3 "next token": "The item of tokens at index. If that index would be out-of-bounds
/// past the end of the list, it's instead an <eof-token>."
pub open spec fn next_token(input: TokenStream, index: int) -> ComponentValue {
    if 0 <= index < input.tokens.len() {
        input.tokens[index]
    } else {
        ComponentValue::Token { token: Token::Eof }
    }
}

/// §5.3 "empty": "if the next token is an <eof-token>".
pub open spec fn is_empty(input: TokenStream, index: int) -> bool {
    is(next_token(input, index), Token::Eof)
}

/// §5.3 "consume a token": "Let token be the next token. Increment index, then return
/// token."
pub open spec fn consume_a_token(input: TokenStream, index: int) -> (ComponentValue, int) {
    (next_token(input, index), index + 1)
}

/// §5.3 "discard a token": "If the token stream is not empty, increment index."
pub open spec fn discard_a_token(input: TokenStream, index: int) -> int {
    if !is_empty(input, index) {
        index + 1
    } else {
        index
    }
}

/// §5.3 "discard whitespace": "While the next token is a <whitespace-token>, discard a
/// token."
pub open spec fn discard_whitespace(input: TokenStream, index: int) -> int
    decreases items_left(input, index),
{
    if is(next_token(input, index), Token::Whitespace) {
        discard_whitespace(input, discard_a_token(input, index))
    } else {
        index
    }
}

/// `next`, the index a loop at `index` reached, if that is further on (modelling
/// choices).
pub open spec fn moved(index: int, next: int) -> int {
    if next > index {
        next
    } else {
        index + 1
    }
}

// ------------------------------------------------------------------------------------
// §5.4 Parser Entry Points: normalize into a token stream
// ------------------------------------------------------------------------------------

/// The tokenizer's "consume a token", which is not the token stream's.
pub open spec fn read_a_token(input: Seq<u32>, pos: int, unicode_ranges_allowed: bool) -> (
    Token,
    int,
) {
    crate::tokenizer::spec::consume_a_token(input, pos, unicode_ranges_allowed)
}

/// The spans of "tokenize", from position `pos` of `input`, with `spans` so far. It walks
/// exactly as [`crate::tokenizer::spec::tokenize_loop`] does.
pub open spec fn spans_loop(
    input: Seq<u32>,
    pos: int,
    unicode_ranges_allowed: bool,
    spans: Seq<Span>,
) -> Seq<Span>
    decreases remaining(input, pos) via spans_decreases
{
    let (token, next) = read_a_token(input, pos, unicode_ranges_allowed);
    let span = Span { start: consume_comments(input, pos), end: next };
    if token is Eof {
        spans.push(span)
    } else {
        spans_loop(input, next, unicode_ranges_allowed, spans.push(span))
    }
}

/// [`tokenize_with`] as the items of a stream.
pub open spec fn as_items(tokens: Seq<Token>) -> Seq<ComponentValue> {
    Seq::new(tokens.len(), |i: int| ComponentValue::Token { token: tokens[i] })
}

/// The stream of `string`'s tokens, which keeps the string and where each token lies in
/// it, for the original text of declarations.
pub open spec fn token_stream(string: Seq<u32>, unicode_ranges_allowed: bool) -> TokenStream {
    TokenStream {
        tokens: as_items(tokenize_with(string, unicode_ranges_allowed)),
        source: Some(
            SourceText {
                text: string,
                spans: spans_loop(string, 0, unicode_ranges_allowed, Seq::empty()),
            },
        ),
    }
}

/// What "normalize into a token stream" takes.
pub ghost enum Input {
    /// "already a token stream", at the index it has reached.
    Stream {
        /// The stream.
        stream: TokenStream,
        /// Its index.
        index: int,
    },
    /// "a list of CSS tokens and/or component values".
    List {
        /// The list.
        list: Seq<ComponentValue>,
    },
    /// "a string".
    String {
        /// The string.
        string: Seq<u32>,
    },
}

/// §5.4 <https://drafts.csswg.org/css-syntax-3/#normalize-into-a-token-stream>, as the
/// stream and its index. 4. "Assert: Only the preceding types should be passed as input."
/// is [`Input`].
pub open spec fn normalize(input: Input) -> (TokenStream, int) {
    match input {
        // 1. "If input is already a token stream, return it."
        Input::Stream { stream, index } => (stream, index),
        // 2. "If input is a list of CSS tokens and/or component values, create a new token
        // stream with input as its tokens, and return it."
        Input::List { list } => (TokenStream { tokens: list, source: None }, 0),
        // 3. "If input is a string, then filter code points from input, tokenize the
        // result, and return the stream of tokens."
        Input::String { string } => (token_stream(filter_code_points(string), false), 0),
    }
}

// ------------------------------------------------------------------------------------
// §5.5.8 Consume a component value, §5.5.9 a simple block, §5.5.10 a function
// ------------------------------------------------------------------------------------

/// The mirror variant of an opening bracket: "if it was called with <[-token>, the ending
/// token is <]-token>".
pub open spec fn mirror(item: ComponentValue) -> Token {
    if is(item, Token::OpenCurly) {
        Token::CloseCurly
    } else if is(item, Token::OpenSquare) {
        Token::CloseSquare
    } else {
        Token::CloseParen
    }
}

/// §5.5.8 <https://drafts.csswg.org/css-syntax-3/#consume-component-value>. "Process" ends
/// at once, since every action returns.
pub open spec fn consume_a_component_value(input: TokenStream, index: int) -> (
    ComponentValue,
    int,
)
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    // <{-token>, <[-token>, <(-token>: "Consume a simple block from input and return the
    // result."
    if is_open_bracket(item) {
        consume_a_simple_block(input, index)
    // <function-token>: "Consume a function from input and return the result."
    } else if is_function_token(item) {
        consume_a_function(input, index)
    // anything else: "Consume a token from input and return the result."
    } else {
        consume_a_token(input, index)
    }
}

/// §5.5.9 <https://drafts.csswg.org/css-syntax-3/#consume-simple-block>.
pub open spec fn consume_a_simple_block(input: TokenStream, index: int) -> (ComponentValue, int)
    // "Assert: the next token of input is <{-token>, <[-token>, or <(-token>."
    decreases items_left(input, index), 0nat when is_open_bracket(next_token(input, index))
{
    let item = next_token(input, index);
    // "Let ending token be the mirror variant of the next token."
    let ending_token = mirror(item);
    // "Let block be a new simple block with its associated token set to the next token and
    // with its value initially set to an empty list."
    let associated_token = match item {
        ComponentValue::Token { token } => token,
        _ => Token::Eof,
    };
    // "Discard a token from input."
    simple_block_loop(
        input,
        discard_a_token(input, index),
        ending_token,
        associated_token,
        Seq::empty(),
    )
}

/// "Process input" of §5.5.9.
pub open spec fn simple_block_loop(
    input: TokenStream,
    index: int,
    ending_token: Token,
    associated_token: Token,
    value: Seq<ComponentValue>,
) -> (ComponentValue, int)
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    // <eof-token>, ending token: "Discard a token from input. Return block."
    if is(item, Token::Eof) || is(item, ending_token) {
        (ComponentValue::SimpleBlock { associated_token, value }, discard_a_token(input, index))
    // anything else: "Consume a component value from input and append the result to
    // block's value."
    } else {
        let (component_value, next) = consume_a_component_value(input, index);
        simple_block_loop(
            input,
            moved(index, next),
            ending_token,
            associated_token,
            value.push(component_value),
        )
    }
}

/// §5.5.10 <https://drafts.csswg.org/css-syntax-3/#consume-function>.
pub open spec fn consume_a_function(input: TokenStream, index: int) -> (ComponentValue, int)
    // "Assert: The next token is a <function-token>."
    decreases items_left(input, index), 0nat when is_function_token(next_token(input, index))
{
    // "Consume a token from input, and let function be a new function with its name equal
    // the returned token's value, and a value set to an empty list."
    let (token, next) = consume_a_token(input, index);
    function_loop(input, next, token_value(token), Seq::empty())
}

/// "Process input" of §5.5.10.
pub open spec fn function_loop(
    input: TokenStream,
    index: int,
    name: Seq<u32>,
    value: Seq<ComponentValue>,
) -> (ComponentValue, int)
    decreases items_left(input, index), 2nat,
{
    let item = next_token(input, index);
    // <eof-token>, <)-token>: "Discard a token from input. Return function."
    if is(item, Token::Eof) || is(item, Token::CloseParen) {
        (ComponentValue::Function { name, value }, discard_a_token(input, index))
    // anything else: "Consume a component value from input and append the result to
    // function's value."
    } else {
        let (component_value, next) = consume_a_component_value(input, index);
        function_loop(input, moved(index, next), name, value.push(component_value))
    }
}

// ------------------------------------------------------------------------------------
// §5.5.7 Consume a list of component values
// ------------------------------------------------------------------------------------

/// "Process input" of §5.5.7.
pub open spec fn list_of_component_values_loop(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
    values: Seq<ComponentValue>,
) -> (Seq<ComponentValue>, int)
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    // <eof-token>, stop token (if passed): "Return values."
    if is(item, Token::Eof) || is_stop(item, stop_token) {
        (values, index)
    // <}-token>
    } else if is(item, Token::CloseCurly) {
        // "If nested is true, return values."
        if nested {
            (values, index)
        // "Otherwise, this is a parse error. Consume a token from input and append the
        // result to values."
        } else {
            let (token, next) = consume_a_token(input, index);
            list_of_component_values_loop(input, next, stop_token, nested, values.push(token))
        }
    // anything else: "Consume a component value from input, and append the result to
    // values."
    } else {
        let (value, next) = consume_a_component_value(input, index);
        list_of_component_values_loop(
            input,
            moved(index, next),
            stop_token,
            nested,
            values.push(value),
        )
    }
}

/// §5.5.7 <https://drafts.csswg.org/css-syntax-3/#consume-list-of-components>.
pub open spec fn consume_a_list_of_component_values(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
) -> (Seq<ComponentValue>, int) {
    // "Let values be an empty list of component values."
    list_of_component_values_loop(input, index, stop_token, nested, Seq::empty())
}

// ------------------------------------------------------------------------------------
// §5.5.11 Consume the value of a unicode-range descriptor
// ------------------------------------------------------------------------------------

/// §5.5.11 <https://drafts.csswg.org/css-syntax-3/#consume-unicode-range-value>.
pub open spec fn consume_the_value_of_a_unicode_range_descriptor(input_string: Seq<u32>) -> Seq<
    ComponentValue,
> {
    // 1. "Let tokens be the result of tokenizing input string with unicode ranges allowed
    // set to true."
    let tokens = token_stream(input_string, true);
    // 2. "Consume a list of component values from tokens, and return the result."
    consume_a_list_of_component_values(tokens, 0, None, false).0
}

// ------------------------------------------------------------------------------------
// §5.5.6 Consume a declaration
// ------------------------------------------------------------------------------------

/// "Process input" of "consume the remnants of a bad declaration", §5.5.6, as the index
/// after it.
pub open spec fn consume_the_remnants_of_a_bad_declaration(
    input: TokenStream,
    index: int,
    nested: bool,
) -> int
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    // <eof-token>, <semicolon-token>: "Discard a token from input, and return nothing."
    if is(item, Token::Eof) || is(item, Token::Semicolon) {
        discard_a_token(input, index)
    // <}-token>
    } else if is(item, Token::CloseCurly) {
        // "If nested is true, return nothing."
        if nested {
            index
        // "Otherwise, discard a token."
        } else {
            consume_the_remnants_of_a_bad_declaration(
                input,
                discard_a_token(input, index),
                nested,
            )
        }
    // anything else: "Consume a component value from input, and do nothing."
    } else {
        let (_, next) = consume_a_component_value(input, index);
        consume_the_remnants_of_a_bad_declaration(input, moved(index, next), nested)
    }
}

/// True for a `<whitespace-token>` in a list.
pub open spec fn is_whitespace_token(item: ComponentValue) -> bool {
    is(item, Token::Whitespace)
}

/// The index of the last non-whitespace item of `value` before `end`, or -1.
pub open spec fn last_non_whitespace(value: Seq<ComponentValue>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        -1
    } else if !is_whitespace_token(value[end - 1]) {
        end - 1
    } else {
        last_non_whitespace(value, end - 1)
    }
}

/// The ASCII lowercase of a code point.
pub open spec fn ascii_lowercase(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// True if `string` from `i` on is an ASCII case-insensitive match for `lowercase`.
pub open spec fn matches_from(string: Seq<u32>, lowercase: Seq<u32>, i: int) -> bool
    decreases string.len() - i,
{
    i >= string.len() || (ascii_lowercase(string[i]) == lowercase[i] && matches_from(
        string,
        lowercase,
        i + 1,
    ))
}

/// True if `string` is an ASCII case-insensitive match for `lowercase`.
pub open spec fn ascii_case_insensitive_match(string: Seq<u32>, lowercase: Seq<u32>) -> bool {
    string.len() == lowercase.len() && matches_from(string, lowercase, 0)
}

/// "important".
pub open spec fn important_string() -> Seq<u32> {
    seq![0x69u32, 0x6D, 0x70, 0x6F, 0x72, 0x74, 0x61, 0x6E, 0x74]
}

/// "unicode-range".
pub open spec fn unicode_range_string() -> Seq<u32> {
    seq![0x75u32, 0x6E, 0x69, 0x63, 0x6F, 0x64, 0x65, 0x2D, 0x72, 0x61, 0x6E, 0x67, 0x65]
}

/// The two items of step 6, as (the index of "!", the index of "important"), if the last
/// two non-whitespace items are those.
pub open spec fn important_at(value: Seq<ComponentValue>) -> Option<(int, int)> {
    let second = last_non_whitespace(value, value.len() as int);
    let first = last_non_whitespace(value, second);
    if first >= 0 && is(value[first], Token::Delim { value: 0x21 }) && is_ident(value[second])
        && ascii_case_insensitive_match(token_value(value[second]), important_string()) {
        Some((first, second))
    } else {
        None
    }
}

/// `value` without its last items while they are `<whitespace-token>`s.
pub open spec fn without_trailing_whitespace(value: Seq<ComponentValue>) -> Seq<ComponentValue>
    decreases value.len(),
{
    if value.len() > 0 && is_whitespace_token(value.last()) {
        without_trailing_whitespace(value.drop_last())
    } else {
        value
    }
}

/// True if a string starts with two dashes, "custom property name string". The text links
/// the term without a definition at the pinned commit; css-variables-1 §2 says "any
/// property whose name starts with two dashes (U+002D HYPHEN-MINUS)". "--" alone is
/// reserved by `<custom-property-name>`, but that is a grammar and this is a string, so
/// it counts here.
pub open spec fn is_custom_property_name_string(name: Seq<u32>) -> bool {
    starts_with_two_dashes(name)
}

/// True for a simple block whose associated token is `<{-token>`.
pub open spec fn is_curly_block(item: ComponentValue) -> bool {
    match item {
        ComponentValue::SimpleBlock { associated_token: Token::OpenCurly, .. } => true,
        _ => false,
    }
}

/// True if `value` from `i` on has a simple block whose associated token is `<{-token>`.
pub open spec fn has_curly_block(value: Seq<ComponentValue>, i: int) -> bool
    decreases value.len() - i,
{
    0 <= i < value.len() && (is_curly_block(value[i]) || has_curly_block(value, i + 1))
}

/// How many items of `value` from `i` on are not `<whitespace-token>`s.
pub open spec fn non_whitespace_count(value: Seq<ComponentValue>, i: int) -> nat
    decreases value.len() - i,
{
    if i < 0 || i >= value.len() {
        0
    } else if is_whitespace_token(value[i]) {
        non_whitespace_count(value, i + 1)
    } else {
        1 + non_whitespace_count(value, i + 1)
    }
}

/// "contains a top-level simple block with an associated token of <{-token>, and also
/// contains any other non-<whitespace-token> value". The block is itself one such value,
/// so the other makes two.
pub open spec fn has_curly_block_and_another(value: Seq<ComponentValue>) -> bool {
    has_curly_block(value, 0) && non_whitespace_count(value, 0) >= 2
}

/// "the segment of the original source text string corresponding to the tokens" from
/// index `start` up to, and not including, index `end`. `None` if the stream has no
/// source text, and empty if there are no such tokens.
pub open spec fn segment(input: TokenStream, start: int, end: int) -> Option<Seq<u32>> {
    match input.source {
        None => None,
        Some(source) => if start >= end {
            Some(Seq::empty())
        } else {
            Some(source.text.subrange(source.spans[start].start, source.spans[end - 1].end))
        },
    }
}

/// "If decl is valid in the current context": a generic processor, so always (modelling
/// choices).
pub open spec fn declaration_is_valid(decl: Declaration) -> bool {
    true
}

/// Step 9 of §5.5.6.
pub open spec fn finish_declaration(decl: Declaration, index: int) -> (Option<Declaration>, int) {
    // 9. "If decl is valid in the current context, return it; otherwise return nothing."
    if declaration_is_valid(decl) {
        (Some(decl), index)
    } else {
        (None, index)
    }
}

/// Steps 5 to 9 of §5.5.6. `start` is the index step 4 reached.
pub open spec fn declaration_value(
    input: TokenStream,
    start: int,
    nested: bool,
    name: Seq<u32>,
) -> (Option<Declaration>, int) {
    // 5. "Consume a list of component values from input, with nested, and with
    // <semicolon-token> as the stop token, and set decl's value to the result."
    let (list, end) = consume_a_list_of_component_values(
        input,
        start,
        Some(Token::Semicolon),
        nested,
    );
    // 6. "If the last two non-<whitespace-token>s in decl's value are a <delim-token> with
    // the value "!" followed by an <ident-token> with a value that is an ASCII
    // case-insensitive match for "important", remove them from decl's value and set
    // decl's important flag."
    let (value, important) = match important_at(list) {
        Some((first, second)) => (list.remove(second).remove(first), true),
        None => (list, false),
    };
    // 7. "While the last item in decl's value is a <whitespace-token>, remove that token."
    let value = without_trailing_whitespace(value);
    // Steps 6 and 7 removed only single tokens after every item that stays, one stream
    // item each, so the items that stay end this far before `end`.
    let value_end = end - (list.len() - value.len());
    // 8. "If decl's name is a custom property name string, then set decl's original text
    // to the segment of the original source text string corresponding to the tokens of
    // decl's value."
    if is_custom_property_name_string(name) {
        finish_declaration(
            Declaration { name, value, important, original_text: segment(input, start, value_end) },
            end,
        )
    // "Otherwise, if decl's value contains a top-level simple block with an associated
    // token of <{-token>, and also contains any other non-<whitespace-token> value, return
    // nothing."
    } else if has_curly_block_and_another(value) {
        (None, end)
    // "Otherwise, if decl's name is an ASCII case-insensitive match for "unicode-range",
    // consume the value of a unicode-range descriptor from the segment of the original
    // source text string corresponding to the tokens returned by the consume a list of
    // component values call, and replace decl's value with the result."
    //
    // That segment is the whole list, so as written a "!important" that step 6 removed
    // comes back into the value, with the flag still set, as does trailing whitespace. The
    // text is explicit, and the descriptor's grammar decides what follows, so this does as
    // it says.
    } else if ascii_case_insensitive_match(name, unicode_range_string()) {
        let replaced = match segment(input, start, end) {
            Some(text) => consume_the_value_of_a_unicode_range_descriptor(text),
            None => value,
        };
        finish_declaration(
            Declaration { name, value: replaced, important, original_text: None },
            end,
        )
    } else {
        finish_declaration(Declaration { name, value, important, original_text: None }, end)
    }
}

/// §5.5.6 <https://drafts.csswg.org/css-syntax-3/#consume-declaration>. "Let decl be a new
/// declaration, with an initially empty name and a value set to an empty list."
pub open spec fn consume_a_declaration(input: TokenStream, index: int, nested: bool) -> (
    Option<Declaration>,
    int,
) {
    // 1. "If the next token is an <ident-token>, consume a token from input and set decl's
    // name to the token's value."
    if is_ident(next_token(input, index)) {
        let (token, after_name) = consume_a_token(input, index);
        let name = token_value(token);
        // 2. "Discard whitespace from input."
        let after_whitespace = discard_whitespace(input, after_name);
        // 3. "If the next token is a <colon-token>, discard a token from input."
        if is(next_token(input, after_whitespace), Token::Colon) {
            let after_colon = discard_a_token(input, after_whitespace);
            // 4. "Discard whitespace from input."
            let start = discard_whitespace(input, after_colon);
            // 5. to 9.
            declaration_value(input, start, nested, name)
        // "Otherwise, consume the remnants of a bad declaration from input, with nested,
        // and return nothing."
        } else {
            (None, consume_the_remnants_of_a_bad_declaration(input, after_whitespace, nested))
        }
    // "Otherwise, consume the remnants of a bad declaration from input, with nested, and
    // return nothing."
    } else {
        (None, consume_the_remnants_of_a_bad_declaration(input, index, nested))
    }
}

// ------------------------------------------------------------------------------------
// §5.5.2 to §5.5.5: at-rules, qualified rules and blocks
// ------------------------------------------------------------------------------------

/// "If rule is valid in the current context": a generic processor, so always (modelling
/// choices).
pub open spec fn rule_is_valid(rule: Rule) -> bool {
    true
}

/// "If rule is valid in the current context, return it; otherwise return nothing."
pub open spec fn rule_if_valid(rule: Rule) -> Option<Rule> {
    if rule_is_valid(rule) {
        Some(rule)
    } else {
        None
    }
}

/// §5.5.2 <https://drafts.csswg.org/css-syntax-3/#consume-at-rule>.
pub open spec fn consume_an_at_rule(input: TokenStream, index: int, nested: bool) -> (
    Option<Rule>,
    int,
)
    // "Assert: The next token is an <at-keyword-token>."
    decreases items_left(input, index), 2nat when is_at_keyword(next_token(input, index))
{
    // "Consume a token from input, and let rule be a new at-rule with its name set to the
    // returned token's value, its prelude initially set to an empty list, and no
    // declarations or child rules."
    let (token, next) = consume_a_token(input, index);
    at_rule_loop(input, next, nested, token_value(token), Seq::empty())
}

/// "Process input" of §5.5.2.
pub open spec fn at_rule_loop(
    input: TokenStream,
    index: int,
    nested: bool,
    name: Seq<u32>,
    prelude: Seq<ComponentValue>,
) -> (Option<Rule>, int)
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    let statement = Rule::AtRule { name, prelude, child_rules: None };
    // <semicolon-token>, <EOF-token>: "Discard a token from input. If rule is valid in the
    // current context, return it; otherwise return nothing."
    if is(item, Token::Semicolon) || is(item, Token::Eof) {
        (rule_if_valid(statement), discard_a_token(input, index))
    // <}-token>
    } else if is(item, Token::CloseCurly) {
        // "If nested is true: If rule is valid in the current context, return it. Otherwise,
        // return nothing."
        if nested {
            (rule_if_valid(statement), index)
        // "Otherwise, consume a token and append the result to rule's prelude."
        } else {
            let (token, next) = consume_a_token(input, index);
            at_rule_loop(input, next, nested, name, prelude.push(token))
        }
    // <{-token>: "Consume a block from input, and assign the result to rule's child rules.
    // … If rule is valid in the current context, return it. Otherwise, return nothing."
    } else if is(item, Token::OpenCurly) {
        let (child_rules, next) = consume_a_block(input, index);
        (rule_if_valid(Rule::AtRule { name, prelude, child_rules: Some(child_rules) }), next)
    // anything else: "Consume a component value from input and append the returned value to
    // rule's prelude."
    } else {
        let (value, next) = consume_a_component_value(input, index);
        at_rule_loop(input, moved(index, next), nested, name, prelude.push(value))
    }
}

/// True if `string` starts with "--".
pub open spec fn starts_with_two_dashes(string: Seq<u32>) -> bool {
    string.len() >= 2 && string[0] == 0x2D && string[1] == 0x2D
}

/// "If the first two non-<whitespace-token> values of rule's prelude are an <ident-token>
/// whose value starts with "--" followed by a <colon-token>".
pub open spec fn prelude_looks_like_a_custom_property(prelude: Seq<ComponentValue>) -> bool {
    let first = first_non_whitespace(prelude, 0);
    let second = first_non_whitespace(prelude, first + 1);
    second < prelude.len() && is_ident(prelude[first]) && starts_with_two_dashes(
        token_value(prelude[first]),
    ) && is(prelude[second], Token::Colon)
}

/// The index of the first non-whitespace item of `value` at or after `start`, or the
/// length of `value`.
pub open spec fn first_non_whitespace(value: Seq<ComponentValue>, start: int) -> int
    decreases value.len() - start,
{
    if start >= value.len() || start < 0 {
        value.len() as int
    } else if !is_whitespace_token(value[start]) {
        start
    } else {
        first_non_whitespace(value, start + 1)
    }
}

/// "If any remaining items of child rules are lists of declarations, replace them with
/// nested declarations rules containing the list as its declarations."
pub open spec fn child_rules_of(items: Seq<BlockItem>) -> Seq<Rule> {
    Seq::new(
        items.len(),
        |i: int|
            match items[i] {
                BlockItem::Rule { rule } => rule,
                BlockItem::Declarations { declarations } => Rule::NestedDeclarationsRule {
                    declarations,
                },
            },
    )
}

/// The rule of §5.5.3's <{-token> branch, once "consume a block" gave `child_rules`.
pub open spec fn qualified_rule_from(
    prelude: Seq<ComponentValue>,
    child_rules: Seq<BlockItem>,
) -> Rule {
    // "If the first item of child rules is a list of declarations, remove it from child
    // rules and assign it to rule's declarations."
    if child_rules.len() > 0 && child_rules[0] is Declarations {
        Rule::QualifiedRule {
            prelude,
            declarations: child_rules[0]->declarations,
            // "Assign child rules to rule's child rules."
            child_rules: child_rules_of(child_rules.drop_first()),
        }
    } else {
        Rule::QualifiedRule {
            prelude,
            declarations: Seq::empty(),
            // "Assign child rules to rule's child rules."
            child_rules: child_rules_of(child_rules),
        }
    }
}

/// §5.5.3 <https://drafts.csswg.org/css-syntax-3/#consume-qualified-rule>.
pub open spec fn consume_a_qualified_rule(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
) -> (QualifiedRuleResult, int)
    decreases items_left(input, index), 2nat,
{
    // "Let rule be a new qualified rule with its prelude, declarations, and child rules all
    // initially set to empty lists."
    qualified_rule_loop(input, index, stop_token, nested, Seq::empty())
}

/// "Process input" of §5.5.3.
pub open spec fn qualified_rule_loop(
    input: TokenStream,
    index: int,
    stop_token: Option<Token>,
    nested: bool,
    prelude: Seq<ComponentValue>,
) -> (QualifiedRuleResult, int)
    decreases items_left(input, index), 1nat,
{
    let item = next_token(input, index);
    // <EOF-token>, stop token (if passed): "This is a parse error. Return nothing."
    if is(item, Token::Eof) || is_stop(item, stop_token) {
        (QualifiedRuleResult::Nothing, index)
    // <}-token>
    } else if is(item, Token::CloseCurly) {
        // "This is a parse error. If nested is true, return nothing."
        if nested {
            (QualifiedRuleResult::Nothing, index)
        // "Otherwise, consume a token and append the result to rule's prelude."
        } else {
            let (token, next) = consume_a_token(input, index);
            qualified_rule_loop(input, next, stop_token, nested, prelude.push(token))
        }
    // <{-token>
    } else if is(item, Token::OpenCurly) {
        // "If the first two non-<whitespace-token> values of rule's prelude are an
        // <ident-token> whose value starts with "--" followed by a <colon-token>, then:"
        if prelude_looks_like_a_custom_property(prelude) {
            // "If nested is true, consume the remnants of a bad declaration from input, with
            // nested set to true, and return nothing."
            if nested {
                (
                    QualifiedRuleResult::Nothing,
                    consume_the_remnants_of_a_bad_declaration(input, index, true),
                )
            // "If nested is false, consume a block from input, and return nothing."
            } else {
                (QualifiedRuleResult::Nothing, consume_a_block(input, index).1)
            }
        // "Otherwise, consume a block from input, and let child rules be the result."
        } else {
            let (child_rules, next) = consume_a_block(input, index);
            let rule = qualified_rule_from(prelude, child_rules);
            // "If rule is valid in the current context, return it; otherwise return an
            // invalid rule error."
            if rule_is_valid(rule) {
                (QualifiedRuleResult::Rule { rule }, next)
            } else {
                (QualifiedRuleResult::InvalidRuleError, next)
            }
        }
    // anything else: "Consume a component value from input and append the result to rule's
    // prelude."
    } else {
        let (value, next) = consume_a_component_value(input, index);
        qualified_rule_loop(input, moved(index, next), stop_token, nested, prelude.push(value))
    }
}

/// §5.5.4 <https://drafts.csswg.org/css-syntax-3/#consume-block>.
pub open spec fn consume_a_block(input: TokenStream, index: int) -> (Seq<BlockItem>, int)
    // "Assert: The next token is a <{-token>."
    decreases items_left(input, index), 0nat when is(next_token(input, index), Token::OpenCurly)
{
    // "Discard a token from input. Consume a block's contents from input and let rules be
    // the result. Discard a token from input."
    let (rules, next) = consume_a_blocks_contents(input, discard_a_token(input, index));
    // "Return rules."
    (rules, discard_a_token(input, next))
}

/// `rules` with `decls` appended, if it is not empty. The caller goes on with "a fresh
/// empty list of declarations".
pub open spec fn with_declarations(rules: Seq<BlockItem>, decls: Seq<Declaration>) -> Seq<
    BlockItem,
> {
    if decls.len() > 0 {
        rules.push(BlockItem::Declarations { declarations: decls })
    } else {
        rules
    }
}

/// §5.5.5 <https://drafts.csswg.org/css-syntax-3/#consume-block-contents>.
pub open spec fn consume_a_blocks_contents(input: TokenStream, index: int) -> (
    Seq<BlockItem>,
    int,
)
    decreases items_left(input, index), 4nat,
{
    // "Let rules be an empty list, containing either rules or lists of declarations. Let
    // decls be an empty list of declarations."
    blocks_contents_loop(input, index, Seq::empty(), Seq::empty())
}

/// "Process input" of §5.5.5.
pub open spec fn blocks_contents_loop(
    input: TokenStream,
    index: int,
    rules: Seq<BlockItem>,
    decls: Seq<Declaration>,
) -> (Seq<BlockItem>, int)
    decreases items_left(input, index), 3nat,
{
    let item = next_token(input, index);
    // <whitespace-token>, <semicolon-token>: "Discard a token from input."
    if is(item, Token::Whitespace) || is(item, Token::Semicolon) {
        blocks_contents_loop(input, discard_a_token(input, index), rules, decls)
    // <EOF-token>, <}-token>: "Return rules." The text stops there, which would lose every
    // declaration after the last rule, so `a { color: red }` would have none. What is
    // evidently meant is that decls goes in first, as in the other branches. See
    // docs/ERRATA.md.
    } else if is(item, Token::Eof) || is(item, Token::CloseCurly) {
        (with_declarations(rules, decls), index)
    // <at-keyword-token>
    } else if is_at_keyword(item) {
        // "If decls is not empty, append it to rules, and set decls to a fresh empty list of
        // declarations."
        let flushed = with_declarations(rules, decls);
        // "Consume an at-rule from input, with nested set to true. If a rule was returned,
        // append it to rules."
        let (rule, next) = consume_an_at_rule(input, index, true);
        match rule {
            Some(rule) => blocks_contents_loop(
                input,
                moved(index, next),
                flushed.push(BlockItem::Rule { rule }),
                Seq::empty(),
            ),
            None => blocks_contents_loop(input, moved(index, next), flushed, Seq::empty()),
        }
    // anything else: "Mark input." (`index` is the mark.)
    } else {
        // "Consume a declaration from input, with nested set to true."
        let (declaration, next) = consume_a_declaration(input, index, true);
        match declaration {
            // "If a declaration was returned, append it to decls, and discard a mark from
            // input."
            Some(decl) => blocks_contents_loop(input, moved(index, next), rules, decls.push(decl)),
            // "Otherwise, restore a mark from input, then consume a qualified rule from
            // input, with nested set to true, and <semicolon-token> as the stop token."
            None => {
                let (result, after_rule) = consume_a_qualified_rule(
                    input,
                    index,
                    Some(Token::Semicolon),
                    true,
                );
                match result {
                    // "If nothing was returned": "Do nothing"
                    QualifiedRuleResult::Nothing => blocks_contents_loop(
                        input,
                        moved(index, after_rule),
                        rules,
                        decls,
                    ),
                    // "If an invalid rule error was returned": "If decls is not empty, append
                    // decls to rules, and set decls to a fresh empty list of declarations.
                    // (Otherwise, do nothing.)"
                    QualifiedRuleResult::InvalidRuleError => blocks_contents_loop(
                        input,
                        moved(index, after_rule),
                        with_declarations(rules, decls),
                        Seq::empty(),
                    ),
                    // "If a rule was returned": "If decls is not empty, append decls to
                    // rules, and set decls to a fresh empty list of declarations. Append the
                    // rule to rules."
                    QualifiedRuleResult::Rule { rule } => blocks_contents_loop(
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

// ------------------------------------------------------------------------------------
// §5.5.1 Consume a stylesheet's contents
// ------------------------------------------------------------------------------------

/// "Process input" of §5.5.1.
pub open spec fn stylesheets_contents_loop(
    input: TokenStream,
    index: int,
    rules: Seq<Rule>,
) -> (Seq<Rule>, int)
    decreases items_left(input, index),
{
    let item = next_token(input, index);
    // <whitespace-token>: "Discard a token from input."
    if is(item, Token::Whitespace) {
        stylesheets_contents_loop(input, discard_a_token(input, index), rules)
    // <EOF-token>: "Return rules."
    } else if is(item, Token::Eof) {
        (rules, index)
    // <CDO-token>, <CDC-token>: "Discard a token from input."
    } else if is(item, Token::Cdo) || is(item, Token::Cdc) {
        stylesheets_contents_loop(input, discard_a_token(input, index), rules)
    // <at-keyword-token>: "Consume an at-rule from input. If anything is returned, append
    // it to rules."
    } else if is_at_keyword(item) {
        let (rule, next) = consume_an_at_rule(input, index, false);
        match rule {
            Some(rule) => stylesheets_contents_loop(input, moved(index, next), rules.push(rule)),
            None => stylesheets_contents_loop(input, moved(index, next), rules),
        }
    // anything else: "Consume a qualified rule from input. If a rule is returned, append it
    // to rules."
    } else {
        let (result, next) = consume_a_qualified_rule(input, index, None, false);
        match result {
            QualifiedRuleResult::Rule { rule } => stylesheets_contents_loop(
                input,
                moved(index, next),
                rules.push(rule),
            ),
            _ => stylesheets_contents_loop(input, moved(index, next), rules),
        }
    }
}

/// §5.5.1 <https://drafts.csswg.org/css-syntax-3/#consume-stylesheet-contents>.
pub open spec fn consume_a_stylesheets_contents(input: TokenStream, index: int) -> (
    Seq<Rule>,
    int,
) {
    // "Let rules be an initially empty list of rules."
    stylesheets_contents_loop(input, index, Seq::empty())
}

// ------------------------------------------------------------------------------------
// §5.4 Parser Entry Points
// ------------------------------------------------------------------------------------

/// §5.4.1 <https://drafts.csswg.org/css-syntax-3/#parse-grammar>. `grammar` is "a CSS
/// grammar production": what it matches is the caller's, and `None` is failure, so this
/// crate depends on no grammar.
pub open spec fn parse_something_according_to_a_css_grammar<T>(
    input: Input,
    grammar: spec_fn(Seq<ComponentValue>) -> Option<T>,
) -> Option<T> {
    // 1. "Normalize input, and set input to the result." 2. "Parse a list of component
    // values from input, and let result be the return value."
    let result = parse_a_list_of_component_values(input);
    // 3. "Attempt to match result against grammar. If this is successful, return the
    // matched result; otherwise, return failure."
    grammar(result)
}

/// §5.4.2 <https://drafts.csswg.org/css-syntax-3/#parse-comma-list>.
pub open spec fn parse_a_comma_separated_list_according_to_a_css_grammar<T>(
    input: Input,
    grammar: spec_fn(Seq<ComponentValue>) -> Option<T>,
) -> Seq<Option<T>> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "If input contains only <whitespace-token>s, return an empty list."
    if is_empty(stream, discard_whitespace(stream, index)) {
        Seq::empty()
    } else {
        // 3. "Parse a comma-separated list of component values from input, and let list be
        // the return value."
        let list = parse_a_comma_separated_list_of_component_values(
            Input::Stream { stream, index },
        );
        // 4. "For each item of list, replace item with the result of parsing item with
        // grammar."
        // 5. "Return list."
        Seq::new(
            list.len(),
            |i: int|
                parse_something_according_to_a_css_grammar(
                    Input::List { list: list[i] },
                    grammar,
                ),
        )
    }
}

/// §5.4.3 <https://drafts.csswg.org/css-syntax-3/#parse-stylesheet>.
pub open spec fn parse_a_stylesheet(input: Input, location: Option<Seq<u32>>) -> Stylesheet {
    // 2. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 3. "Create a new stylesheet, with its location set to location (or null, if location
    // was not passed)."
    // 4. "Consume a stylesheet's contents from input, and set the stylesheet's rules to the
    // result."
    // 5. "Return the stylesheet."
    Stylesheet { location, rules: consume_a_stylesheets_contents(stream, index).0 }
}

/// §5.4.4 <https://drafts.csswg.org/css-syntax-3/#parse-stylesheet-contents>.
pub open spec fn parse_a_stylesheets_contents(input: Input) -> Seq<Rule> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Consume a stylesheet's contents from input, and return the result."
    consume_a_stylesheets_contents(stream, index).0
}

/// Step 3 of §5.4.5, "While input is not empty".
pub open spec fn list_of_declarations_loop(
    input: TokenStream,
    index: int,
    decls: Seq<Declaration>,
) -> Seq<Declaration>
    decreases items_left(input, index),
{
    if is_empty(input, index) {
        // 4. "Return decls."
        decls
    } else {
        // "Discard whitespace from input."
        let start = discard_whitespace(input, index);
        let item = next_token(input, start);
        // "If the next token from input is a <semicolon-token>, discard a token from input."
        if is(item, Token::Semicolon) {
            list_of_declarations_loop(input, moved(index, discard_a_token(input, start)), decls)
        // "Otherwise, if the next token from input is an <at-keyword-token>, consume an
        // at-rule from input and discard the result."
        } else if is_at_keyword(item) {
            let (_, next) = consume_an_at_rule(input, start, false);
            list_of_declarations_loop(input, moved(index, next), decls)
        // "Otherwise, consume a declaration. If anything was returned, append it to decls."
        } else {
            let (declaration, next) = consume_a_declaration(input, start, false);
            match declaration {
                Some(decl) => list_of_declarations_loop(
                    input,
                    moved(index, next),
                    decls.push(decl),
                ),
                None => list_of_declarations_loop(input, moved(index, next), decls),
            }
        }
    }
}

/// §5.4.5 <https://drafts.csswg.org/css-syntax-3/#parse-list-of-declarations>.
pub open spec fn parse_a_list_of_declarations(input: Input) -> Seq<Declaration> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Let decls be an empty list."
    // 3.
    list_of_declarations_loop(stream, index, Seq::empty())
}

/// §5.4.6 <https://drafts.csswg.org/css-syntax-3/#parse-rule>.
pub open spec fn parse_a_rule(input: Input) -> Option<Rule> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Discard whitespace from input."
    let start = discard_whitespace(stream, index);
    // 3. "If input is empty, return a syntax error."
    if is_empty(stream, start) {
        None
    // "Otherwise, if the next token from input is an <at-keyword-token>, consume an at-rule
    // from input, and let rule be the return value."
    } else if is_at_keyword(next_token(stream, start)) {
        let (rule, next) = consume_an_at_rule(stream, start, false);
        finish_rule(stream, rule, next)
    // "Otherwise, consume a qualified rule from input and let rule be the return value. If
    // nothing or an invalid rule error was returned, return a syntax error."
    } else {
        let (result, next) = consume_a_qualified_rule(stream, start, None, false);
        match result {
            QualifiedRuleResult::Rule { rule } => finish_rule(stream, Some(rule), next),
            _ => None,
        }
    }
}

/// Steps 4 and 5 of §5.4.6.
pub open spec fn finish_rule(input: TokenStream, rule: Option<Rule>, index: int) -> Option<Rule> {
    // 4. "Discard whitespace from input."
    let end = discard_whitespace(input, index);
    // 5. "If input is empty, return rule. Otherwise, return a syntax error."
    if is_empty(input, end) {
        rule
    } else {
        None
    }
}

/// §5.4.7 <https://drafts.csswg.org/css-syntax-3/#parse-declaration>.
pub open spec fn parse_a_declaration(input: Input) -> Option<Declaration> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Discard whitespace from input."
    let start = discard_whitespace(stream, index);
    // 3. "If input is empty, return a syntax error."
    if is_empty(stream, start) {
        None
    } else {
        // 4. "Consume a declaration from input. If anything was returned, let value be the
        // return value. Otherwise, return a syntax error."
        let (declaration, next) = consume_a_declaration(stream, start, false);
        match declaration {
            None => None,
            Some(value) => {
                // 5. "Discard whitespace from input."
                let end = discard_whitespace(stream, next);
                // 6. "If input is empty, return value. Otherwise, return a syntax error."
                if is_empty(stream, end) {
                    Some(value)
                } else {
                    None
                }
            },
        }
    }
}

/// §5.4.8 <https://drafts.csswg.org/css-syntax-3/#parse-component-value>.
pub open spec fn parse_a_component_value(input: Input) -> Option<ComponentValue> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Discard whitespace from input."
    let start = discard_whitespace(stream, index);
    // 3. "If input is empty, return a syntax error."
    if is_empty(stream, start) {
        None
    } else {
        // 4. "Consume a component value from input and let value be the return value."
        let (value, next) = consume_a_component_value(stream, start);
        // 5. "Discard whitespace from input."
        let end = discard_whitespace(stream, next);
        // 6. "If input is empty, return value. Otherwise, return a syntax error."
        if is_empty(stream, end) {
            Some(value)
        } else {
            None
        }
    }
}

/// §5.4.9 <https://drafts.csswg.org/css-syntax-3/#parse-list-of-component-values>.
pub open spec fn parse_a_list_of_component_values(input: Input) -> Seq<ComponentValue> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Consume a list of component values from input, and return the result."
    consume_a_list_of_component_values(stream, index, None, false).0
}

/// Step 3 of §5.4.10, "While input is not empty".
pub open spec fn comma_separated_list_loop(
    input: TokenStream,
    index: int,
    groups: Seq<Seq<ComponentValue>>,
) -> Seq<Seq<ComponentValue>>
    decreases items_left(input, index),
{
    if is_empty(input, index) {
        // 4. "Return groups."
        groups
    } else {
        // 3.1 "Consume a list of component values from input, with <comma-token> as the
        // stop token, and append the result to groups."
        let (list, next) = consume_a_list_of_component_values(
            input,
            index,
            Some(Token::Comma),
            false,
        );
        // 3.2 "Discard a token from input."
        comma_separated_list_loop(
            input,
            moved(index, discard_a_token(input, next)),
            groups.push(list),
        )
    }
}

/// §5.4.10 <https://drafts.csswg.org/css-syntax-3/#parse-comma-separated-list-of-component-values>.
pub open spec fn parse_a_comma_separated_list_of_component_values(input: Input) -> Seq<
    Seq<ComponentValue>,
> {
    // 1. "Normalize input, and set input to the result."
    let (stream, index) = normalize(input);
    // 2. "Let groups be an empty list."
    // 3.
    comma_separated_list_loop(stream, index, Seq::empty())
}

// ------------------------------------------------------------------------------------
// §6 The An+B microsyntax
// ------------------------------------------------------------------------------------

/// True if `string` from `i` on is all digits.
pub open spec fn all_digits(string: Seq<u32>, i: int) -> bool
    decreases string.len() - i,
{
    i >= string.len() || (is_digit(string[i]) && all_digits(string, i + 1))
}

/// True for "n", ASCII case-insensitively, followed by "-" and one or more digits, from
/// position `start` of `string`: "n-*" at 0, or "-n-*" at 1.
pub open spec fn is_n_dash_digits(string: Seq<u32>, start: int) -> bool {
    string.len() >= start + 3 && ascii_lowercase(string[start]) == 0x6E && string[start + 1]
        == 0x2D && all_digits(string, start + 2)
}

/// The base-10 number that `string`, of the form "-" and digits, is from `start`, which is
/// negative: "the remainder interpreted as a base-10 number".
pub open spec fn negative_remainder(string: Seq<u32>, start: int) -> int {
    -digits_value(string.subrange(start + 1, string.len() as int), 0)
}

/// The value of an integer number.
pub open spec fn integer_value(number: Number) -> int {
    number_value(number).0
}

/// `<n-dimension>` and the rest: a `<dimension-token>` with its type flag set to "integer".
pub open spec fn is_integer_dimension(item: ComponentValue) -> bool {
    match item {
        ComponentValue::Token { token: Token::Dimension { number, .. } } => number.is_integer,
        _ => false,
    }
}

/// The value of a `<dimension-token>` with its type flag set to "integer".
pub open spec fn dimension_value(item: ComponentValue) -> int {
    match item {
        ComponentValue::Token { token: Token::Dimension { number, .. } } => integer_value(number),
        _ => 0,
    }
}

/// The unit of a `<dimension-token>`.
pub open spec fn dimension_unit(item: ComponentValue) -> Seq<u32> {
    match item {
        ComponentValue::Token { token: Token::Dimension { unit, .. } } => unit,
        _ => Seq::empty(),
    }
}

/// `<integer>`: a `<number-token>` with its type flag set to "integer".
pub open spec fn integer_number(item: ComponentValue) -> Option<Number> {
    match item {
        ComponentValue::Token { token: Token::Number { number } } => if number.is_integer {
            Some(number)
        } else {
            None
        },
        _ => None,
    }
}

/// `<signed-integer>`, as its value.
pub open spec fn signed_integer(item: ComponentValue) -> Option<int> {
    match integer_number(item) {
        Some(number) => if number.sign_character is Some {
            Some(integer_value(number))
        } else {
            None
        },
        None => None,
    }
}

/// `<signless-integer>`, as its value.
pub open spec fn signless_integer(item: ComponentValue) -> Option<int> {
    match integer_number(item) {
        Some(number) => if number.sign_character is None {
            Some(integer_value(number))
        } else {
            None
        },
        None => None,
    }
}

/// True if `item` is an `<ident-token>` matching `lowercase`, ASCII case-insensitively.
pub open spec fn is_keyword(item: ComponentValue, lowercase: Seq<u32>) -> bool {
    is_ident(item) && ascii_case_insensitive_match(token_value(item), lowercase)
}

/// `<delim-token>` "+".
pub open spec fn is_plus(item: ComponentValue) -> bool {
    is(item, Token::Delim { value: 0x2B })
}

/// `<delim-token>` "-".
pub open spec fn is_minus(item: ComponentValue) -> bool {
    is(item, Token::Delim { value: 0x2D })
}

/// "n".
pub open spec fn n_string() -> Seq<u32> {
    seq![0x6Eu32]
}

/// "n-".
pub open spec fn n_dash_string() -> Seq<u32> {
    seq![0x6Eu32, 0x2D]
}

/// "-n".
pub open spec fn dash_n_string() -> Seq<u32> {
    seq![0x2Du32, 0x6E]
}

/// "-n-".
pub open spec fn dash_n_dash_string() -> Seq<u32> {
    seq![0x2Du32, 0x6E, 0x2D]
}

/// `<n-dimension>`, or `'+'? n`, or `-n`, at the head of `items`, as (A, how many items
/// that took). `plus_adjacent` says whether a "+" has no whitespace after it.
pub open spec fn a_of_n(items: Seq<ComponentValue>, plus_adjacent: bool) -> Option<(int, int)> {
    if items.len() == 0 {
        None
    } else if is_integer_dimension(items[0]) && ascii_case_insensitive_match(
        dimension_unit(items[0]),
        n_string(),
    ) {
        Some((dimension_value(items[0]), 1))
    } else if is_keyword(items[0], n_string()) {
        Some((1, 1))
    } else if is_keyword(items[0], dash_n_string()) {
        Some((-1, 1))
    } else if items.len() >= 2 && is_plus(items[0]) && plus_adjacent && is_keyword(
        items[1],
        n_string(),
    ) {
        Some((1, 2))
    } else {
        None
    }
}

/// `<ndash-dimension>`, or `'+'? n-`, or `-n-`, at the head of `items`, as (A, how many
/// items that took).
pub open spec fn a_of_n_dash(items: Seq<ComponentValue>, plus_adjacent: bool) -> Option<
    (int, int),
> {
    if items.len() == 0 {
        None
    } else if is_integer_dimension(items[0]) && ascii_case_insensitive_match(
        dimension_unit(items[0]),
        n_dash_string(),
    ) {
        Some((dimension_value(items[0]), 1))
    } else if is_keyword(items[0], n_dash_string()) {
        Some((1, 1))
    } else if is_keyword(items[0], dash_n_dash_string()) {
        Some((-1, 1))
    } else if items.len() >= 2 && is_plus(items[0]) && plus_adjacent && is_keyword(
        items[1],
        n_dash_string(),
    ) {
        Some((1, 2))
    } else {
        None
    }
}

/// `items` without its `<whitespace-token>`s: "Whitespace is valid (and ignored) between any
/// other two tokens."
pub open spec fn without_whitespace(items: Seq<ComponentValue>) -> Seq<ComponentValue>
    decreases items.len(),
{
    if items.len() == 0 {
        items
    } else if is_whitespace_token(items.last()) {
        without_whitespace(items.drop_last())
    } else {
        without_whitespace(items.drop_last()).push(items.last())
    }
}

/// The clauses of `<a-n-plus-b>` that are one token or `'+'` and one token, as (A, B).
pub open spec fn single_clause(items: Seq<ComponentValue>, plus_adjacent: bool) -> Option<
    (int, int),
> {
    let plussed = items.len() == 2 && is_plus(items[0]) && plus_adjacent;
    let last = items.last();
    // <ndashdigit-dimension>: "A is the dimension's value. B is the dimension's unit, with
    // the first code point removed and the remainder interpreted as a base-10 number."
    if items.len() == 1 && is_integer_dimension(last) && is_n_dash_digits(
        dimension_unit(last),
        0,
    ) {
        Some((dimension_value(last), negative_remainder(dimension_unit(last), 1)))
    // '+'? <ndashdigit-ident>: "A is 1. B is the ident's value, with the first code point
    // removed and the remainder interpreted as a base-10 number."
    } else if (items.len() == 1 || plussed) && is_ident(last) && is_n_dash_digits(
        token_value(last),
        0,
    ) {
        Some((1, negative_remainder(token_value(last), 1)))
    // <dashndashdigit-ident>: "A is -1. B is the ident's value, with the first two code
    // points removed and the remainder interpreted as a base-10 number."
    } else if items.len() == 1 && is_ident(last) && token_value(last).len() > 0 && token_value(
        last,
    )[0] == 0x2D && is_n_dash_digits(token_value(last), 1) {
        Some((-1, negative_remainder(token_value(last), 2)))
    } else {
        None
    }
}

/// §6.2 "The <a-n-plus-b> type", as a grammar for [`parse_something_according_to_a_css_grammar`],
/// giving (A, B). <https://drafts.csswg.org/css-syntax-3/#the-anb-type>
pub open spec fn a_n_plus_b(value: Seq<ComponentValue>) -> Option<(int, int)> {
    let start = first_non_whitespace(value, 0);
    let plus_adjacent = start + 1 < value.len() && !is_whitespace_token(value[start + 1]);
    a_n_plus_b_items(without_whitespace(value), plus_adjacent)
}

/// The clauses of `<a-n-plus-b>`, on its items without whitespace.
pub open spec fn a_n_plus_b_items(items: Seq<ComponentValue>, plus_adjacent: bool) -> Option<
    (int, int),
> {
    if items.len() == 0 {
        None
    // odd: "A is 2, B is 1."
    } else if items.len() == 1 && is_keyword(items[0], seq![0x6Fu32, 0x64, 0x64]) {
        Some((2, 1))
    // even: "A is 2, B is 0."
    } else if items.len() == 1 && is_keyword(items[0], seq![0x65u32, 0x76, 0x65, 0x6E]) {
        Some((2, 0))
    // <integer>: "A is 0, B is the integer's value."
    } else if items.len() == 1 && integer_number(items[0]) is Some {
        Some((0, integer_value(integer_number(items[0]).unwrap())))
    } else {
        match a_of_n(items, plus_adjacent) {
            Some((a, taken)) if items.len() == taken => {
                // <n-dimension>, '+'? n, -n: "A is the dimension's value, 1, or -1,
                // respectively. B is 0."
                Some((a, 0))
            },
            Some((a, taken)) if items.len() == taken + 1 => {
                // <n-dimension> <signed-integer>, '+'? n <signed-integer>, -n
                // <signed-integer>: "A is the dimension's value, 1, or -1, respectively. B is
                // the integer's value."
                match signed_integer(items.last()) {
                    Some(b) => Some((a, b)),
                    None => None,
                }
            },
            Some((a, taken)) if items.len() == taken + 2 => {
                // <n-dimension> ['+' | '-'] <signless-integer>, and so on: "B is the integer's
                // value. If a '-' was provided between the two, B is instead the negation of
                // the integer's value."
                match signless_integer(items.last()) {
                    Some(b) => if is_plus(items[taken]) {
                        Some((a, b))
                    } else if is_minus(items[taken]) {
                        Some((a, -b))
                    } else {
                        None
                    },
                    None => None,
                }
            },
            Some(_) => None,
            None => match a_of_n_dash(items, plus_adjacent) {
                Some((a, taken)) if items.len() == taken + 1 => {
                    // <ndash-dimension> <signless-integer>, and so on: "B is the negation of
                    // the integer's value."
                    match signless_integer(items.last()) {
                        Some(b) => Some((a, -b)),
                        None => None,
                    }
                },
                _ => single_clause(items, plus_adjacent),
            },
        }
    }
}

// ------------------------------------------------------------------------------------
// §9 Serialization
// ------------------------------------------------------------------------------------

/// The digits of `n`, after the digits `digits`.
pub open spec fn decimal_digits(n: nat, digits: Seq<u32>) -> Seq<u32>
    decreases n,
{
    if n < 10 {
        seq![(0x30 + n) as u32] + digits
    } else {
        decimal_digits(n / 10, seq![(0x30 + n % 10) as u32] + digits)
    }
}

/// "the serialization of" an integer: its base-10 digits, after "-" if it is negative
/// (CSSOM "serialize an <integer>").
pub open spec fn serialize_integer(n: int) -> Seq<u32> {
    if n < 0 {
        seq![0x2Du32] + decimal_digits((-n) as nat, Seq::empty())
    } else {
        decimal_digits(n as nat, Seq::empty())
    }
}

/// §9.1 <https://drafts.csswg.org/css-syntax-3/#serialize-an-anb-value>.
pub open spec fn serialize_a_n_plus_b(a: int, b: int) -> Seq<u32> {
    // 1. "If A is zero, return the serialization of B."
    if a == 0 {
        serialize_integer(b)
    } else {
        // 2. "Otherwise, let result initially be an empty string."
        // 3. "A is 1": "Append "n" to result."
        let result = if a == 1 {
            seq![0x6Eu32]
        // "A is -1": "Append "-n" to result."
        } else if a == -1 {
            seq![0x2Du32, 0x6E]
        // "A is non-zero": "Serialize A and append it to result, then append "n" to result."
        } else {
            serialize_integer(a) + seq![0x6Eu32]
        };
        // 4. "B is greater than zero": "Append "+" to result, then append the serialization
        // of B to result."
        if b > 0 {
            result + seq![0x2Bu32] + serialize_integer(b)
        // "B is less than zero": "Append the serialization of B to result."
        } else if b < 0 {
            result + serialize_integer(b)
        // 5. "Return result."
        } else {
            result
        }
    }
}

/// True for a `<delim-token>` with the value `c`: a single character in the table's
/// headings.
pub open spec fn is_delim(token: Token, c: u32) -> bool {
    token == (Token::Delim { value: c })
}

/// The first nine columns of §9's table that most of its rows mark: ident, function, url,
/// bad url, "-", number, percentage, dimension and CDC.
pub open spec fn is_first_nine(second: Token) -> bool {
    is_word_like(second) || is_delim(second, 0x2D) || is_numeric(second) || second is Cdc
}

/// The columns ident, function, url and bad url.
pub open spec fn is_word_like(second: Token) -> bool {
    second is Ident || second is Function || second is Url || second is BadUrl
}

/// The columns number, percentage and dimension.
pub open spec fn is_numeric(second: Token) -> bool {
    second is Number || second is Percentage || second is Dimension
}

/// §9's table: true if "the pair of tokens must be serialized with a comment between
/// them". <https://drafts.csswg.org/css-syntax-3/#serialization>
pub open spec fn needs_comment_between(first: Token, second: Token) -> bool {
    // Row ident.
    if first is Ident {
        is_first_nine(second) || second is OpenParen
    // Rows at-keyword, hash, dimension, "#" and "-".
    } else if first is AtKeyword || first is Hash || first is Dimension || is_delim(first, 0x23)
        || is_delim(first, 0x2D) {
        is_first_nine(second)
    // Row number.
    } else if first is Number {
        is_word_like(second) || is_numeric(second) || second is Cdc || is_delim(second, 0x25)
    // Row "@".
    } else if is_delim(first, 0x40) {
        is_word_like(second) || is_delim(second, 0x2D) || second is Cdc
    // Rows "." and "+".
    } else if is_delim(first, 0x2E) || is_delim(first, 0x2B) {
        is_numeric(second)
    // Row "/".
    } else if is_delim(first, 0x2F) {
        is_delim(second, 0x2A)
    } else {
        false
    }
}

/// Termination of [`spans_loop`].
#[via_fn]
pub proof fn spans_decreases(
    input: Seq<u32>,
    pos: int,
    unicode_ranges_allowed: bool,
    spans: Seq<Span>,
) {
    crate::tokenizer::termination::lemma_token_advances(input, pos, unicode_ranges_allowed);
}

} // verus!
