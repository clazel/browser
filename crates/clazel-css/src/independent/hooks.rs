//! The inputs of the parser entry points other than a string (§5.3.1 "normalize
//! into a token stream", steps 2 and 3, and the entry points on them), and the
//! "parse according to a grammar" hooks (§5.3.2 "Parse something according to a CSS
//! grammar" and §5.3.3 "Parse a comma-separated list according to a CSS grammar"),
//! transcribed from the standard alone; see the header of [`super`] for the text
//! and the modelling choices that this file shares.
//!
//! ## Modelling choices
//!
//! - An input is a string of code points, a list of tokens, or a list of component
//!   values ([`IInput`]). Step 1 of "normalize" ("If |input| is already a token
//!   stream, return it") is not a separate input: every algorithm already works on
//!   a token stream.
//! - A list of tokens becomes a token stream "with |input| as its tokens"
//!   ([`i_lex_tokens`]): the stream has no source string, so the position of every
//!   token is 0. Only the three entry points that never read the source string are
//!   defined on a list of tokens (parse a component value, parse a list of component
//!   values, parse a comma-separated list of component values): the "original text" of
//!   a declaration and the unicode-range value of a descriptor, which the other four
//!   entry points read from the source, have no source in a list of tokens, and what
//!   the algorithms do then is left out here.
//! - A list of component values is a stream whose items are already component
//!   values, so "consume a component value" returns the item at the index as it
//!   is. This is what the standard leaves out (it says "tokens and/or component
//!   values" and then consumes tokens). Only the three entry points that read
//!   component values and nothing else are defined on such a list (parse a
//!   component value, parse a list of component values, parse a comma-separated
//!   list of component values): the others (rules, declarations) read tokens that
//!   a component value cannot be split back into.
//! - "Attempt to match |result| against |grammar|" is `grammar(result)`, a
//!   function from a list of component values to the matched result or `None`
//!   (failure); the matched result is of any type `G` ("an unspecified
//!   structure"). Failure is `None` and not a `G`.
//! - "If |input| contains only `<whitespace-token>`s" is tested on the normalized
//!   input: its tokens, or its component values.

use super::parse::*;
use super::*;

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An |input| of an entry point: "a string", "a list of CSS tokens", or "a list of
/// CSS component values".
pub ghost enum IInput {
    /// A string, as code points.
    Str(Seq<int>),
    /// A list of tokens.
    Tokens(Seq<ITok>),
    /// A list of component values.
    Values(Seq<ICv>),
}

/// "create a new token stream with |input| as its tokens", for a list of tokens:
/// a token and a position 0 each (see the header).
pub open spec fn i_lex_tokens(ts: Seq<ITok>) -> Seq<Lex> {
    ts.map_values(|t: ITok| Lex { tok: t, start: 0, end: 0 })
}

// ---------------------------------------------------------------------
// The entry points on a list of tokens

/// "parse a component value" of a list of tokens.
pub open spec fn i_tokens_parse_component_value(ts: Seq<ITok>) -> IParsed<ICv> {
    i_parse_component_value_of(i_lex_tokens(ts))
}

/// "parse a list of component values" of a list of tokens.
pub open spec fn i_tokens_parse_list_of_component_values(ts: Seq<ITok>) -> Seq<ICv> {
    i_parse_list_of_component_values_of(i_lex_tokens(ts))
}

/// "parse a comma-separated list of component values" of a list of tokens.
pub open spec fn i_tokens_parse_comma_separated_list_of_component_values(ts: Seq<ITok>) -> Seq<Seq<ICv>> {
    i_parse_comma_separated_list_of_component_values_of(i_lex_tokens(ts))
}

// ---------------------------------------------------------------------
// The entry points on a list of component values

/// The index of the first item of `vs` from `p` on that is not a
/// `<whitespace-token>`: "discard whitespace".
pub open spec fn i_values_discard_whitespace(vs: Seq<ICv>, p: nat) -> nat
    decreases (if vs.len() > p { vs.len() - p } else { 0 }),
{
    if p < vs.len() && vs[p as int] == ICv::Token(ITok::Whitespace) {
        i_values_discard_whitespace(vs, p + 1)
    } else {
        p
    }
}

/// "parse a component value" of a list of component values: "Discard whitespace
/// from |input|. If |input| is empty, return a syntax error. Consume a component
/// value from |input| and let |value| be the return value. Discard whitespace from
/// |input|. If |input| is empty, return |value|. Otherwise, return a syntax error."
pub open spec fn i_values_parse_component_value(vs: Seq<ICv>) -> IParsed<ICv> {
    let p = i_values_discard_whitespace(vs, 0);
    if p >= vs.len() {
        IParsed::SyntaxError
    } else if i_values_discard_whitespace(vs, p + 1) >= vs.len() {
        IParsed::Value(vs[p as int])
    } else {
        IParsed::SyntaxError
    }
}

/// "parse a list of component values" of a list of component values: every item is
/// consumed as a component value, so the list is the list.
pub open spec fn i_values_parse_list_of_component_values(vs: Seq<ICv>) -> Seq<ICv> { vs }

/// "parse a comma-separated list of component values" of a list of component
/// values.
pub open spec fn i_values_parse_comma_separated_list_of_component_values(vs: Seq<ICv>) -> Seq<Seq<ICv>> {
    i_values_comma_split(vs, 0, seq![], seq![])
}

/// The loop of "parse a comma-separated list of component values" on a list of
/// component values: "While |input| is not empty: consume a list of component
/// values from |input|, with a `<comma-token>` as the stop token", the comma
/// being discarded with it. The group being collected and the groups so far; the
/// group that runs to the end is a group when it has an item (the loop ends when
/// the input is empty after a comma).
pub open spec fn i_values_comma_split(vs: Seq<ICv>, p: nat, group: Seq<ICv>, groups: Seq<Seq<ICv>>) -> Seq<Seq<ICv>>
    decreases (if vs.len() > p { vs.len() - p } else { 0 }),
{
    if p >= vs.len() {
        if group.len() > 0 { groups + seq![group] } else { groups }
    } else if vs[p as int] == ICv::Token(ITok::Comma) {
        i_values_comma_split(vs, p + 1, seq![], groups + seq![group])
    } else {
        i_values_comma_split(vs, p + 1, group + seq![vs[p as int]], groups)
    }
}

// ---------------------------------------------------------------------
// §5.3.2 and §5.3.3: the grammar hooks

/// "parse a list of component values" of a normalized |input|.
pub open spec fn i_input_values(input: IInput) -> Seq<ICv> {
    match input {
        IInput::Str(s) => i_parse_list_of_component_values(s),
        IInput::Tokens(ts) => i_tokens_parse_list_of_component_values(ts),
        IInput::Values(vs) => i_values_parse_list_of_component_values(vs),
    }
}

/// "parse a comma-separated list of component values" of a normalized |input|.
pub open spec fn i_input_groups(input: IInput) -> Seq<Seq<ICv>> {
    match input {
        IInput::Str(s) => i_parse_comma_separated_list_of_component_values(s),
        IInput::Tokens(ts) => i_tokens_parse_comma_separated_list_of_component_values(ts),
        IInput::Values(vs) => i_values_parse_comma_separated_list_of_component_values(vs),
    }
}

/// "If |input| contains only `<whitespace-token>`s", of a normalized |input|.
pub open spec fn i_input_only_whitespace(input: IInput) -> bool {
    match input {
        IInput::Str(s) => forall|k: int| 0 <= k < i_normalize(s).0.len() ==> i_normalize(s).0[k].tok == ITok::Whitespace,
        IInput::Tokens(ts) => forall|k: int| 0 <= k < ts.len() ==> ts[k] == ITok::Whitespace,
        IInput::Values(vs) => forall|k: int| 0 <= k < vs.len() ==> vs[k] == ICv::Token(ITok::Whitespace),
    }
}

/// §5.3.2 "parse something according to a CSS grammar", given an |input| and a
/// |grammar|: "1. Normalize |input|, and set |input| to the result. 2. Parse a list
/// of component values from |input|, and let |result| be the return value. 3.
/// Attempt to match |result| against |grammar|. If this is successful, return the
/// matched result; otherwise, return failure."
pub open spec fn i_parse_grammar<G>(input: IInput, grammar: spec_fn(Seq<ICv>) -> Option<G>) -> Option<G> {
    grammar(i_input_values(input))
}

/// §5.3.3 "parse a comma-separated list according to a CSS grammar", given an
/// |input| and a |grammar|: "1. Normalize |input|, and set |input| to the result. 2.
/// If |input| contains only `<whitespace-token>`s, return an empty list. 3. Parse a
/// comma-separated list of component values from |input|, and let |list| be the
/// return value. 4. For each |item| of |list|, replace |item| with the result of
/// parsing |item| with |grammar|. 5. Return |list|."
pub open spec fn i_parse_list_grammar<G>(input: IInput, grammar: spec_fn(Seq<ICv>) -> Option<G>) -> Seq<Option<G>> {
    if i_input_only_whitespace(input) {
        seq![]
    } else {
        i_input_groups(input).map_values(|item: Seq<ICv>| grammar(item))
    }
}

} // verus!
