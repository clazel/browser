//! Contracts the executable parser and quoter must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`], and the meaning of
//! the tree in [`super::tree`]) is enough to know what the implementation
//! guarantees.
//!
//! Text is `u32` code points, as in `clazel-base64`: vstd has no
//! specification for a safe `u32` to `char` conversion, and supplying one
//! would need `assume_specification`, which is banned (CLAUDE.md rule 4).
//! A JavaScript string is `u16` code units.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `parse(&[u32]) -> Option<Json>`: `None` exactly when
/// ECMA-262 `JSON.parse` would throw a SyntaxError at ParseJSON† step 1, or
/// the text nests deeper than `max_depth()` (a listed deviation), and
/// otherwise a tree whose meaning is the value the spec constructs. There
/// is no precondition: every sequence of `u32` is a candidate text.
pub open spec fn parse_ensures(input: Seq<u32>, output: Option<JsonValue>) -> bool {
    output == json_parse(input)
}

/// Contract for `quote(&[u16]) -> Vec<u16>`: equals QuoteJSONString
/// (§25.5.2.3†). There is no precondition: every string, one with lone
/// surrogates included, can be quoted.
pub open spec fn quote_ensures(value: Seq<u16>, output: Seq<u16>) -> bool {
    output == quote_json_string(value)
}

} // verus!
