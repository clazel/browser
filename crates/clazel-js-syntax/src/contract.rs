//! Contracts the executable parser must be proven to meet. The method of
//! [`super::api::JsParser`] has exactly one `requires` predicate and one
//! `ensures` predicate here, written in terms of [`super::spec`], so reviewing
//! these and the spec is enough to know what the implementation guarantees
//! (docs/SPEC-STYLE.md).
//!
//! The properties of phase-7.md item 7.3, where they are stated:
//!
//! - **Totality:** the `requires` is `true`; the `ensures` determines the result
//!   (`Ok`, or one of the two errors) for every source text and goal: `Ok`
//!   exactly when a valid parse within the limit exists ([`parse_ensures`]:
//!   `Ok` implies one, `Err` implies none).
//! - **Spans inside the input:** [`spans_wf`] and [`ast_wf`] of an `Ok`.
//! - **An `Ok` result satisfies the spec relation:** [`is_valid_parse`], at most
//!   [`MAX_DEPTH`] high.
//! - **An `Err` is a syntax error or the depth limit:** `Syntax` means no valid
//!   parse of any height ([`has_valid_parse`] is false); `TooDeep` means none
//!   within the limit ([`has_valid_parse_within`] is false) and is allowed
//!   only if a deeper one may exist, which the contract does not require.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of `parse`: none. Any `[u32]` (including values above U+10FFFF,
/// which are lexical errors) and either goal symbol is allowed.
pub open spec fn parse_requires(src: Seq<u32>, goal: SourceGoal) -> bool {
    true
}

/// There is a valid parse of `src` as `goal` (a parse by the grammar with no
/// early error), whatever its height.
pub open spec fn has_valid_parse<L: LexerSpec>(src: Seq<u32>, goal: SourceGoal) -> bool {
    exists|a: AstV| is_valid_parse::<L>(src, goal, a)
}

/// There is a valid parse of `src` as `goal` whose height is at most the limit.
pub open spec fn has_valid_parse_within<L: LexerSpec>(src: Seq<u32>, goal: SourceGoal) -> bool {
    exists|a: AstV| is_valid_parse::<L>(src, goal, a) && height(a, a.root) <= MAX_DEPTH as int
}

/// Contract for `parse`: the result is the one the grammar, the early errors,
/// and the depth limit determine.
pub open spec fn parse_ensures<L: LexerSpec>(
    src: Seq<u32>,
    goal: SourceGoal,
    r: Result<crate::ast::Ast, crate::api::ParseError>,
) -> bool {
    match r {
        // A parse: a well-formed arena with every span inside the source text, which is a
        // derivation of a token stream of the source text with no early error, within the limit.
        Ok(ast) => ast_wf(ast@) && spans_wf(ast@, src.len() as int) && is_valid_parse::<L>(
            src,
            goal,
            ast@,
        ) && height(ast@, ast@.root) <= MAX_DEPTH as int,
        // An error: no valid parse within the limit; `Syntax` is no valid parse at all.
        Err(e) => !has_valid_parse_within::<L>(src, goal) && (e == crate::api::ParseError::Syntax
            ==> !has_valid_parse::<L>(src, goal)),
    }
}

} // verus!
