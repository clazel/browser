//! The parser's public types and its contract-only API.
//!
//! The function is in [`JsParser`], a trait with no implementation: the method
//! states its `requires` and `ensures` by the predicates of
//! [`super::contract`], and no body is written, so Verus accepts it with no
//! escape hatch (CLAUDE.md rule 4), the pattern of `clazel-js-lexer`'s `api.rs`.
//! The implementation (item 7.3, second half) implements it, or replaces it
//! with a free function whose `requires` and `ensures` are the same predicates.
//!
//! The parser drives a lexer (§12: the syntactic grammar chooses the goal symbol
//! of every token), so the trait is generic in the lexer's specification
//! [`LexerSpec`]: what the parser promises is relative to what the lexer
//! promises. The implementation names `clazel-js-lexer`'s as the model of
//! [`LexerSpec`]; this crate does not depend on it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Why a source text was not parsed.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ParseError {
    /// The source text is not a valid `Script` or `Module`: it has a lexical error,
    /// is not derived by the grammar, or has an early error (§16.1.1, §16.2.1.1 and
    /// the rules they name). Raised as a `SyntaxError` by `eval`, `new Function`,
    /// `import()` and the like.
    Syntax,
    /// The source text is nested more deeply than [`MAX_DEPTH`] (the deviation
    /// of phase-7.md item 7.3): no parse of it is that low. The embedder reports it
    /// as a `SyntaxError` too.
    TooDeep,
}

/// The parser's contract (CLAUDE.md rule 3): the function is total: for every
/// source text and goal symbol the result is determined by [`super::spec`],
/// and there is no precondition.
pub trait JsParser<L: LexerSpec> {
    /// Parses `src` (code points, §11.1) as a `Script` or `Module`.
    ///
    /// - **Totality:** every `src` and `goal` has a result, and nothing it does
    ///   depends on anything but them.
    /// - **Spans inside the input:** the arena is well formed (the root is the last
    ///   node, every child is before its parent), and every span, and every child's
    ///   span in its parent's, is inside `0..src.len()`.
    /// - **Ok is a parse:** the arena is a derivation of a token stream of `src` from
    ///   the goal symbol (semicolon insertion included), with no early error, and at
    ///   most `MAX_DEPTH` high.
    /// - **Err is a syntax error or the depth limit:** `Err` only when there is no
    ///   parse of `src` that is within the limit, and `Syntax` only when there is no
    ///   parse of it at all.
    fn parse(src: &[u32], goal: SourceGoal) -> (r: Result<crate::ast::Ast, ParseError>)
        requires
            crate::contract::parse_requires(src@, goal),
        ensures
            crate::contract::parse_ensures::<L>(src@, goal, r),
    ;
}

} // verus!
