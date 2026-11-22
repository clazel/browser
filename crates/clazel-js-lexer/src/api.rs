//! The lexer's public types and its contract-only API.
//!
//! The types are the output of item 7.2: tokens with spans, the values the
//! standard defines for them (identifier code points, string values as
//! UTF-16, template values), and the line-terminator flag automatic
//! semicolon insertion (§12.10) needs. The functions are in [`JsLexer`], a
//! trait with no implementation: each method states its `requires` and
//! `ensures` by the predicates of [`super::contract`], and no body is
//! written, so Verus accepts it with no escape hatch (CLAUDE.md rule 4). The
//! implementation (item 7.2, second half) implements it, or replaces it
//! with free functions whose `requires` and `ensures` are the same
//! predicates.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The value of an input element, where the standard defines one.
pub enum Value {
    /// The element has no value but its span (white space, comments,
    /// punctuators, and so on).
    None,
    /// An `IdentifierName` or `PrivateIdentifier` (the name after the `#`):
    /// its IdentifierCodePoints (§12.7.1.2), with escapes resolved, and
    /// whether it was written with a `UnicodeEscapeSequence`, in which case
    /// it is never a `ReservedWord` (§12.7.2).
    Name {
        /// The code points of the name.
        code_points: Vec<u32>,
        /// Whether any `\` `UnicodeEscapeSequence` was used.
        escaped: bool,
    },
    /// A `StringLiteral`: its SV (§12.9.4.2) as UTF-16 code units, lone
    /// surrogates allowed.
    String {
        /// The code units of the string value.
        units: Vec<u16>,
    },
    /// A template component: its TV (§12.9.6.1), `None` for *undefined*
    /// (an invalid escape sequence, an error unless the template is tagged),
    /// and its TRV (§12.9.6.2).
    Template {
        /// The template value.
        cooked: Option<Vec<u16>>,
        /// The template raw value.
        raw: Vec<u16>,
    },
    /// A `NumericLiteral`. Its value is computed from its span (7.11).
    Numeric {
        /// A BigInt literal (it ends in `BigIntLiteralSuffix`).
        bigint: bool,
        /// A `LegacyOctalIntegerLiteral` or a `NonOctalDecimalIntegerLiteral`
        /// (§12.9.3.1: a Syntax Error in strict mode code).
        legacy: bool,
    },
    /// A `RegularExpressionLiteral`: the index of its closing `/`. BodyText
    /// is `start + 1..body_end` (§12.9.5.1) and FlagText is `body_end +
    /// 1..end` (§12.9.5.2).
    RegExp {
        /// The index of the closing `/`.
        body_end: usize,
    },
}

/// One input element: the longest element of the goal symbol at `start`.
pub struct Element {
    /// What the input element is.
    pub kind: ElementKind,
    /// Its first code point's index in the source text.
    pub start: usize,
    /// One past its last code point's index.
    pub end: usize,
    /// Its value.
    pub value: Value,
}

/// The result of [`JsLexer::next_input_element`] when no error occurs.
pub enum Step {
    /// The end of the source text: there is no input element.
    Eof,
    /// An input element, trivia included.
    Element(Element),
}

/// A token: an input element that is not trivia, with the flag that
/// automatic semicolon insertion (§12.10) needs.
pub struct Token {
    /// The token.
    pub element: Element,
    /// Whether a line terminator precedes the token since the previous one:
    /// a `LineTerminator`, a multi-line comment that contains one, or a
    /// `SingleLineHTMLCloseComment` (§12.3, §12.4, Annex B.1.1).
    pub newline_before: bool,
}

/// The result of [`JsLexer::next_token`] when no error occurs.
pub enum Next {
    /// Only trivia remain before the end of the source text.
    Eof {
        /// Whether the trivia hold a line terminator.
        newline_before: bool,
    },
    /// The next token.
    Token(Token),
}

/// The lexer's contract (CLAUDE.md rule 3): both methods are total, which
/// is to say that for every source text, position and goal symbol the result
/// is determined by [`super::spec`], and there is no precondition but
/// `pos <= src.len()`.
pub trait JsLexer {
    /// The next input element of `goal` at `pos`, trivia included: what the
    /// grammar of `goal` derives at `pos`, taking the longest (§12).
    ///
    /// - **Totality:** every `src`, `pos <= src.len()`, `goal` and `html`
    ///   has a result: `Err` exactly when [`lex_error`] says so, `Eof`
    ///   exactly at `src.len()`, and otherwise an element.
    /// - **Span coverage:** the element starts at `pos`, ends after it and
    ///   within `src`, so repeated calls from each element's `end` tile the
    ///   source text with no gap and no overlap.
    /// - **Agreement:** the element's kind derives the range, no longer
    ///   input element derives a longer one, and the value is the one the
    ///   standard defines.
    fn next_input_element(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Result<
        Step,
        LexError,
    >)
        requires
            crate::contract::next_input_element_requires(src@, pos, goal, html),
        ensures
            crate::contract::next_input_element_ensures(src@, pos, goal, html, r),
    ;

    /// The next token of `goal` at `pos`: skips the trivia (white space,
    /// line terminators, comments) in front of it, with the line-terminator
    /// flag for ASI.
    ///
    /// - **Span coverage:** the skipped trivia are consecutive input elements
    ///   ([`skip_trivia`]), the token follows them, and the next call starts
    ///   at the token's `end`: trivia, then token, then trivia, then token,
    ///   concatenated, are the input.
    fn next_token(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Result<Next, LexError>)
        requires
            crate::contract::next_token_requires(src@, pos, goal, html),
        ensures
            crate::contract::next_token_ensures(src@, pos, goal, html, r),
    ;
}

} // verus!
