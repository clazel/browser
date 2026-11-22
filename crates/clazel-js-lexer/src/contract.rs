//! Contracts the executable lexer must be proven to meet. Each method of
//! [`super::api::JsLexer`] has exactly one `requires` predicate and one
//! `ensures` predicate here, written in terms of [`super::spec`], so
//! reviewing these and the spec is enough to know what the implementation
//! guarantees (docs/SPEC-STYLE.md).
//!
//! The properties of phase-7.md item 7.2, where they are stated:
//!
//! - **Totality:** the `requires` is `pos <= src.len()` and nothing else;
//!   the `ensures` determines the result (`Err`, end of input, or an
//!   element) for every case, by [`lex_error`] and [`longest_len`].
//! - **Span coverage:** `start == pos`, `pos < end <= src.len()` for an
//!   element; for a token, the trivia before it are [`skip_trivia`]'s
//!   elements, which are consecutive and end at the token's `start`.
//! - **Agreement with spec.rs:** the kind derives the range
//!   ([`element_matches`]), the length is [`longest_len`], the errors are
//!   [`lex_error`], the values are the relations of [`super::spec`], and the
//!   line-terminator flag is [`skip_trivia`]'s.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of `next_input_element`: the position is inside the source
/// text or at its end. Any `[u32]`, any goal and either `html` is allowed.
pub open spec fn next_input_element_requires(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
) -> bool {
    pos <= src.len()
}

/// Whether the value of an element is the one the standard defines for its
/// kind and range (§12.7.1.2 IdentifierCodePoints, §12.9.4.2 SV, §12.9.6.1
/// TV, §12.9.6.2 TRV), and the element has a `Value` exactly when its kind
/// has one.
pub open spec fn element_value_agrees(src: Seq<u32>, el: crate::api::Element) -> bool {
    let i = el.start as int;
    let j = el.end as int;
    match el.value {
        crate::api::Value::None => !(el.kind == ElementKind::IdentifierName
            || el.kind == ElementKind::PrivateIdentifier
            || el.kind == ElementKind::StringLiteral
            || el.kind == ElementKind::NumericLiteral
            || el.kind == ElementKind::RegularExpressionLiteral
            || el.kind == ElementKind::Template(TemplateKind::NoSubstitution)
            || el.kind == ElementKind::Template(TemplateKind::Head)
            || el.kind == ElementKind::Template(TemplateKind::Middle)
            || el.kind == ElementKind::Template(TemplateKind::Tail)),
        crate::api::Value::Name { code_points, escaped } => {
            (el.kind == ElementKind::IdentifierName && identifier_name_cps(
                src,
                i,
                j,
                code_points@,
            ) && escaped == identifier_has_escape(src, i, j))
                || (el.kind == ElementKind::PrivateIdentifier && identifier_name_cps(
                src,
                i + 1,
                j,
                code_points@,
            ) && escaped == identifier_has_escape(src, i + 1, j))
        },
        crate::api::Value::String { units } => el.kind == ElementKind::StringLiteral && string_literal_sv(
            src,
            i,
            j,
            units@,
        ),
        crate::api::Value::Template { cooked, raw } => match el.kind {
            ElementKind::Template(k) => template_part(
                src,
                i,
                j,
                k,
                match cooked {
                    Some(c) => Some(c@),
                    None => None,
                },
                raw@,
            ),
            _ => false,
        },
        crate::api::Value::Numeric { bigint, legacy } => el.kind == ElementKind::NumericLiteral
            && bigint == numeric_literal_is_bigint(src, i, j)
            && legacy == numeric_literal_is_legacy(src, i, j),
        crate::api::Value::RegExp { body_end } => el.kind == ElementKind::RegularExpressionLiteral
            && regexp_literal(src, i, j, body_end as int),
    }
}

/// Contract for `next_input_element`: the result is the one the grammar and
/// §12's longest-element rule determine.
pub open spec fn next_input_element_ensures(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<crate::api::Step, LexError>,
) -> bool {
    match r {
        // An error exactly when `lex_error` says so (which is `None` at the
        // end of the source text).
        Err(e) => lex_error(goal, html, src, pos as int) == Some(e),
        // The end of the source text: there is no element.
        Ok(crate::api::Step::Eof) => pos == src.len(),
        Ok(crate::api::Step::Element(el)) => {
            pos < src.len() && lex_error(goal, html, src, pos as int) is None
                // Span coverage: the element is the range [pos, end), and
                // the longest input element of the goal at pos.
                 && el.start == pos && pos < el.end && el.end <= src.len() && el.end as int
                == pos + longest_len(goal, html, src, pos as int)
                // Agreement: the kind derives the range, and the value is
                // the standard's.
                 && element_matches(goal, html, el.kind, src, pos as int, el.end as int)
                && element_value_agrees(src, el)
        },
    }
}

/// Precondition of `next_token`: as for `next_input_element`.
pub open spec fn next_token_requires(src: Seq<u32>, pos: usize, goal: Goal, html: bool) -> bool {
    pos <= src.len()
}

/// Contract for `next_token`: skip trivia ([`skip_trivia`]), then lex one
/// element; the line-terminator flag is the trivia's.
pub open spec fn next_token_ensures(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<crate::api::Next, LexError>,
) -> bool {
    let skipped = skip_trivia(goal, html, src, pos as int);
    let t = skipped.0;
    let newline = skipped.1;
    match r {
        // The error of the first element that is not trivia.
        Err(e) => lex_error(goal, html, src, t) == Some(e),
        // Only trivia remain.
        Ok(crate::api::Next::Eof { newline_before }) => t == src.len() && newline_before == newline,
        Ok(crate::api::Next::Token(tok)) => {
            t < src.len() && 0 <= t && tok.newline_before == newline && !is_trivia(
                tok.element.kind,
            )
                && next_input_element_ensures(
                src,
                t as usize,
                goal,
                html,
                Ok(crate::api::Step::Element(tok.element)),
            )
        },
    }
}

} // verus!
