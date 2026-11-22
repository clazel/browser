//! The executable lexer (phase-7.md item 7.2, second half).
//!
//! Each `scan_` function reads one production of [`super::spec`] at a
//! position, as a loop with no recursion (a script is what a page chose;
//! Verus proves no panic, not no stack overflow), and returns where it
//! ends. [`next_input_element`] dispatches on the first code point, takes
//! the longest of the alternatives that can start there (§12), and then
//! applies the two checks the spec makes after the longest element is
//! chosen ([`lex_error`]); [`next_token`] repeats it over trivia.
//!
//! # What is proven, and what is not
//!
//! Verus proves, for every input, with no escape hatch:
//!
//! - **Totality:** every function terminates (each loop has a `decreases`)
//!   and never panics: no index out of range, no overflow.
//! - **Span coverage:** [`next_input_element_proven`]: the end of the
//!   source text gives `Eof`, and nothing else does; an element starts at
//!   `pos`, ends after it and inside the source text; so elements from
//!   repeated calls tile the source text. [`next_token_proven`]: the token
//!   starts at or after `pos`, is not trivia, and its `newline_before` is
//!   exactly [`contains_line_terminator`] of the code points between `pos`
//!   and the token, which is [`skip_trivia`]'s flag for the range it skips
//!   ([`super::lemmas::lemma_skip_trivia_flag`]).
//! - **The value's shape:** [`value_shape_agrees`]: an element has the
//!   kind of `Value` its kind has (a `StringLiteral` a `Value::String`, and
//!   so on), and a regular expression's `body_end` is inside it.
//! - **Agreement with the spec, for the kinds of [`kind_proven`]:**
//!   [`kind_agrees_proven`]: the element's kind derives its range in the
//!   goal ([`element_matches`]), and no longer range inside the source text
//!   is derived by an element of that kind. The kinds are `WhiteSpace`,
//!   `LineTerminator`, `HashbangComment`, `DivPunctuator`,
//!   `RightBracePunctuator`, `Punctuator`, `NumericLiteral`,
//!   `StringLiteral`, and `Comment` outside Annex B's `html` mode (a `//`
//!   or `/* */` comment).
//! - **Values, for the kinds of [`value_proven`]:** [`value_agrees_proven`]:
//!   a `NumericLiteral`'s `bigint` and `legacy` flags and a
//!   `StringLiteral`'s SV are the spec's relations
//!   ([`super::contract::element_value_agrees`]).
//! - **Longest match across the proven kinds** ([`proven_bounded`]): when
//!   the element is of a [`kind_proven`] kind, no derivation, from `pos`, of
//!   any other proven kind is longer; and when the result is
//!   [`LexError::NoInputElement`], no proven kind derives anything at `pos`.
//!   Each branch of the dispatch on the first code point (`lex_ws`,
//!   `lex_lt`, `lex_slash`, `lex_brace`, `lex_backtick`, `lex_string`,
//!   `lex_hash`, `lex_numeric`, `lex_ident`, `lex_html_open`, `lex_punct`)
//!   proves it from the code points each kind can start with
//!   ([`super::longest_proofs::start_ok`], `lemma_first_cp`).
//! - **The contract, for a proven kind, given what is not proven**
//!   ([`lemma_element_meets_contract`]): if no derivation of a kind that is
//!   not proven ([`super::longest_proofs::unproven_bounded`]: identifiers,
//!   private identifiers, regular expression literals, templates, and in
//!   `html` mode comments) is as long as the element, then
//!   [`super::contract::next_input_element_ensures`] holds for it in full
//!   (the longest length, the errors of [`lex_error`], the value), except
//!   that for a `NumericLiteral` the code point after it must be below
//!   U+0080 or absent ([`numeric_follow_error`] is proven to be the spec's
//!   [`super::spec::numeric_literal_follow_error`] only then).
//!   [`lemma_no_input_element_meets_contract`] and
//!   [`lemma_numeric_error_meets_contract`] do the same for
//!   [`LexError::NoInputElement`] and
//!   [`LexError::IdentifierAfterNumericLiteral`].
//! - **The scanners that carry these:** `scan_punctuator`, `scan_numeric`
//!   (with `scan_digits_sep`, `scan_exponent`, `scan_decimal_tail`),
//!   `scan_string` (with `scan_string_escape`, `scan_legacy_octal_escape`,
//!   `scan_unicode_escape`, `scan_hex_digits`, `scan_hex4`) and
//!   `scan_block_comment` each state, in their `ensures`, that the end they
//!   return is a range the spec derives, that no longer range is, and that
//!   `None` means the spec derives none. The proofs reduce the spec's
//!   productions to the closed forms of [`super::independent`] through
//!   [`super::equivalence`], and reason about the closed forms in
//!   [`super::scan_proofs`] and [`super::string_proofs`].
//! - **Single code points:** the classifiers (`is_ws`, `is_lt`, the digit
//!   classes, `hex_val`) equal the spec's, and `push_utf16` is
//!   UTF16EncodeCodePoint (§11.1.1).
//!
//! It is **not** proven that the results agree with [`super::spec`]
//! otherwise, so these functions do not implement [`super::api::JsLexer`]:
//!
//! - **Longest element against the unproven kinds** ([`longest_len`]): that
//!   no element of a kind that is not proven is as long as the one returned
//!   (the hypothesis of [`lemma_element_meets_contract`]). Nothing here
//!   discharges it, not even where the first code point is ASCII and rules
//!   an identifier out.
//! - **The errors** of [`lex_error`]: [`LexError::InvalidIdentifierEscape`]
//!   (identifiers); [`LexError::IdentifierAfterNumericLiteral`] when the
//!   code point after the literal is above U+007F (see below).
//! - **`newline_before` being [`skip_trivia`]'s**: the flag is proven to be
//!   the line terminators in the range, and [`skip_trivia`]'s to be the same
//!   for its range; that the two ranges end at the same place is the
//!   longest-match property for each trivia element, which holds only given
//!   the hypothesis above.
//! - **Annex B.1.1 comments** (`html` mode: `<!--`, `-->`, a multi-line
//!   comment with an `HTMLCloseComment`): `Comment` is claimed only with
//!   `html == false`. Not done: it needs the determinism of
//!   `HTMLCloseComment`'s split (its `WhiteSpaceSequence?` and
//!   `SingleLineDelimitedCommentSequence?` before `-->`) and the longest
//!   range of an Annex B `MultiLineComment` followed by one.
//! - **Identifiers and private identifiers, regular expression literals
//!   (their flags are `IdentifierPartChar`s), the `ReservedWord` rule, and
//!   the checks that read `IdentifierStart`**: nothing ties the table of
//!   [`super::unicode`] to the spec's uninterpreted `ID_Start` and
//!   `ID_Continue` of code points above U+007F
//!   ([`super::spec::unicode_id_start_non_ascii`]), so the agreement of
//!   anything that tests them cannot be stated until it is tied (an axiom
//!   in an `axioms.rs`, CLAUDE.md rule 4, or an interpretation of the spec).
//! - **Template literals** (their ranges, TV and TRV). Blocked by a proof
//!   obstacle in [`super::spec`], not a lexing one: see
//!   [`super::template_proofs`]. What it proves is that a
//!   `TemplateCharacter` has one length and value and that none starts at a
//!   closing delimiter.
//!
//! Their agreement with the spec is tested (`tests/`), not proven.
//! [`lemma_contract_implies_proven`] shows that what is proven is implied
//! by the full contract.
//!
//! Non-ASCII `ID_Start` and `ID_Continue` come from [`super::unicode`],
//! which the spec leaves uninterpreted: nothing is claimed about them.

#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::ident_proofs::*;
#[cfg(verus_only)]
use super::independent::*;
#[cfg(verus_only)]
use super::longest_proofs::*;
#[cfg(verus_only)]
use super::scan_proofs::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::string_proofs::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::api::{Element, Next, Step, Token, Value};

verus! {

// ---------------------------------------------------------------------
// What the executable lexer is proven to satisfy.
// ---------------------------------------------------------------------

/// The kind of [`Value`] an element has is the one its kind has (the shape
/// of [`super::contract::element_value_agrees`], not the values), and a
/// regular expression's closing `/` is inside it, after a non-empty body.
pub open spec fn value_shape_agrees(el: Element) -> bool {
    match el.value {
        Value::None => !(el.kind == ElementKind::IdentifierName
            || el.kind == ElementKind::PrivateIdentifier || el.kind == ElementKind::StringLiteral
            || el.kind == ElementKind::NumericLiteral
            || el.kind == ElementKind::RegularExpressionLiteral
            || el.kind == ElementKind::Template(TemplateKind::NoSubstitution)
            || el.kind == ElementKind::Template(TemplateKind::Head)
            || el.kind == ElementKind::Template(TemplateKind::Middle)
            || el.kind == ElementKind::Template(TemplateKind::Tail)),
        Value::Name { .. } => el.kind == ElementKind::IdentifierName || el.kind
            == ElementKind::PrivateIdentifier,
        Value::String { .. } => el.kind == ElementKind::StringLiteral,
        Value::Template { .. } => el.kind == ElementKind::Template(TemplateKind::NoSubstitution)
            || el.kind == ElementKind::Template(TemplateKind::Head) || el.kind
            == ElementKind::Template(TemplateKind::Middle) || el.kind == ElementKind::Template(
            TemplateKind::Tail,
        ),
        Value::Numeric { .. } => el.kind == ElementKind::NumericLiteral,
        Value::RegExp { body_end } => el.kind == ElementKind::RegularExpressionLiteral
            && el.start + 1 < body_end < el.end,
    }
}

/// The code points of a `Name` value (empty for any other).
pub open spec fn value_name_cps(v: Value) -> Seq<u32> {
    match v {
        Value::Name { code_points, .. } => code_points@,
        _ => Seq::empty(),
    }
}

/// The kinds whose agreement with the spec is proven (see
/// [`kind_agrees_proven`]).
pub open spec fn kind_proven(kind: ElementKind, html: bool) -> bool {
    kind == ElementKind::WhiteSpace || kind == ElementKind::LineTerminator || kind
        == ElementKind::HashbangComment || kind == ElementKind::DivPunctuator || kind
        == ElementKind::RightBracePunctuator || kind == ElementKind::Punctuator || (kind
        == ElementKind::Comment && !html) || kind == ElementKind::NumericLiteral || kind
        == ElementKind::StringLiteral || kind == ElementKind::IdentifierName || kind
        == ElementKind::PrivateIdentifier
}

/// The kinds whose value is proven to be the spec's
/// ([`super::contract::element_value_agrees`]).
pub open spec fn value_proven(kind: ElementKind) -> bool {
    kind == ElementKind::NumericLiteral || kind == ElementKind::StringLiteral || kind
        == ElementKind::IdentifierName || kind == ElementKind::PrivateIdentifier
}

/// For the kinds of [`value_proven`], the value is the one the standard
/// defines for the range.
pub open spec fn value_agrees_proven(src: Seq<u32>, el: Element) -> bool {
    value_proven(el.kind) ==> super::contract::element_value_agrees(src, el)
}

/// For the kinds of [`kind_proven`], the kind derives the element's range
/// in the goal ([`element_matches`], one conjunct of
/// [`super::contract::next_input_element_ensures`]), and no longer range
/// inside the source text is derived by an element of that kind. (Not that
/// no element of another kind is longer: that is [`longest_len`], which is
/// not proven.) For the other kinds nothing is claimed here.
pub open spec fn kind_agrees_proven(goal: Goal, html: bool, src: Seq<u32>, el: Element) -> bool {
    kind_proven(el.kind, html) ==> (element_matches(
        goal,
        html,
        el.kind,
        src,
        el.start as int,
        el.end as int,
    ) && forall|j: int|
        j <= src.len() && #[trigger] element_matches(goal, html, el.kind, src, el.start as int, j)
            ==> j <= el.end)
}

/// What [`next_input_element`] is proven to return: totality, span
/// coverage, the value's shape, and the derivation of the simple kinds. A
/// weakening of [`super::contract::next_input_element_ensures`]
/// ([`lemma_contract_implies_proven`]).
pub open spec fn next_input_element_proven(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<Step, LexError>,
) -> bool {
    match r {
        Err(e) => pos < src.len() && (e == LexError::NoInputElement ==> proven_bounded(
            goal,
            html,
            src,
            pos as int,
            pos as int,
        )) && (e == LexError::IdentifierAfterNumericLiteral ==> exists|end: int|
            pos < end <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::NumericLiteral,
                src,
                pos as int,
                end,
            ) && proven_bounded(goal, html, src, pos as int, end) && numeric_literal_follow_error(
                src,
                end,
            )) && (e == LexError::InvalidIdentifierEscape ==> exists|end: int|
            pos < end <= src.len() && proven_bounded(goal, html, src, pos as int, end)
                && numeric_absent(src, pos as int) && #[trigger] invalid_identifier_at(
                goal,
                html,
                src,
                pos as int,
                end,
            )),
        Ok(Step::Eof) => pos == src.len(),
        Ok(Step::Element(el)) => pos < src.len() && el.start == pos && pos < el.end && el.end
            <= src.len() && value_shape_agrees(el) && kind_agrees_proven(goal, html, src, el)
            && value_agrees_proven(src, el) && (kind_proven(el.kind, html) ==> proven_bounded(
            goal,
            html,
            src,
            pos as int,
            el.end as int,
        )) && (kind_proven(el.kind, html) && el.kind != ElementKind::NumericLiteral
            ==> numeric_absent(src, pos as int)) && (el.kind == ElementKind::NumericLiteral
            ==> !numeric_literal_follow_error(src, el.end as int)) && (kind_proven(el.kind, html)
            && el.kind != ElementKind::IdentifierName ==> ident_absent(src, pos as int)) && (
        kind_proven(el.kind, html) && el.kind != ElementKind::PrivateIdentifier ==> private_absent(
            src,
            pos as int,
        )) && (el.kind == ElementKind::IdentifierName ==> identifier_name_valid(
            src,
            pos as int,
            el.end as int,
        )) && (el.kind == ElementKind::PrivateIdentifier ==> identifier_name_valid(
            src,
            pos as int + 1,
            el.end as int,
        )),
    }
}

/// An identifier or private identifier over `pos..end` with an early error
/// (§12.7.1.1), and no other kind of that error possible at `pos`.
pub open spec fn invalid_identifier_at(
    goal: Goal,
    html: bool,
    src: Seq<u32>,
    pos: int,
    end: int,
) -> bool {
    (element_matches(goal, html, ElementKind::IdentifierName, src, pos, end)
        && !identifier_name_valid(src, pos, end) && private_absent(src, pos))
        || (element_matches(goal, html, ElementKind::PrivateIdentifier, src, pos, end)
        && !identifier_name_valid(src, pos + 1, end) && ident_absent(src, pos))
}

/// What [`next_token`] is proven to return: the token is after `pos`,
/// inside the source text and not trivia, and the flag is exactly whether a
/// line terminator code point is between `pos` and the token (which is
/// [`skip_trivia`]'s flag for the trivia that end there, by
/// [`super::lemmas::lemma_skip_trivia_flag`]; that the trivia end where
/// [`skip_trivia`] says is the longest-match property, not proven).
pub open spec fn next_token_proven(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<Next, LexError>,
) -> bool {
    match r {
        Err(e) => pos < src.len(),
        Ok(Next::Eof { newline_before }) => newline_before == contains_line_terminator(
            src,
            pos as int,
            src.len() as int,
        ),
        Ok(Next::Token(tok)) => pos <= tok.element.start < tok.element.end <= src.len()
            && !is_trivia(tok.element.kind) && value_shape_agrees(tok.element)
            && kind_agrees_proven(goal, html, src, tok.element) && value_agrees_proven(
            src,
            tok.element,
        ) && (kind_proven(tok.element.kind, html) ==> proven_bounded(
            goal,
            html,
            src,
            tok.element.start as int,
            tok.element.end as int,
        )) && tok.newline_before == contains_line_terminator(
            src,
            pos as int,
            tok.element.start as int,
        ),
    }
}

/// The full contract implies what is proven of [`next_input_element`]
/// about the spec (except the value's shape, which the full contract states
/// value by value, and the facts about the dispatch that
/// [`next_input_element_proven`] also carries to prove the above:
/// `numeric_absent` and the numeric follow check): the proven part is a
/// weakening, not a different claim. ([`kind_agrees_proven`] is the
/// contract's `element_matches` conjunct itself, restricted to some kinds;
/// [`proven_bounded`] is what the contract's longest length says of the
/// proven kinds.)
pub proof fn lemma_contract_implies_proven(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Result<Step, LexError>,
)
    requires
        pos <= src.len(),
        super::contract::next_input_element_ensures(src, pos, goal, html, r),
    ensures
        match r {
            Err(e) => pos < src.len() && (e == LexError::NoInputElement ==> proven_bounded(
                goal,
                html,
                src,
                pos as int,
                pos as int,
            )),
            Ok(Step::Eof) => pos == src.len(),
            Ok(Step::Element(el)) => pos < src.len() && el.start == pos && pos < el.end && el.end
                <= src.len() && kind_agrees_proven(goal, html, src, el) && value_agrees_proven(
                src,
                el,
            ) && (kind_proven(el.kind, html) ==> proven_bounded(
                goal,
                html,
                src,
                pos as int,
                el.end as int,
            )),
        },
{
    super::lemmas::lemma_longest_len(goal, html, src, pos as int);
    if let Err(LexError::NoInputElement) = r {
        // The longest length is 0: no range, so no kind, derives anything.
        assert forall|k: ElementKind, j: int|
            pos < j <= src.len() && #[trigger] element_matches(goal, html, k, src, pos as int, j)
                implies j <= pos by {
            super::lemmas::lemma_kind_implies_any(goal, html, k, src, pos as int, j);
            let n = j - pos as int;
            assert(pos as int + n == j);
            assert(any_element_matches(goal, html, src, pos as int, pos as int + n));
        }
    }
    if let Ok(Step::Element(el)) = r {
        assert forall|k: ElementKind, j: int|
            pos < j <= src.len() && #[trigger] element_matches(goal, html, k, src, pos as int, j)
                implies j <= el.end by {
            super::lemmas::lemma_kind_implies_any(goal, html, k, src, pos as int, j);
            let n = j - pos as int;
            assert(pos as int + n == j);
            assert(any_element_matches(goal, html, src, pos as int, pos as int + n));
        }
        assert forall|j: int|
            j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                el.kind,
                src,
                el.start as int,
                j,
            ) implies j <= el.end by {
            super::lemmas::lemma_kind_implies_any(goal, html, el.kind, src, pos as int, j);
            super::lemmas::lemma_longest_len(goal, html, src, pos as int);
            let n = j - pos as int;
            assert(pos as int + n == j);
            assert(any_element_matches(goal, html, src, pos as int, pos as int + n));
        }
    }
}

/// The full contract for an element that [`next_input_element`] returns of
/// a proven kind, **given** that no element of a kind that is not proven
/// ([`unproven_bounded`]: an identifier, private identifier, regular
/// expression literal, template or, in `html` mode, a comment, as long as
/// this one or longer) is derived at `pos`, and, for a numeric literal,
/// that the code point after it is below U+0080 (above it,
/// `IdentifierStart` is the uninterpreted `ID_Start`).
///
/// This is the part of the longest-match property and of the errors
/// ([`lex_error`]) that does not depend on the unproven kinds.
pub proof fn lemma_element_meets_contract(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    el: Element,
)
    requires
        next_input_element_proven(src, pos, goal, html, Ok(Step::Element(el))),
        kind_proven(el.kind, html),
        unproven_bounded(goal, html, src, pos as int, el.end as int),
    ensures
        super::contract::next_input_element_ensures(src, pos, goal, html, Ok(Step::Element(el))),
{
    let i = pos as int;
    let e = el.end as int;
    assert(element_matches(goal, html, el.kind, src, i, e));
    super::lemmas::lemma_kind_implies_any(goal, html, el.kind, src, i, e);
    assert(unproven_bounded(goal, html, src, i, e + 1));
    lemma_longest_from_bounds(goal, html, src, i, e);
    let n = longest_len(goal, html, src, i);
    assert(n == e - i);
    // No error: the numeric literal rule, and the identifier rules, do not fire.
    assert(!(element_matches(goal, html, ElementKind::NumericLiteral, src, i, i + n)
        && numeric_literal_follow_error(src, i + n))) by {
        if el.kind == ElementKind::NumericLiteral {
            assert(!numeric_literal_follow_error(src, e));
        } else {
            reveal(numeric_absent);
            assert(numeric_absent(src, i));
        }
    }
    assert(!(element_matches(goal, html, ElementKind::IdentifierName, src, i, i + n)
        && !identifier_name_valid(src, i, i + n))) by {
        if el.kind != ElementKind::IdentifierName {
            reveal(ident_absent);
            assert(ident_absent(src, i));
        }
    }
    assert(!(element_matches(goal, html, ElementKind::PrivateIdentifier, src, i, i + n)
        && !identifier_name_valid(src, i + 1, i + n))) by {
        if el.kind != ElementKind::PrivateIdentifier {
            reveal(private_absent);
            assert(private_absent(src, i));
        }
    }
    assert(lex_error(goal, html, src, i) is None);
    // The value is the standard's: for the kinds whose value is proven, as
    // proven; for the others there is none.
    assert(super::contract::element_value_agrees(src, el)) by {
        if value_proven(el.kind) {
            assert(value_agrees_proven(src, el));
        } else {
            assert(value_shape_agrees(el));
        }
    }
}

/// The contract for [`LexError::NoInputElement`], given that no element of
/// a kind that is not proven starts at `pos`.
pub proof fn lemma_no_input_element_meets_contract(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
)
    requires
        next_input_element_proven(src, pos, goal, html, Err(LexError::NoInputElement)),
        unproven_bounded(goal, html, src, pos as int, pos as int + 1),
    ensures
        super::contract::next_input_element_ensures(
            src,
            pos,
            goal,
            html,
            Err(LexError::NoInputElement),
        ),
{
    lemma_longest_zero(goal, html, src, pos as int);
}

/// The contract for [`LexError::IdentifierAfterNumericLiteral`], given that
/// no element of a kind that is not proven is longer than the literal and
/// that the code point after it is below U+0080.
pub proof fn lemma_numeric_error_meets_contract(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    end: int,
)
    requires
        next_input_element_proven(
            src,
            pos,
            goal,
            html,
            Err(LexError::IdentifierAfterNumericLiteral),
        ),
        pos < end <= src.len(),
        element_matches(goal, html, ElementKind::NumericLiteral, src, pos as int, end),
        proven_bounded(goal, html, src, pos as int, end),
        numeric_literal_follow_error(src, end),
        unproven_bounded(goal, html, src, pos as int, end + 1),
    ensures
        super::contract::next_input_element_ensures(
            src,
            pos,
            goal,
            html,
            Err(LexError::IdentifierAfterNumericLiteral),
        ),
{
    super::lemmas::lemma_kind_implies_any(
        goal,
        html,
        ElementKind::NumericLiteral,
        src,
        pos as int,
        end,
    );
    lemma_longest_from_bounds(goal, html, src, pos as int, end);
}

/// The contract for [`LexError::InvalidIdentifierEscape`], given that no
/// element of a kind that is not proven is longer than the identifier.
pub proof fn lemma_invalid_identifier_meets_contract(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    end: int,
)
    requires
        next_input_element_proven(
            src,
            pos,
            goal,
            html,
            Err(LexError::InvalidIdentifierEscape),
        ),
        pos < end <= src.len(),
        proven_bounded(goal, html, src, pos as int, end),
        numeric_absent(src, pos as int),
        invalid_identifier_at(goal, html, src, pos as int, end),
        unproven_bounded(goal, html, src, pos as int, end + 1),
    ensures
        super::contract::next_input_element_ensures(
            src,
            pos,
            goal,
            html,
            Err(LexError::InvalidIdentifierEscape),
        ),
{
    let i = pos as int;
    let kind = if element_matches(goal, html, ElementKind::IdentifierName, src, i, end) {
        ElementKind::IdentifierName
    } else {
        ElementKind::PrivateIdentifier
    };
    super::lemmas::lemma_kind_implies_any(goal, html, kind, src, i, end);
    lemma_longest_from_bounds(goal, html, src, i, end);
    let n = longest_len(goal, html, src, i);
    assert(n == end - i);
    reveal(numeric_absent);
    assert(!element_matches(goal, html, ElementKind::NumericLiteral, src, i, i + n));
}

// ---------------------------------------------------------------------
// Reading code points.
// ---------------------------------------------------------------------

/// What [`peek`] returns past the end of the source text. It is above
/// U+10FFFF, so it is no `SourceCharacter` and matches no class below,
/// just as a lookahead fails at the end (§11.1, `at` in the spec).
pub const EOF: u32 = 0xFFFF_FFFF;

/// The code point at `k`, or [`EOF`].
pub fn peek(src: &[u32], k: usize) -> (c: u32)
    ensures
        k < src.len() ==> c == src@[k as int],
        k >= src.len() ==> c == EOF,
{
    match src.get(k) {
        Some(c) => *c,
        None => EOF,
    }
}

/// §11.1 `SourceCharacter`.
fn is_src(c: u32) -> (r: bool)
    ensures
        r == is_source_character(c),
{
    c <= 0x10FFFF
}

/// `low <= c <= high`.
fn between(c: u32, low: u32, high: u32) -> (r: bool)
    ensures
        r == (low <= c <= high),
{
    low <= c && c <= high
}

/// §12.3 `LineTerminator`: <LF>, <CR>, <LS>, <PS>.
fn is_lt(c: u32) -> (r: bool)
    ensures
        r == is_line_terminator(c),
{
    c == 0x0A || c == 0x0D || c == 0x2028 || c == 0x2029
}

/// `SourceCharacter but not LineTerminator` (§12.4 `SingleLineCommentChar`,
/// §12.9.5 `RegularExpressionNonTerminator`).
fn is_line_char(c: u32) -> (r: bool)
    ensures
        r == is_not_line_terminator(c),
{
    is_src(c) && !is_lt(c)
}

/// §12.2 `WhiteSpace`: <TAB>, <VT>, <FF>, <ZWNBSP>, <USP>.
fn is_ws(c: u32) -> (r: bool)
    ensures
        r == (c == 0x0009 || c == 0x000B || c == 0x000C || c == 0xFEFF
            || unicode_space_separator(c)),
{
    c == 0x0009 || c == 0x000B || c == 0x000C || c == 0xFEFF || c == 0x0020 || c == 0x00A0 || c
        == 0x1680 || between(c, 0x2000, 0x200A) || c == 0x202F || c == 0x205F || c == 0x3000
}

/// §12.9.3 `DecimalDigit`.
fn is_dec(c: u32) -> (r: bool)
    ensures
        r == is_decimal_digit(c),
{
    between(c, 0x30, 0x39)
}

/// §12.9.3 `OctalDigit`.
fn is_oct(c: u32) -> (r: bool)
    ensures
        r == is_octal_digit(c),
{
    between(c, 0x30, 0x37)
}

/// §12.9.3 `HexDigit`.
fn is_hex(c: u32) -> (r: bool)
    ensures
        r == is_hex_digit(c),
{
    between(c, 0x30, 0x39) || between(c, 0x61, 0x66) || between(c, 0x41, 0x46)
}

/// `BinaryDigit`, `OctalDigit`, `DecimalDigit` or `HexDigit` by radix.
fn is_radix(radix: u32, c: u32) -> (r: bool)
    requires
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        r == is_radix_digit(radix as int, c),
{
    if radix == 2 {
        c == 0x30 || c == 0x31
    } else if radix == 8 {
        is_oct(c)
    } else if radix == 10 {
        is_dec(c)
    } else {
        is_hex(c)
    }
}

/// The MV of a `HexDigit` (§12.9.3.2).
fn hex_val(c: u32) -> (r: u32)
    requires
        is_hex_digit(c),
    ensures
        r as int == hex_digit_value(c),
        r < 16,
{
    if between(c, 0x30, 0x39) {
        c.saturating_sub(0x30)
    } else if between(c, 0x61, 0x66) {
        c.saturating_sub(0x61).saturating_add(10)
    } else {
        c.saturating_sub(0x41).saturating_add(10)
    }
}

/// §12.7 `IdentifierStartChar :: UnicodeIDStart | $ | _`. Above U+007F,
/// [`super::unicode`]'s table, which the spec's predicate is.
fn id_start_char(c: u32) -> (r: bool)
    ensures
        r == is_identifier_start_char(c),
        r ==> c <= 0x10FFFF,
        r ==> c != 0x5C,
{
    if c < 0x80 {
        between(c, 0x61, 0x7A) || between(c, 0x41, 0x5A) || c == 0x24 || c == 0x5F
    } else {
        super::unicode::id_start_non_ascii(c)
    }
}

/// §12.7 `IdentifierPartChar :: UnicodeIDContinue | $`.
fn id_part_char(c: u32) -> (r: bool)
    ensures
        r == is_identifier_part_char(c),
        r ==> c <= 0x10FFFF,
        r ==> c != 0x5C,
{
    if c < 0x80 {
        between(c, 0x61, 0x7A) || between(c, 0x41, 0x5A) || between(c, 0x30, 0x39) || c
            == 0x24 || c == 0x5F
    } else {
        super::unicode::id_continue_non_ascii(c)
    }
}

/// Appends UTF16EncodeCodePoint(`cp`) (§11.1.1).
fn push_utf16(out: &mut Vec<u16>, cp: u32)
    requires
        cp <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + utf16_encode_code_point(cp as int),
{
    if cp <= 0xFFFF {
        // 2. "If cp ≤ 0xFFFF, return the String value consisting of the
        //    code unit whose numeric value is cp."
        out.push(cp as u16);
        assert(final(out)@ =~= old(out)@ + utf16_encode_code_point(cp as int));
    } else {
        let v = cp.saturating_sub(0x10000);
        // 3. cu1 is floor((cp - 0x10000) / 0x400) + 0xD800.
        let cu1 = (v / 0x400).saturating_add(0xD800) as u16;
        // 4. cu2 is ((cp - 0x10000) modulo 0x400) + 0xDC00.
        let cu2 = (v % 0x400).saturating_add(0xDC00) as u16;
        // 5. The string-concatenation of cu1 and cu2.
        out.push(cu1);
        out.push(cu2);
        assert(final(out)@ =~= old(out)@ + utf16_encode_code_point(cp as int));
    }
}

/// Appends the UTF-16 of `src[i..j)`, each code point a `SourceCharacter`.
fn push_range_utf16(out: &mut Vec<u16>, src: &[u32], i: usize, j: usize)
    requires
        i <= j <= src.len(),
{
    let mut k = i;
    while k < j
        invariant
            i <= k <= j <= src.len(),
        decreases j - k,
    {
        let c = peek(src, k);
        if c <= 0x10FFFF {
            push_utf16(out, c);
        }
        k = k.saturating_add(1);
    }
}

// ---------------------------------------------------------------------
// §12.4 Comments, §12.5 Hashbang Comments, Annex B.1.1
// ---------------------------------------------------------------------

/// §12.4 `SingleLineCommentChars?` from `k`: the first index at or after
/// `k` that is not a `SourceCharacter` other than a `LineTerminator`.
fn scan_line_chars(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
        all_of(src@, k as int, r as int, |c: u32| is_not_line_terminator(c)),
        r < src.len() ==> !is_not_line_terminator(src@[r as int]),
{
    let mut j = k;
    loop
        invariant
            k <= j <= src.len(),
            all_of(src@, k as int, j as int, |c: u32| is_not_line_terminator(c)),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if is_line_char(c) {
            j = j.saturating_add(1);
        } else {
            return j;
        }
    }
}

/// The `*/` that ends at `e` closes a block comment whose body starts at
/// `k`: it is the first `*/` at or after `k`, and every code point before
/// it is a `SourceCharacter` (and, if `!multi_line`, not a
/// `LineTerminator`).
pub open spec fn block_close_ok(s: Seq<u32>, k: int, e: int, multi_line: bool) -> bool {
    k + 2 <= e && e <= s.len() && s[e - 2] == 0x2A && s[e - 1] == 0x2F && forall|m: int|
        k <= m < e - 2 ==> (#[trigger] s[m] <= 0x10FFFF && !(s[m] == 0x2A && s[m + 1] == 0x2F) && (
        multi_line || !is_line_terminator(s[m])))
}

/// §12.4 `MultiLineComment` (or, with `!multi_line`, Annex B's
/// `SingleLineDelimitedComment`) after its `/*` at `k`: the end of the
/// first `*/` and whether a `LineTerminator` came before it. `None` if the
/// source text ends, or a code point that is not a `SourceCharacter` (or,
/// with `!multi_line`, a `LineTerminator`) comes, first.
///
/// Proven: `Some((e, lt))` is the one end [`block_close_ok`] allows, and
/// `lt` is [`contains_line_terminator`] of the body; `None` means no end
/// is allowed.
fn scan_block_comment(src: &[u32], k: usize, multi_line: bool) -> (r: Option<(usize, bool)>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some((e, lt)) => block_close_ok(src@, k as int, e as int, multi_line)
                && lt == contains_line_terminator(src@, k as int, e as int - 2) && (forall|
                e2: int,
            | block_close_ok(src@, k as int, e2, multi_line) ==> e2 == e),
            None => forall|e2: int| !block_close_ok(src@, k as int, e2, multi_line),
        },
{
    let mut j = k;
    let mut lt = false;
    loop
        invariant
            k <= j <= src.len(),
            lt == contains_line_terminator(src@, k as int, j as int),
            forall|m: int|
                k <= m < j ==> (#[trigger] src@[m] <= 0x10FFFF && !(m + 1 < src.len()
                    && src@[m] == 0x2A && src@[m + 1] == 0x2F) && (multi_line
                    || !is_line_terminator(src@[m]))),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x2A && peek(src, j.saturating_add(1)) == 0x2F {
            proof {
                let e = j + 2;
                assert(block_close_ok(src@, k as int, e, multi_line));
                assert forall|e2: int| block_close_ok(src@, k as int, e2, multi_line) implies e2
                    == e by {
                    if e2 < e {
                        assert(src@[e2 - 2] == 0x2A && src@[e2 - 1] == 0x2F);
                        assert(k <= e2 - 2 < j);
                    } else if e2 > e {
                        assert(k <= j < e2 - 2);
                    }
                }
            }
            return Some((j.saturating_add(2), lt));
        }
        if !is_src(c) || (!multi_line && is_lt(c)) {
            proof {
                assert forall|e2: int| !block_close_ok(src@, k as int, e2, multi_line) by {
                    if block_close_ok(src@, k as int, e2, multi_line) {
                        if e2 - 2 < j {
                            assert(k <= e2 - 2 < j);
                        } else if e2 - 2 == j {
                            assert(src@[j as int] == 0x2A);
                        } else {
                            assert(k <= j < e2 - 2);
                        }
                    }
                }
            }
            return None;
        }
        if is_lt(c) {
            lt = true;
        }
        proof {
            assert(contains_line_terminator(src@, k as int, (j + 1) as int) == (lt || false) || true);
            assert(lt == contains_line_terminator(src@, k as int, (j + 1) as int)) by {
                if is_line_terminator(src@[j as int]) {
                    assert(contains_line_terminator(src@, k as int, (j + 1) as int));
                } else if contains_line_terminator(src@, k as int, (j + 1) as int) {
                    let m = choose|m: int| k <= m < j + 1 && is_line_terminator(src@[m]);
                    assert(m < j);
                }
            }
        }
        j = j.saturating_add(1);
    }
}

/// Annex B.1.1 `WhiteSpaceSequence?` from `k`.
fn scan_ws(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
{
    let mut j = k;
    loop
        invariant
            k <= j <= src.len(),
        decreases src.len() - j,
    {
        if is_ws(peek(src, j)) {
            j = j.saturating_add(1);
        } else {
            return j;
        }
    }
}

/// Annex B.1.1 the end of `-->` SingleLineCommentChars? at `k`.
fn scan_html_arrow(src: &[u32], k: usize) -> (r: Option<usize>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some(e) => k + 3 <= e <= src.len(),
            None => true,
        },
{
    if peek(src, k) == 0x2D && peek(src, k.saturating_add(1)) == 0x2D && peek(
        src,
        k.saturating_add(2),
    ) == 0x3E {
        Some(scan_line_chars(src, k.saturating_add(3)))
    } else {
        None
    }
}

/// Annex B.1.1 `HTMLCloseComment :: WhiteSpaceSequence?
/// SingleLineDelimitedCommentSequence? --> SingleLineCommentChars?` at `k`.
/// Each part is determined by the code point that starts it (white space,
/// `/*` or `-->`), so the parse is the only one, and it ends where the
/// line does.
fn scan_html_close(src: &[u32], k: usize) -> (r: Option<usize>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some(e) => k + 3 <= e <= src.len(),
            None => true,
        },
{
    let mut j = scan_ws(src, k);
    loop
        invariant
            k <= j <= src.len(),
        decreases src.len() - j,
    {
        if peek(src, j) == 0x2F && peek(src, j.saturating_add(1)) == 0x2A {
            // SingleLineDelimitedComment WhiteSpaceSequence?
            match scan_block_comment(src, j.saturating_add(2), false) {
                Some((e, _)) => {
                    j = scan_ws(src, e);
                },
                None => {
                    return None;
                },
            }
        } else {
            return scan_html_arrow(src, j);
        }
    }
}

/// The `LineTerminatorSequence` at `k` (§12.3): <CR><LF> is one.
fn line_terminator_sequence_end(src: &[u32], k: usize) -> (r: usize)
    requires
        k < src.len(),
        is_line_terminator(src@[k as int]),
    ensures
        k < r <= src.len(),
        line_terminator_sequence(src@, k as int, r as int),
        forall|r2: int| line_terminator_sequence(src@, k as int, r2) ==> r2 == r,
{
    if peek(src, k) == 0x0D && peek(src, k.saturating_add(1)) == 0x0A {
        k.saturating_add(2)
    } else {
        k.saturating_add(1)
    }
}

// ---------------------------------------------------------------------
// §12.7 Names
// ---------------------------------------------------------------------

/// The MV of the `HexDigits[~Sep]` that start at `k` (all of them), capped
/// at 0x110000 (any value above U+10FFFF is `NotCodePoint`), and the end.
///
/// Proven: the end is where the run of hex digits ends, and the value is
/// the spec's [`hex_digits_mv`] of the run when that is at most U+10FFFF
/// (and above U+10FFFF otherwise).
fn scan_hex_digits(src: &[u32], k: usize) -> (r: (u32, usize))
    requires
        k <= src.len(),
    ensures
        r.0 <= 0x110000,
        k <= r.1 <= src.len(),
        r.1 as int == ind_hex_run_end(src@, k as int),
        r.0 <= 0x10FFFF ==> r.0 as int == hex_digits_mv(src@, k as int, r.1 as int),
        r.0 > 0x10FFFF ==> hex_digits_mv(src@, k as int, r.1 as int) > 0x10FFFF,
        forall|t: int| k <= t < r.1 ==> is_hex_digit(#[trigger] src@[t]),
{
    let mut j = k;
    let mut v: u32 = 0;
    loop
        invariant
            k <= j <= src.len(),
            v <= 0x110000,
            ind_hex_run_end(src@, k as int) == ind_hex_run_end(src@, j as int),
            forall|t: int| k <= t < j ==> is_hex_digit(#[trigger] src@[t]),
            v <= 0x10FFFF ==> v as int == hex_digits_mv(src@, k as int, j as int),
            v > 0x10FFFF ==> hex_digits_mv(src@, k as int, j as int) > 0x10FFFF,
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if is_hex(c) {
            let d = hex_val(c);
            proof {
                reveal_with_fuel(hex_digits_mv, 2);
                assert(ind_hex_run_end(src@, j as int) == ind_hex_run_end(src@, j as int + 1));
            }
            if v <= 0x10FFFF {
                let w = v.saturating_mul(16).saturating_add(d);
                v = if w > 0x10FFFF {
                    0x110000
                } else {
                    w
                };
            }
            j = j.saturating_add(1);
        } else {
            return (v, j);
        }
    }
}

/// §12.9.4 `Hex4Digits` at `k`: its MV.
///
/// Proven: `Some(v)` when four hex digits start at `k`, and then `v` is
/// their [`hex_digits_mv`]; `None` when they do not.
fn scan_hex4(src: &[u32], k: usize) -> (r: Option<u32>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some(v) => k + 4 <= src.len() && v <= 0xFFFF && ind_hex_run_end(src@, k as int) >= k
                + 4 && v as int == hex_digits_mv(src@, k as int, k as int + 4),
            None => ind_hex_run_end(src@, k as int) < k + 4,
        },
{
    let a = peek(src, k);
    let b = peek(src, k.saturating_add(1));
    let c = peek(src, k.saturating_add(2));
    let d = peek(src, k.saturating_add(3));
    proof {
        lemma_hex_run_end(src@, k as int);
    }
    if is_hex(a) && is_hex(b) && is_hex(c) && is_hex(d) {
        let v = hex_val(a).saturating_mul(0x1000).saturating_add(
            hex_val(b).saturating_mul(0x100),
        ).saturating_add(hex_val(c).saturating_mul(0x10)).saturating_add(hex_val(d));
        proof {
            reveal_with_fuel(hex_digits_mv, 5);
            let end = ind_hex_run_end(src@, k as int);
            if end < k + 4 {
                assert(ind_hex(src@[end]));
            }
        }
        Some(v)
    } else {
        proof {
            let end = ind_hex_run_end(src@, k as int);
            if end >= k + 4 {
                assert(ind_hex(src@[k as int]));
                assert(ind_hex(src@[k as int + 1]));
                assert(ind_hex(src@[k as int + 2]));
                assert(ind_hex(src@[k as int + 3]));
            }
        }
        None
    }
}

/// §12.9.4 `UnicodeEscapeSequence :: u Hex4Digits | u{ CodePoint }` at `k`
/// (after the backslash): its code point (§12.7.1.3 IdentifierCodePoint)
/// and its end.
///
/// Proven: `Some((cp, e))` is the one `UnicodeEscapeSequence` the spec
/// derives at `k` (the deterministic reading [`ind_escape_end`] of
/// `independent.rs`, which `equivalence.rs` proves equal to the spec's) and
/// `cp` is its code point; `None` means the spec derives none.
fn scan_unicode_escape(src: &[u32], k: usize) -> (r: Option<(u32, usize)>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some((cp, e)) => k < e <= src.len() && cp <= 0x10FFFF && ind_escape_end(
                src@,
                k as int,
            ) == e as int && cp as int == unicode_escape_code_point(src@, k as int, e as int) && ((
            k + 1 < src.len() && src@[k as int + 1] != 0x7B) ==> cp <= 0xFFFF),
            None => ind_escape_end(src@, k as int) == -1,
        },
{
    if peek(src, k) != 0x75 {
        return None;
    }
    if peek(src, k.saturating_add(1)) == 0x7B {
        // 2. `u{` CodePoint `}`, with CodePoint's MV at most 0x10FFFF.
        let (v, e) = scan_hex_digits(src, k.saturating_add(2));
        if e > k.saturating_add(2) && v <= 0x10FFFF && peek(src, e) == 0x7D {
            proof {
                lemma_hex_value_equiv(src@, k as int + 2, e as int);
            }
            Some((v, e.saturating_add(1)))
        } else {
            proof {
                if v > 0x10FFFF {
                    lemma_hex_value_equiv(src@, k as int + 2, e as int);
                }
            }
            None
        }
    } else {
        // 1. `u` Hex4Digits
        let v = scan_hex4(src, k.saturating_add(1))?;
        Some((v, k.saturating_add(5)))
    }
}

/// §12.7 `IdentifierName` at `k`, greedily (each `IdentifierPart` is
/// determined by its first code point, so the longest derivation is the
/// greedy one): IdentifierCodePoints (§12.7.1.2), whether an escape was
/// used, whether the §12.7.1.1 early errors pass, and the end.
///
/// Proven: `Some` is the longest `IdentifierName` the spec derives at `k`
/// (it is read left to right as [`super::independent`]'s units, so no
/// derivation is longer: [`name_end`]), the code points are the spec's
/// IdentifierCodePoints of it, `escaped` is whether it has an escape, and
/// `valid` is whether it has no early error; `None` means the spec derives
/// none.
fn scan_identifier(src: &[u32], k: usize) -> (r: Option<(Vec<u32>, bool, bool, usize)>)
    requires
        k <= src.len(),
    ensures
        match r {
            Some((cps, escaped, valid, e)) => k < e <= src.len() && ind_name_from(
                src@,
                k as int,
                e as int,
                true,
            ) && name_end(src@, k as int, true) == e as int && identifier_name_cps(
                src@,
                k as int,
                e as int,
                cps@,
            ) && escaped == identifier_has_escape(src@, k as int, e as int) && valid
                == identifier_early_errors_ok(cps@),
            None => ind_unit_end(src@, k as int, true) < 0,
        },
{
    let mut cps: Vec<u32> = Vec::new();
    let mut escaped = false;
    let mut valid = true;
    let c = peek(src, k);
    let mut j: usize;
    if c == 0x5C {
        // IdentifierStart :: \ UnicodeEscapeSequence; §12.7.1.1: "It is a
        // Syntax Error if the IdentifierCodePoint of UnicodeEscapeSequence
        // is not some Unicode code point matched by the IdentifierStartChar
        // lexical grammar production."
        match scan_unicode_escape(src, k.saturating_add(1)) {
            Some((cp, e)) => {
                proof {
                    let s = src@;
                    assert(s[k as int] == 0x5C);
                    assert(ind_unit_end(s, k as int, true) == e as int);
                    lemma_unit_equiv(s, k as int, e as int);
                    assert(identifier_start(s, k as int, e as int));
                    assert(identifier_code_point(s, k as int, e as int) == cp);
                    lemma_cps_start(s, k as int, e as int);
                    assert(ind_name_from(s, e as int, e as int, false));
                    lemma_name_end_step(s, k as int, e as int, true);
                    lemma_early_one(cp);
                    lemma_has_escape_esc(s, k as int, k as int, e as int);
                }
                cps.push(cp);
                escaped = true;
                valid = id_start_char(cp);
                j = e;
            },
            None => {
                return None;
            },
        }
    } else if id_start_char(c) {
        // IdentifierStart :: IdentifierStartChar
        proof {
            let s = src@;
            assert(k < s.len() && c == s[k as int]);
            lemma_id_char_equiv(c);
            assert(ind_unit_end(s, k as int, true) == k as int + 1);
            lemma_unit_equiv(s, k as int, k as int + 1);
            assert(identifier_start(s, k as int, k as int + 1));
            lemma_cps_start(s, k as int, k as int + 1);
            assert(ind_name_from(s, k as int + 1, k as int + 1, false));
            lemma_name_end_step(s, k as int, k as int + 1, true);
            lemma_early_one(c);
            lemma_has_escape_plain(s, k as int, k as int);
        }
        cps.push(c);
        j = k.saturating_add(1);
    } else {
        proof {
            let s = src@;
            if k < s.len() {
                lemma_id_char_equiv(s[k as int]);
            }
        }
        return None;
    }
    loop
        invariant
            k < j <= src.len(),
            ind_name_from(src@, k as int, j as int, true),
            name_end(src@, k as int, true) == name_end(src@, j as int, false),
            identifier_name_cps(src@, k as int, j as int, cps@),
            escaped == identifier_has_escape(src@, k as int, j as int),
            valid == identifier_early_errors_ok(cps@),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x5C {
            // IdentifierPart :: \ UnicodeEscapeSequence, with §12.7.1.1's
            // rule for IdentifierPartChar.
            match scan_unicode_escape(src, j.saturating_add(1)) {
                Some((cp, e)) => {
                    proof {
                        let s = src@;
                        assert(s[j as int] == 0x5C);
                        assert(ind_unit_end(s, j as int, false) == e as int);
                        lemma_unit_equiv(s, j as int, e as int);
                        assert(identifier_part(s, j as int, e as int));
                        assert(identifier_code_point(s, j as int, e as int) == cp);
                        lemma_cps_extend(s, k as int, j as int, e as int, cps@);
                        lemma_name_from_append(s, k as int, j as int, e as int, true);
                        lemma_name_end_step(s, j as int, e as int, false);
                        lemma_cps_nonempty(s, k as int, j as int, cps@);
                        lemma_early_push(cps@, cp);
                        lemma_has_escape_esc(s, k as int, j as int, e as int);
                    }
                    cps.push(cp);
                    escaped = true;
                    if !id_part_char(cp) {
                        valid = false;
                    }
                    j = e;
                },
                None => {
                    proof {
                        let s = src@;
                        assert(s[j as int] == 0x5C);
                        assert(ind_unit_end(s, j as int, false) < 0);
                        lemma_name_end_stop(s, j as int);
                        lemma_name_end_derives(s, k as int, true);
                    }
                    return Some((cps, escaped, valid, j));
                },
            }
        } else if id_part_char(c) {
            // IdentifierPart :: IdentifierPartChar
            proof {
                let s = src@;
                assert(j < s.len() && c == s[j as int]);
                lemma_id_char_equiv(c);
                assert(ind_unit_end(s, j as int, false) == j as int + 1);
                lemma_unit_equiv(s, j as int, j as int + 1);
                assert(identifier_part(s, j as int, j as int + 1));
                assert(identifier_code_point(s, j as int, j as int + 1) == c);
                lemma_cps_extend(s, k as int, j as int, j as int + 1, cps@);
                lemma_name_from_append(s, k as int, j as int, j as int + 1, true);
                lemma_name_end_step(s, j as int, j as int + 1, false);
                lemma_cps_nonempty(s, k as int, j as int, cps@);
                lemma_early_push(cps@, c);
                lemma_has_escape_plain(s, k as int, j as int);
            }
            cps.push(c);
            j = j.saturating_add(1);
        } else {
            proof {
                let s = src@;
                if j < s.len() {
                    lemma_id_char_equiv(s[j as int]);
                }
                assert(ind_unit_end(s, j as int, false) < 0);
                lemma_name_end_stop(s, j as int);
                lemma_name_end_derives(s, k as int, true);
            }
            return Some((cps, escaped, valid, j));
        }
    }
}

// ---------------------------------------------------------------------
// §12.8 Punctuators
// ---------------------------------------------------------------------

/// §12.8 `Punctuator` (`OptionalChainingPunctuator` and `OtherPunctuator`)
/// at `k`: the end of the longest one, or `k` if none starts there.
fn scan_punctuator(src: &[u32], k: usize) -> (r: usize)
    requires
        k < src.len(),
    ensures
        k <= r <= src.len(),
        r > k ==> punctuator(src@, k as int, r as int),
        forall|j: int| punctuator(src@, k as int, j) ==> j <= r,
{
    let c0 = peek(src, k);
    let c1 = peek(src, k.saturating_add(1));
    let c2 = peek(src, k.saturating_add(2));
    let c3 = peek(src, k.saturating_add(3));
    let n: usize = if c0 == 0x7B || c0 == 0x28 || c0 == 0x29 || c0 == 0x5B || c0 == 0x5D || c0
        == 0x3B || c0 == 0x2C || c0 == 0x7E || c0 == 0x3A {
        // { ( ) [ ] ; , ~ :
        1
    } else if c0 == 0x2E {
        // ... .
        if c1 == 0x2E && c2 == 0x2E {
            3
        } else {
            1
        }
    } else if c0 == 0x3C {
        // <<= << <= <
        if c1 == 0x3C && c2 == 0x3D {
            3
        } else if c1 == 0x3C || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x3E {
        // >>>= >>> >>= >> >= >
        if c1 == 0x3E && c2 == 0x3E && c3 == 0x3D {
            4
        } else if c1 == 0x3E && (c2 == 0x3E || c2 == 0x3D) {
            3
        } else if c1 == 0x3E || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x3D {
        // === == => =
        if c1 == 0x3D && c2 == 0x3D {
            3
        } else if c1 == 0x3D || c1 == 0x3E {
            2
        } else {
            1
        }
    } else if c0 == 0x21 {
        // !== != !
        if c1 == 0x3D && c2 == 0x3D {
            3
        } else if c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x2B || c0 == 0x2D {
        // ++ += +, -- -= -
        if c1 == c0 || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x2A {
        // **= ** *= *
        if c1 == 0x2A && c2 == 0x3D {
            3
        } else if c1 == 0x2A || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x25 || c0 == 0x5E {
        // %= %, ^= ^
        if c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x26 || c0 == 0x7C {
        // &&= && &= &, ||= || |= |
        if c1 == c0 && c2 == 0x3D {
            3
        } else if c1 == c0 || c1 == 0x3D {
            2
        } else {
            1
        }
    } else if c0 == 0x3F {
        // ??= ?? ?. ?, with OptionalChainingPunctuator :: ?.
        // [lookahead ∉ DecimalDigit]
        if c1 == 0x3F && c2 == 0x3D {
            3
        } else if c1 == 0x3F || (c1 == 0x2E && !is_dec(c2)) {
            2
        } else {
            1
        }
    } else {
        0
    };
    proof {
        // The punctuators are the closed forms of `independent.rs`.
        assert forall|j: int| punctuator(src@, k as int, j) implies j <= k + n by {
            lemma_other_punctuator_equiv(src@, k as int, j);
            lemma_optional_chaining_equiv(src@, k as int, j);
        }
        if n > 0 {
            lemma_other_punctuator_equiv(src@, k as int, (k + n) as int);
            lemma_optional_chaining_equiv(src@, k as int, (k + n) as int);
        }
    }
    k.saturating_add(n)
}

// ---------------------------------------------------------------------
// §12.9.3 Numeric Literals
// ---------------------------------------------------------------------

/// §12.9.3 `Digits[+Sep]` of a radix, from a digit at `k`: digits, each
/// pair of them possibly separated by one `_`. Greedy, since a `_` is
/// taken only when a digit follows it.
fn scan_digits_sep(src: &[u32], k: usize, radix: u32) -> (r: usize)
    requires
        k < src.len(),
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
        is_radix_digit(radix as int, src@[k as int]),
    ensures
        k < r <= src.len(),
        ind_sep_digits(radix as int, src@, k as int, r as int),
        forall|j: int| j > r ==> !ind_sep_digits(radix as int, src@, k as int, j),
        !(r < src.len() && is_radix_digit(radix as int, src@[r as int])),
        !(r + 1 < src.len() && src@[r as int] == 0x5F && is_radix_digit(
            radix as int,
            src@[r as int + 1],
        )),
{
    proof {
        lemma_digit_class_equiv(radix as int, src@[k as int]);
        lemma_sep_base(radix as int, src@, k as int);
    }
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
            radix == 2 || radix == 8 || radix == 10 || radix == 16,
            ind_sep_digits(radix as int, src@, k as int, j as int),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if is_radix(radix, c) {
            proof {
                lemma_digit_class_equiv(radix as int, c);
                lemma_sep_extend1(radix as int, src@, k as int, j as int);
            }
            j = j.saturating_add(1);
        } else if c == 0x5F && is_radix(radix, peek(src, j.saturating_add(1))) {
            proof {
                lemma_digit_class_equiv(radix as int, src@[j as int + 1]);
                lemma_sep_extend2(radix as int, src@, k as int, j as int);
            }
            j = j.saturating_add(2);
        } else {
            proof {
                if j < src.len() {
                    lemma_digit_class_equiv(radix as int, src@[j as int]);
                }
                if j + 1 < src.len() {
                    lemma_digit_class_equiv(radix as int, src@[j as int + 1]);
                }
                lemma_sep_maximal(radix as int, src@, k as int, j as int);
            }
            return j;
        }
    }
}

/// §12.9.3 `ExponentPart[+Sep]?` at `k`: its end, or `k`.
fn scan_exponent(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
        r > k ==> ind_exponent(src@, k as int, r as int),
        forall|j: int| ind_exponent(src@, k as int, j) ==> j <= r,
{
    let c = peek(src, k);
    if c == 0x65 || c == 0x45 {
        let s = peek(src, k.saturating_add(1));
        let m = if s == 0x2B || s == 0x2D {
            k.saturating_add(2)
        } else {
            k.saturating_add(1)
        };
        if is_dec(peek(src, m)) {
            scan_digits_sep(src, m, 10)
        } else {
            k
        }
    } else {
        k
    }
}

/// The rest of a §12.9.3 `DecimalLiteral` after its `DecimalIntegerLiteral`
/// ends at `k`: `. DecimalDigits[+Sep]? ExponentPart[+Sep]?` or
/// `ExponentPart[+Sep]?`.
fn scan_decimal_tail(src: &[u32], k: usize) -> (r: usize)
    requires
        k <= src.len(),
    ensures
        k <= r <= src.len(),
        ind_tail(src@, k as int, r as int),
        forall|j: int| ind_tail(src@, k as int, j) ==> j <= r,
{
    if peek(src, k) == 0x2E {
        let m = k.saturating_add(1);
        let n = if is_dec(peek(src, m)) {
            scan_digits_sep(src, m, 10)
        } else {
            m
        };
        let r = scan_exponent(src, n);
        proof {
            // The tail `.` digits? exponent?, on `[k, r)`.
            assert(ind_dl_tail_mid(src@, k as int, n as int, r as int));
            assert forall|j: int| ind_tail(src@, k as int, j) implies j <= r by {
                if ind_tail(src@, k as int, j) && j != k {
                    assert(!ind_exponent(src@, k as int, j));
                    let b = choose|b: int| ind_dl_tail_mid(src@, k as int, b, j);
                    if m < src.len() && is_decimal_digit(src@[m as int]) {
                        if b > n {
                            assert(ind_sep_digits(10, src@, m as int, b));
                        }
                        if b < n {
                            if b > m {
                                lemma_sep_chars(10, src@, m as int, n as int, b);
                            }
                            assert(b == j);
                        }
                    }
                }
            }
        }
        r
    } else {
        scan_exponent(src, k)
    }
}

/// What [`scan_numeric`] returns, in the closed forms of `independent.rs`.
pub open spec fn numeric_ind_result(s: Seq<u32>, k: int, r: Option<(usize, bool, bool)>) -> bool {
    match r {
        Some((e, bigint, legacy)) => k < e <= s.len() && ind_numeric_literal(s, k, e as int) && (
        forall|j: int| ind_numeric_literal(s, k, j) ==> j <= e) && bigint == ind_is_bigint(
            s,
            k,
            e as int,
        ) && legacy == ind_is_legacy(s, k, e as int),
        None => forall|j: int| !ind_numeric_literal(s, k, j),
    }
}

/// A `.` and a decimal digit.
fn num_dot(src: &[u32], k: usize) -> (r: Option<(usize, bool, bool)>)
    requires
        k + 1 < src.len(),
        src@[k as int] == 0x2E,
        is_decimal_digit(src@[k as int + 1]),
    ensures
        numeric_ind_result(src@, k as int, r),
{
    let e = scan_digits_sep(src, k.saturating_add(1), 10);
    let r = scan_exponent(src, e);
    proof {
        let s = src@;
        lemma_shape_dot(s, k as int);
        assert forall|j: int| ind_numeric_literal(s, k as int, j) implies j <= r by {
            let b = choose|b: int| #[trigger] ind_dl_alt2(s, k as int, j, b);
            if b < e {
                lemma_sep_chars(10, s, k as int + 1, e as int, b);
                assert(j == b);
            }
        }
        assert(ind_dl_alt2(s, k as int, r as int, e as int));
        assert(ind_decimal_literal(s, k as int, r as int));
    }
    Some((r, false, false))
}

/// A `0`, a prefix letter and a digit of its radix.
fn num_prefix(src: &[u32], k: usize, radix: u32) -> (r: Option<(usize, bool, bool)>)
    requires
        k + 2 < src.len(),
        prefix_digit(src@, k as int),
        radix == 2 || radix == 8 || radix == 16,
        radix == 2 ==> (src@[k as int + 1] == 0x62 || src@[k as int + 1] == 0x42),
        radix == 8 ==> (src@[k as int + 1] == 0x6F || src@[k as int + 1] == 0x4F),
        radix == 16 ==> (src@[k as int + 1] == 0x78 || src@[k as int + 1] == 0x58),
        is_radix_digit(radix as int, src@[k as int + 2]),
    ensures
        numeric_ind_result(src@, k as int, r),
{
    // NonDecimalIntegerLiteral[+Sep] BigIntLiteralSuffix?
    let e = scan_digits_sep(src, k.saturating_add(2), radix);
    proof {
        lemma_shape_prefix(src@, k as int, radix as int);
    }
    if peek(src, e) == 0x6E {
        proof {
            let s = src@;
            assert forall|j: int| ind_numeric_literal(s, k as int, j) implies j <= e + 1 by {
                if j > k + 3 && s[j - 1] == 0x6E && ind_sep_digits(
                    radix as int,
                    s,
                    k as int + 2,
                    j - 1,
                ) {
                    if j - 1 < e {
                        lemma_sep_chars(radix as int, s, k as int + 2, e as int, j - 1);
                    }
                }
            }
        }
        Some((e.saturating_add(1), true, false))
    } else {
        proof {
            let s = src@;
            assert forall|j: int| ind_numeric_literal(s, k as int, j) implies j <= e by {
                if j > k + 3 && s[j - 1] == 0x6E && ind_sep_digits(
                    radix as int,
                    s,
                    k as int + 2,
                    j - 1,
                ) {
                    if j - 1 < e {
                        lemma_sep_chars(radix as int, s, k as int + 2, e as int, j - 1);
                    }
                    assert(false);
                }
            }
        }
        Some((e, false, false))
    }
}

/// A `0` and a decimal digit: `0` and decimal digits, with no separator: a
/// LegacyOctalIntegerLiteral if they are all octal, else a
/// NonOctalDecimalIntegerLiteral, which a DecimalLiteral may continue.
fn num_zero_digit(src: &[u32], k: usize) -> (r: Option<(usize, bool, bool)>)
    requires
        k + 1 < src.len(),
        src@[k as int] == 0x30,
        is_decimal_digit(src@[k as int + 1]),
    ensures
        numeric_ind_result(src@, k as int, r),
{
    let mut j = k.saturating_add(1);
    let mut octal = true;
    while is_dec(peek(src, j))
        invariant
            k < j <= src.len(),
            all_dec(src@, k as int + 1, j as int),
            octal == (forall|t: int|
                k + 1 <= t < j ==> is_octal_digit(#[trigger] src@[t])),
            !octal ==> exists|t: int|
                k + 1 <= t < j && is_non_octal_digit(#[trigger] src@[t]),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if !is_oct(c) {
            octal = false;
        }
        j = j.saturating_add(1);
    }
    proof {
        lemma_shape_zero_digit(src@, k as int);
        assert(j > k + 1) by {
            if j == k + 1 {
                assert(!is_decimal_digit(src@[k as int + 1]));
            }
        }
    }
    if octal {
        proof {
            let s = src@;
            assert(ind_plain_digits(8, s, k as int + 1, j as int));
            assert(ind_legacy_octal(s, k as int, j as int));
            assert forall|jj: int| ind_numeric_literal(s, k as int, jj) implies jj <= j by {
                if jj > j {
                    if ind_legacy_octal(s, k as int, jj) {
                        assert(ind_dec(s[j as int]));
                    }
                }
                if exists|a: int| #![trigger ind_non_octal_decimal_integer(s, k as int, a)]
                    ind_non_octal_decimal_integer(s, k as int, a) && ind_tail(s, a, jj) {
                    let a = choose|a: int|
                        #![trigger ind_non_octal_decimal_integer(s, k as int, a)]
                        ind_non_octal_decimal_integer(s, k as int, a) && ind_tail(
                            s,
                            a,
                            jj,
                        );
                    let t = choose|t: int| k < t < a && (s[t] == 0x38 || s[t] == 0x39);
                    assert(a <= j) by {
                        if a > j {
                            assert(ind_dec(s[j as int]));
                        }
                    }
                    assert(is_octal_digit(s[t]));
                }
            }
        }
        Some((j, false, true))
    } else {
        let r = scan_decimal_tail(src, j);
        proof {
            let s = src@;
            let t0 = choose|t: int| k + 1 <= t < j && is_non_octal_digit(src@[t]);
            assert(ind_non_octal_decimal_integer(s, k as int, j as int)) by {
                assert(ind_plain_digits(10, s, k as int + 1, j as int));
                assert(k < t0 < j && (s[t0] == 0x38 || s[t0] == 0x39));
            }
            assert forall|jj: int| ind_numeric_literal(s, k as int, jj) implies jj <= r by {
                if ind_legacy_octal(s, k as int, jj) && jj > j {
                    assert(ind_dec(s[j as int]));
                }
                if exists|a: int| #![trigger ind_non_octal_decimal_integer(s, k as int, a)]
                    ind_non_octal_decimal_integer(s, k as int, a) && ind_tail(s, a, jj) {
                    let a = choose|a: int|
                        #![trigger ind_non_octal_decimal_integer(s, k as int, a)]
                        ind_non_octal_decimal_integer(s, k as int, a) && ind_tail(
                            s,
                            a,
                            jj,
                        );
                    assert(a <= j) by {
                        if a > j {
                            assert(ind_dec(s[j as int]));
                        }
                    }
                    if a < j {
                        if jj > a {
                            lemma_tail_first(s, a, jj);
                            assert(ind_dec(s[a]));
                        }
                    }
                }
            }
        }
        Some((r, false, true))
    }
}

/// A non-zero digit.
#[verifier::rlimit(100)]
fn num_nonzero(src: &[u32], k: usize) -> (r: Option<(usize, bool, bool)>)
    requires
        k < src.len(),
        is_decimal_digit(src@[k as int]),
        src@[k as int] != 0x30,
    ensures
        numeric_ind_result(src@, k as int, r),
{
    let e = scan_digits_sep(src, k, 10);
    proof {
        lemma_shape_nonzero(src@, k as int);
    }
    if peek(src, e) == 0x6E {
        proof {
            let s = src@;
            assert forall|j: int| ind_numeric_literal(s, k as int, j) implies j <= e + 1 by {
                if exists|a: int| #![trigger ind_sep_digits(10, s, k as int, a)]
                    ind_sep_digits(10, s, k as int, a) && ind_tail(s, a, j) {
                    let a = choose|a: int| #![trigger ind_sep_digits(10, s, k as int, a)]
                        ind_sep_digits(10, s, k as int, a) && ind_tail(s, a, j);
                    if j > a {
                        lemma_tail_first(s, a, j);
                        if a < e {
                            lemma_sep_chars(10, s, k as int, e as int, a);
                        }
                    }
                }
                if j > k + 1 && s[j - 1] == 0x6E && ind_sep_digits(10, s, k as int, j - 1) {
                    if j - 1 < e {
                        lemma_sep_chars(10, s, k as int, e as int, j - 1);
                    }
                }
            }
        }
        Some((e.saturating_add(1), true, false))
    } else {
        let r = scan_decimal_tail(src, e);
        proof {
            let s = src@;
            assert forall|j: int| ind_numeric_literal(s, k as int, j) implies j <= r by {
                if exists|a: int| #![trigger ind_sep_digits(10, s, k as int, a)]
                    ind_sep_digits(10, s, k as int, a) && ind_tail(s, a, j) {
                    let a = choose|a: int| #![trigger ind_sep_digits(10, s, k as int, a)]
                        ind_sep_digits(10, s, k as int, a) && ind_tail(s, a, j);
                    if a < e {
                        if j > a {
                            lemma_tail_first(s, a, j);
                            lemma_sep_chars(10, s, k as int, e as int, a);
                        }
                    }
                }
                if j > k + 1 && s[j - 1] == 0x6E && ind_sep_digits(10, s, k as int, j - 1) {
                    if j - 1 < e {
                        lemma_sep_chars(10, s, k as int, e as int, j - 1);
                    } else {
                        assert(j - 1 == e);
                    }
                }
            }
        }
        Some((r, false, false))
    }
}

/// [`scan_numeric`], stated in the closed forms of `independent.rs`.
fn scan_numeric_ind(src: &[u32], k: usize) -> (r: Option<(usize, bool, bool)>)
    requires
        k < src.len(),
    ensures
        numeric_ind_result(src@, k as int, r),
{
    let c0 = peek(src, k);
    let c1 = peek(src, k.saturating_add(1));
    if c0 == 0x2E {
        // DecimalLiteral :: . DecimalDigits[+Sep] ExponentPart[+Sep]?
        if is_dec(c1) {
            num_dot(src, k)
        } else {
            proof {
                let s = src@;
                assert forall|j: int| !ind_numeric_literal(s, k as int, j) by {
                    lemma_shape_dot(s, k as int);
                    if ind_numeric_literal(s, k as int, j) {
                        let b = choose|b: int| #[trigger] ind_dl_alt2(s, k as int, j, b);
                    }
                }
            }
            None
        }
    } else if c0 == 0x30 {
        let c2 = peek(src, k.saturating_add(2));
        let radix: u32 = if c1 == 0x62 || c1 == 0x42 {
            2
        } else if c1 == 0x6F || c1 == 0x4F {
            8
        } else if c1 == 0x78 || c1 == 0x58 {
            16
        } else {
            0
        };
        if radix != 0 && is_radix(radix, c2) {
            num_prefix(src, k, radix)
        } else if c1 == 0x6E {
            // DecimalBigIntegerLiteral :: 0 BigIntLiteralSuffix
            proof {
                lemma_shape_zero_n(src@, k as int);
            }
            Some((k.saturating_add(2), true, false))
        } else if is_dec(c1) {
            num_zero_digit(src, k)
        } else {
            // DecimalIntegerLiteral :: 0
            proof {
                let s = src@;
                assert(!prefix_digit(s, k as int));
                lemma_shape_zero_alone(s, k as int);
            }
            Some((scan_decimal_tail(src, k.saturating_add(1)), false, false))
        }
    } else if is_dec(c0) {
        // DecimalIntegerLiteral :: NonZeroDigit NumericLiteralSeparator?
        // DecimalDigits[+Sep], or a DecimalBigIntegerLiteral.
        num_nonzero(src, k)
    } else {
        proof {
            let s = src@;
            assert forall|j: int| !ind_numeric_literal(s, k as int, j) by {
                lemma_decimal_literal_tail(s, k as int, j);
                if ind_decimal_literal(s, k as int, j) {
                    if !(exists|b: int| #[trigger] ind_dl_alt2(s, k as int, j, b)) {
                        let a = choose|a: int| #![trigger ind_decimal_integer(s, k as int, a)]
                            k < a && ind_decimal_integer(s, k as int, a) && ind_tail(s, a, j);
                    }
                }
            }
        }
        None
    }
}

/// §12.9.3 `NumericLiteral` at `k`, the longest: its end, whether it is a
/// BigInt literal, and whether it is legacy (§12.9.3.1).
///
/// Proven: the end is a range the spec derives as a `NumericLiteral`
/// ([`numeric_literal`]) and no longer range is; `None` means no range is;
/// the two flags are [`numeric_literal_is_bigint`] and
/// [`numeric_literal_is_legacy`] of the range.
fn scan_numeric(src: &[u32], k: usize) -> (r: Option<(usize, bool, bool)>)
    requires
        k < src.len(),
    ensures
        match r {
            Some((e, bigint, legacy)) => k < e <= src.len() && numeric_literal(
                src@,
                k as int,
                e as int,
            ) && (forall|j: int| numeric_literal(src@, k as int, j) ==> j <= e) && bigint
                == numeric_literal_is_bigint(src@, k as int, e as int) && legacy
                == numeric_literal_is_legacy(src@, k as int, e as int),
            None => forall|j: int| !numeric_literal(src@, k as int, j),
        },
{
    let r = scan_numeric_ind(src, k);
    proof {
        match r {
            Some((e, bigint, legacy)) => {
                lemma_numeric_literal_equiv(src@, k as int, e as int);
                lemma_flags_equiv(src@, k as int, e as int);
                assert forall|j: int| numeric_literal(src@, k as int, j) implies j <= e by {
                    lemma_numeric_literal_equiv(src@, k as int, j);
                }
            },
            None => {
                assert forall|j: int| !numeric_literal(src@, k as int, j) by {
                    lemma_numeric_literal_equiv(src@, k as int, j);
                }
            },
        }
    }
    r
}

/// §12.9.3: "The SourceCharacter immediately following a NumericLiteral
/// must not be an IdentifierStart or DecimalDigit."
///
/// Proven: it is [`numeric_literal_follow_error`] (an `IdentifierStart`
/// that is a `UnicodeEscapeSequence` included; above U+007F, the spec's
/// `ID_Start` is the table of [`super::unicode`]).
fn numeric_follow_error(src: &[u32], j: usize) -> (r: bool)
    requires
        j <= src.len(),
    ensures
        r == numeric_literal_follow_error(src@, j as int),
{
    let c = peek(src, j);
    proof {
        let s = src@;
        if j < s.len() {
            assert(c == s[j as int]);
            if is_decimal_digit(c) {
                assert(numeric_literal_follow_error(s, j as int));
            }
        }
    }
    if is_dec(c) || id_start_char(c) {
        proof {
            let s = src@;
            if j < s.len() && !is_decimal_digit(c) {
                assert(identifier_start(s, j as int, j as int + 1));
            }
        }
        true
    } else if c == 0x5C {
        let esc = scan_unicode_escape(src, j.saturating_add(1));
        proof {
            let s = src@;
            if esc is Some {
                let e = esc.unwrap().1;
                lemma_unicode_escape_equiv(s, j as int + 1, e as int);
                assert(identifier_start(s, j as int, e as int));
            } else {
                assert forall|k: int| !(j < k <= s.len() && identifier_start(s, j as int, k)) by {
                    if j < k <= s.len() && identifier_start(s, j as int, k) {
                        lemma_unicode_escape_equiv(s, j as int + 1, k);
                    }
                }
            }
        }
        esc.is_some()
    } else {
        proof {
            let s = src@;
            assert forall|k: int| !(j < k <= s.len() && identifier_start(s, j as int, k)) by {}
            if j < s.len() {
                assert(!is_decimal_digit(s[j as int]));
            }
        }
        false
    }
}

// ---------------------------------------------------------------------
// §12.9.4 String Literals
// ---------------------------------------------------------------------

/// §12.9.4 `LegacyOctalEscapeSequence` at `k`, whose first digit `d` is an
/// octal digit: its MV, pushed as one code unit, and its end. The
/// lookaheads make it the longest run its first digit allows: three digits
/// after `0` to `3`, two after `4` to `7`.
///
/// Proven: it is the `LegacyOctalEscapeSequence` the spec derives at `k`
/// (given that a leading `0` has an octal digit after it, the other cases
/// being `0` alone), and the code unit pushed is its MV.
fn scan_legacy_octal_escape(src: &[u32], k: usize, units: &mut Vec<u16>) -> (r: usize)
    requires
        k < src.len(),
        is_octal_digit(src@[k as int]),
        src@[k as int] != 0x30 || (k + 1 < src.len() && is_octal_digit(src@[k as int + 1])),
    ensures
        k < r <= src.len(),
        legacy_octal_escape_sequence(src@, k as int, r as int),
        final(units)@ =~= old(units)@ + seq![legacy_octal_escape_sequence_mv(
            src@,
            k as int,
            r as int,
        ) as u16],
{
    let d = peek(src, k);
    let mut v: u32 = d.saturating_sub(0x30);
    let mut e = k.saturating_add(1);
    let c1 = peek(src, e);
    if is_oct(c1) {
        v = v.saturating_mul(8).saturating_add(c1.saturating_sub(0x30));
        e = e.saturating_add(1);
        let c2 = peek(src, e);
        if d <= 0x33 && is_oct(c2) {
            v = v.saturating_mul(8).saturating_add(c2.saturating_sub(0x30));
            e = e.saturating_add(1);
        }
    }
    units.push(v as u16);
    e
}

/// §12.9.4 `\ EscapeSequence` or `LineContinuation`, the backslash at
/// `k`: appends the SV (§12.9.4.2) and returns the end.
///
/// Proven: `Some(e)` is the one end of a `StringCharacter` (an escape) at
/// `k` that the spec derives, and what is appended is its SV; `None` means
/// the spec derives none.
fn scan_string_escape(src: &[u32], k: usize, units: &mut Vec<u16>) -> (r: Option<usize>)
    requires
        k < src.len(),
        src@[k as int] == 0x5C,
    ensures
        match r {
            Some(e) => k + 1 < e <= src.len() && exists|v: Seq<u16>|
                string_character_sv(src@, k as int, e as int, 0x22, v) && final(units)@
                    =~= old(units)@ + v,
            None => forall|e: int, v: Seq<u16>| !string_character_sv(src@, k as int, e, 0x22, v),
        },
{
    let m = k.saturating_add(1);
    let d = peek(src, m);
    proof {
        lemma_is_lit(src@, m as int, m as int + 2, seq!['u', '{']);
    }
    if is_lt(d) {
        // LineContinuation: the empty String.
        let e = line_terminator_sequence_end(src, m);
        proof {
            assert(line_continuation(src@, k as int, e as int));
            assert(string_character_sv(
                src@,
                k as int,
                e as int,
                0x22,
                Seq::<u16>::empty(),
            ));
            assert(units@ =~= old(units)@ + Seq::<u16>::empty());
        }
        Some(e)
    } else if d == 0x27 || d == 0x22 || d == 0x5C {
        // SingleEscapeCharacter ' " \: the character itself.
        units.push(d as u16);
        proof {
            let v = seq![d as u16];
            assert(character_escape_sequence_sv(src@, m as int, m as int + 1, v));
            assert(string_character_sv(src@, k as int, m as int + 1, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(m.saturating_add(1))
    } else if d == 0x62 || d == 0x66 || d == 0x6E || d == 0x72 || d == 0x74 || d == 0x76 {
        // SingleEscapeCharacter b f n r t v (Table "String Single Character
        // Escape Sequences").
        let u: u16 = if d == 0x62 {
            0x08
        } else if d == 0x74 {
            0x09
        } else if d == 0x6E {
            0x0A
        } else if d == 0x76 {
            0x0B
        } else if d == 0x66 {
            0x0C
        } else {
            0x0D
        };
        units.push(u);
        proof {
            let v = seq![u];
            assert(u == single_escape_code_unit(d));
            assert(character_escape_sequence_sv(src@, m as int, m as int + 1, v));
            assert(string_character_sv(src@, k as int, m as int + 1, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(m.saturating_add(1))
    } else if d == 0x30 && !is_dec(peek(src, m.saturating_add(1))) {
        // `0` [lookahead ∉ DecimalDigit]: 0x0000.
        units.push(0);
        proof {
            let v = seq![0u16];
            assert(template_escape_sequence_sv(src@, m as int, m as int + 1, v));
            assert(string_character_sv(src@, k as int, m as int + 1, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(m.saturating_add(1))
    } else if d == 0x30 && !is_oct(peek(src, m.saturating_add(1))) {
        // LegacyOctalEscapeSequence :: `0` [lookahead ∈ { 8, 9 }]: 0.
        units.push(0);
        proof {
            let v = seq![0u16];
            assert(legacy_octal_escape_sequence(src@, m as int, m as int + 1));
            assert(legacy_octal_escape_sequence_mv(src@, m as int, m as int + 1) == 0);
            assert(escape_sequence_sv(src@, m as int, m as int + 1, v));
            assert(string_character_sv(src@, k as int, m as int + 1, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(m.saturating_add(1))
    } else if is_oct(d) {
        // LegacyOctalEscapeSequence, the other alternatives.
        let e = scan_legacy_octal_escape(src, m, units);
        proof {
            let v = seq![legacy_octal_escape_sequence_mv(src@, m as int, e as int) as u16];
            assert(escape_sequence_sv(src@, m as int, e as int, v));
            assert(string_character_sv(src@, k as int, e as int, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(e)
    } else if d == 0x38 || d == 0x39 {
        // NonOctalDecimalEscapeSequence: 0x0038 or 0x0039.
        units.push(d as u16);
        proof {
            let v = seq![d as u16];
            assert(escape_sequence_sv(src@, m as int, m as int + 1, v));
            assert(string_character_sv(src@, k as int, m as int + 1, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(m.saturating_add(1))
    } else if d == 0x78 {
        // HexEscapeSequence :: x HexDigit HexDigit
        let a = peek(src, m.saturating_add(1));
        let b = peek(src, m.saturating_add(2));
        if is_hex(a) && is_hex(b) {
            units.push(hex_val(a).saturating_mul(16).saturating_add(hex_val(b)) as u16);
            proof {
                let s = src@;
                reveal_with_fuel(hex_digits_mv, 3);
                let v = seq![hex_digits_mv(s, m as int + 1, m as int + 3) as u16];
                assert(hex_escape_sequence(s, m as int, m as int + 3));
                assert(escape_sequence_sv(s, m as int, m as int + 3, v));
                assert(string_character_sv(s, k as int, m as int + 3, 0x22, v));
                assert(units@ =~= old(units)@ + v);
            }
            Some(m.saturating_add(3))
        } else {
            proof {
                assert forall|e: int, v: Seq<u16>| !string_character_sv(src@, k as int, e, 0x22, v) by {
                    if string_character_sv(src@, k as int, e, 0x22, v) {
                        assert(!hex_escape_sequence(src@, m as int, e));
                        assert(!line_continuation(src@, k as int, e));
                    }
                }
            }
            None
        }
    } else if d == 0x75 {
        // UnicodeEscapeSequence: UTF16EncodeCodePoint of its MV.
        match scan_unicode_escape(src, m) {
            Some((cp, e)) => {
                push_utf16(units, cp);
                proof {
                    let s = src@;
                    lemma_unicode_escape_equiv(s, m as int, e as int);
                    let v = utf16_encode_code_point(cp as int);
                    assert(unicode_escape_sequence(s, m as int, e as int));
                    assert(v =~= unicode_escape_sv(s, m as int, e as int)) by {
                        if s[m as int + 1] != 0x7B {
                            assert(cp <= 0xFFFF);
                        }
                    }
                    assert(escape_sequence_sv(s, m as int, e as int, v));
                    assert(string_character_sv(s, k as int, e as int, 0x22, v));
                    assert(units@ =~= old(units)@ + v);
                }
                Some(e)
            },
            None => {
                proof {
                    assert forall|e: int, v: Seq<u16>|
                        !string_character_sv(src@, k as int, e, 0x22, v) by {
                        lemma_unicode_escape_equiv(src@, m as int, e);
                        if string_character_sv(src@, k as int, e, 0x22, v) {
                            assert(!line_continuation(src@, k as int, e));
                        }
                    }
                }
                None
            },
        }
    } else if is_src(d) {
        // NonEscapeCharacter: the code point.
        push_utf16(units, d);
        proof {
            let v = utf16_encode_code_point(d as int);
            assert(character_escape_sequence_sv(src@, m as int, m as int + 1, v));
            assert(string_character_sv(src@, k as int, m as int + 1, 0x22, v));
            assert(units@ =~= old(units)@ + v);
        }
        Some(m.saturating_add(1))
    } else {
        proof {
            assert forall|e: int, v: Seq<u16>| !string_character_sv(src@, k as int, e, 0x22, v) by {
                if string_character_sv(src@, k as int, e, 0x22, v) {
                    assert(!line_continuation(src@, k as int, e));
                }
            }
        }
        None
    }
}

/// §12.9.4 `StringLiteral` at `k` (a quote): its SV and its end.
///
/// Proven: `Some((units, e))` is the one `StringLiteral` the spec derives at
/// `k`, and `units` is its SV ([`string_literal_sv`]); `None` means the
/// spec derives none.
fn scan_string(src: &[u32], k: usize) -> (r: Option<(Vec<u16>, usize)>)
    requires
        k < src.len(),
        src@[k as int] == 0x22 || src@[k as int] == 0x27,
    ensures
        match r {
            Some((units, e)) => k + 2 <= e <= src.len() && string_literal_sv(
                src@,
                k as int,
                e as int,
                units@,
            ) && (forall|j: int| string_literal(src@, k as int, j) ==> j == e),
            None => forall|j: int| !string_literal(src@, k as int, j),
        },
{
    let quote = peek(src, k);
    let mut units: Vec<u16> = Vec::new();
    let mut j = k.saturating_add(1);
    proof {
        lemma_str_init(src@, k as int + 1, quote);
    }
    loop
        invariant
            k < j <= src.len(),
            quote == src@[k as int],
            quote == 0x22 || quote == 0x27,
            str_inv(src@, k as int + 1, j as int, quote, units@),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == quote {
            proof {
                lemma_str_quote(src@, k as int + 1, j as int, quote, units@, k as int);
            }
            return Some((units, j.saturating_add(1)));
        } else if c == 0x5C {
            let ghost before = units@;
            match scan_string_escape(src, j, &mut units) {
                Some(e) => {
                    proof {
                        let v = choose|v: Seq<u16>|
                            string_character_sv(src@, j as int, e as int, 0x22, v) && units@
                                =~= before + v;
                        lemma_esc_q_free(src@, j as int, e as int, 0x22, quote, v);
                        lemma_str_step(src@, k as int + 1, j as int, e as int, quote, before, v);
                    }
                    j = e;
                },
                None => {
                    proof {
                        assert forall|m: int, v: Seq<u16>|
                            !string_character_sv(src@, j as int, m, quote, v) by {
                            if string_character_sv(src@, j as int, m, quote, v) {
                                lemma_esc_q_free(src@, j as int, m, quote, 0x22, v);
                            }
                        }
                        lemma_str_no_char(src@, k as int + 1, j as int, quote, before, k as int);
                    }
                    return None;
                },
            }
        } else if c == 0x2028 || c == 0x2029 {
            // <LS>, <PS>: the code unit.
            let ghost before = units@;
            units.push(c as u16);
            proof {
                assert(string_character_sv(
                    src@,
                    j as int,
                    j as int + 1,
                    quote,
                    seq![c as u16],
                ));
                assert(units@ =~= before + seq![c as u16]);
                lemma_str_step(
                    src@,
                    k as int + 1,
                    j as int,
                    j as int + 1,
                    quote,
                    before,
                    seq![c as u16],
                );
            }
            j = j.saturating_add(1);
        } else if is_line_char(c) {
            // SourceCharacter but not one of the quote or \ or
            // LineTerminator.
            let ghost before = units@;
            push_utf16(&mut units, c);
            proof {
                let v = utf16_encode_code_point(c as int);
                assert(string_character_sv(src@, j as int, j as int + 1, quote, v));
                assert(units@ =~= before + v);
                lemma_str_step(src@, k as int + 1, j as int, j as int + 1, quote, before, v);
            }
            j = j.saturating_add(1);
        } else {
            proof {
                lemma_str_no_char(src@, k as int + 1, j as int, quote, units@, k as int);
            }
            return None;
        }
    }
}

// ---------------------------------------------------------------------
// §12.9.5 Regular Expression Literals
// ---------------------------------------------------------------------

/// §12.9.5 `RegularExpressionClass` at `k` (a `[`): its end.
fn scan_regexp_class(src: &[u32], k: usize) -> (r: Option<usize>)
    requires
        k < src.len(),
    ensures
        match r {
            Some(e) => k < e <= src.len(),
            None => true,
        },
{
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x5D {
            return Some(j.saturating_add(1));
        } else if c == 0x5C {
            // RegularExpressionBackslashSequence
            if is_line_char(peek(src, j.saturating_add(1))) {
                j = j.saturating_add(2);
            } else {
                return None;
            }
        } else if is_line_char(c) {
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

/// §12.9.5 `RegularExpressionLiteral` at `k` (a `/`): the index of the
/// closing `/` and the end of the flags.
fn scan_regexp(src: &[u32], k: usize) -> (r: Option<(usize, usize)>)
    requires
        k < src.len(),
    ensures
        match r {
            Some((b, e)) => k + 1 < b < e <= src.len(),
            None => true,
        },
{
    let first = peek(src, k.saturating_add(1));
    // RegularExpressionFirstChar is not `*` or `/`.
    if first == 0x2A || first == 0x2F {
        return None;
    }
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
            j == k + 1 ==> (k + 1 >= src.len() || src@[(k + 1) as int] != 0x2F),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x2F {
            // The closing `/`, then RegularExpressionFlags.
            let mut f = j.saturating_add(1);
            loop
                invariant
                    k + 1 < j < f <= src.len(),
                decreases src.len() - f,
            {
                if id_part_char(peek(src, f)) {
                    f = f.saturating_add(1);
                } else {
                    return Some((j, f));
                }
            }
        } else if c == 0x5C {
            if is_line_char(peek(src, j.saturating_add(1))) {
                j = j.saturating_add(2);
            } else {
                return None;
            }
        } else if c == 0x5B {
            match scan_regexp_class(src, j) {
                Some(e) => {
                    j = e;
                },
                None => {
                    return None;
                },
            }
        } else if is_line_char(c) {
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

// ---------------------------------------------------------------------
// §12.9.6 Template Literal Lexical Components
// ---------------------------------------------------------------------

/// A template component's TV (`None` once a `NotEscapeSequence` makes it
/// *undefined*) and TRV, as they are built.
struct TemplateValues {
    cooked: Vec<u16>,
    defined: bool,
    raw: Vec<u16>,
}

/// §12.9.6 `\ TemplateEscapeSequence`, `\ NotEscapeSequence` or
/// `LineContinuation`, the backslash at `k`: appends the TV and TRV
/// (§12.9.6.1, §12.9.6.2) and returns the end.
fn scan_template_escape(src: &[u32], k: usize, values: &mut TemplateValues) -> (r: Option<usize>)
    requires
        k < src.len(),
    ensures
        match r {
            Some(e) => k + 1 < e <= src.len(),
            None => true,
        },
{
    let m = k.saturating_add(1);
    let d = peek(src, m);
    if is_lt(d) {
        // LineContinuation: TV is empty; TRV is \ and the TRV of the
        // LineTerminatorSequence (<CR><LF> and <CR> are <LF>).
        let e = line_terminator_sequence_end(src, m);
        values.raw.push(0x5C);
        if d == 0x2028 || d == 0x2029 {
            values.raw.push(d as u16);
        } else {
            values.raw.push(0x0A);
        }
        return Some(e);
    }
    // In every other case the TRV is the UTF-16 of the matched code points.
    let e: usize;
    if d == 0x27 || d == 0x22 || d == 0x5C {
        values.cooked.push(d as u16);
        e = m.saturating_add(1);
    } else if d == 0x62 || d == 0x66 || d == 0x6E || d == 0x72 || d == 0x74 || d == 0x76 {
        let u: u16 = if d == 0x62 {
            0x08
        } else if d == 0x74 {
            0x09
        } else if d == 0x6E {
            0x0A
        } else if d == 0x76 {
            0x0B
        } else if d == 0x66 {
            0x0C
        } else {
            0x0D
        };
        values.cooked.push(u);
        e = m.saturating_add(1);
    } else if d == 0x30 {
        if is_dec(peek(src, m.saturating_add(1))) {
            // NotEscapeSequence :: 0 DecimalDigit
            values.defined = false;
            e = m.saturating_add(2);
        } else {
            // TemplateEscapeSequence :: 0 [lookahead ∉ DecimalDigit]
            values.cooked.push(0);
            e = m.saturating_add(1);
        }
    } else if is_dec(d) {
        // NotEscapeSequence :: DecimalDigit but not 0
        values.defined = false;
        e = m.saturating_add(1);
    } else if d == 0x78 {
        let a = peek(src, m.saturating_add(1));
        let b = peek(src, m.saturating_add(2));
        if is_hex(a) && is_hex(b) {
            // HexEscapeSequence
            values.cooked.push(hex_val(a).saturating_mul(16).saturating_add(hex_val(b)) as u16);
            e = m.saturating_add(3);
        } else if is_hex(a) {
            // NotEscapeSequence :: x HexDigit [lookahead ∉ HexDigit]
            values.defined = false;
            e = m.saturating_add(2);
        } else {
            // NotEscapeSequence :: x [lookahead ∉ HexDigit]
            values.defined = false;
            e = m.saturating_add(1);
        }
    } else if d == 0x75 {
        match scan_unicode_escape(src, m) {
            Some((cp, end)) => {
                // UnicodeEscapeSequence
                push_utf16(&mut values.cooked, cp);
                e = end;
            },
            None => {
                // NotEscapeSequence, alternatives 5 to 11: `u` and the hex
                // digits that follow (up to three), or `u{` and all of
                // them; each ends where no further hex digit follows.
                values.defined = false;
                if peek(src, m.saturating_add(1)) == 0x7B {
                    let (_, h) = scan_hex_digits(src, m.saturating_add(2));
                    e = h;
                } else {
                    let mut h = m.saturating_add(1);
                    while is_hex(peek(src, h)) && h < m.saturating_add(4)
                        invariant
                            m < h <= src.len(),
                        decreases src.len() - h,
                    {
                        h = h.saturating_add(1);
                    }
                    e = h;
                }
            },
        }
    } else if is_src(d) {
        // CharacterEscapeSequence :: NonEscapeCharacter
        push_utf16(&mut values.cooked, d);
        e = m.saturating_add(1);
    } else {
        return None;
    }
    push_range_utf16(&mut values.raw, src, k, e);
    Some(e)
}

/// What [`scan_template`] finds: whether the component closes with `` ` ``,
/// its TV (`None` for *undefined*), its TRV, and its end.
type TemplateScan = (bool, Option<Vec<u16>>, Vec<u16>, usize);

/// §12.9.6 a template component at `k` (`` ` `` for `NoSubstitutionTemplate`
/// and `TemplateHead`, `}` for `TemplateMiddle` and `TemplateTail`): whether
/// it closes with `` ` `` (rather than `${`), its TV and TRV, and its end.
fn scan_template(src: &[u32], k: usize) -> (r: Option<TemplateScan>)
    requires
        k < src.len(),
    ensures
        match r {
            Some((_, _, _, e)) => k + 2 <= e <= src.len(),
            None => true,
        },
{
    let mut values = TemplateValues { cooked: Vec::new(), defined: true, raw: Vec::new() };
    let mut j = k.saturating_add(1);
    loop
        invariant
            k < j <= src.len(),
        decreases src.len() - j,
    {
        let c = peek(src, j);
        if c == 0x60 || (c == 0x24 && peek(src, j.saturating_add(1)) == 0x7B) {
            let closes = c == 0x60;
            let end = if closes {
                j.saturating_add(1)
            } else {
                j.saturating_add(2)
            };
            let cooked = if values.defined {
                Some(values.cooked)
            } else {
                None
            };
            return Some((closes, cooked, values.raw, end));
        } else if c == 0x5C {
            match scan_template_escape(src, j, &mut values) {
                Some(e) => {
                    j = e;
                },
                None => {
                    return None;
                },
            }
        } else if is_lt(c) {
            // LineTerminatorSequence: TV and TRV are its TRV.
            let e = line_terminator_sequence_end(src, j);
            let u: u16 = if c == 0x2028 || c == 0x2029 {
                c as u16
            } else {
                0x0A
            };
            values.cooked.push(u);
            values.raw.push(u);
            j = e;
        } else if is_src(c) {
            // `$` [lookahead ≠ {], or SourceCharacter but not one of ` \ $
            // LineTerminator: UTF16EncodeCodePoint of it.
            push_utf16(&mut values.cooked, c);
            push_utf16(&mut values.raw, c);
            j = j.saturating_add(1);
        } else {
            return None;
        }
    }
}

// ---------------------------------------------------------------------
// §12 The goal symbols and the longest input element.
// ---------------------------------------------------------------------

/// The goal has `RegularExpressionLiteral`.
fn goal_regexp(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementRegExp || goal == Goal::InputElementRegExpOrTemplateTail
            || goal == Goal::InputElementHashbangOrRegExp),
{
    matches!(
        goal,
        Goal::InputElementRegExp | Goal::InputElementRegExpOrTemplateTail
            | Goal::InputElementHashbangOrRegExp
    )
}

/// The goal has `DivPunctuator`.
fn goal_div(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementDiv || goal == Goal::InputElementTemplateTail),
{
    matches!(goal, Goal::InputElementDiv | Goal::InputElementTemplateTail)
}

/// The goal has `RightBracePunctuator`.
fn goal_right_brace(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementDiv || goal == Goal::InputElementRegExp),
{
    matches!(goal, Goal::InputElementDiv | Goal::InputElementRegExp)
}

/// The goal has `TemplateSubstitutionTail`.
fn goal_template_tail(goal: Goal) -> (r: bool)
    ensures
        r == (goal == Goal::InputElementRegExpOrTemplateTail || goal
            == Goal::InputElementTemplateTail),
{
    matches!(goal, Goal::InputElementRegExpOrTemplateTail | Goal::InputElementTemplateTail)
}

/// An element with no value.
fn plain(kind: ElementKind, start: usize, end: usize) -> (r: Element)
    requires
        !(kind == ElementKind::IdentifierName || kind == ElementKind::PrivateIdentifier || kind
            == ElementKind::StringLiteral || kind == ElementKind::NumericLiteral || kind
            == ElementKind::RegularExpressionLiteral || kind == ElementKind::Template(
            TemplateKind::NoSubstitution,
        ) || kind == ElementKind::Template(TemplateKind::Head) || kind == ElementKind::Template(
            TemplateKind::Middle,
        ) || kind == ElementKind::Template(TemplateKind::Tail)),
    ensures
        r.kind == kind,
        r.start == start,
        r.end == end,
        value_shape_agrees(r),
{
    Element { kind, start, end, value: Value::None }
}

/// An element and the error that the checks after the longest element is
/// chosen raise for it, if any (§12.9.3, §12.7.1.1; [`lex_error`]).
type Candidate = (Element, Option<LexError>);

/// The candidate's element is a non-empty range at `pos`.
pub open spec fn candidate_ok(src: Seq<u32>, pos: usize, c: (Element, Option<LexError>)) -> bool {
    c.0.start == pos && pos < c.0.end <= src.len() && value_shape_agrees(c.0) && c.1
        != Some(LexError::NoInputElement) && (c.1 == Some(LexError::IdentifierAfterNumericLiteral)
        ==> c.0.kind == ElementKind::NumericLiteral) && (c.0.kind == ElementKind::NumericLiteral
        ==> ((c.1 == Some(LexError::IdentifierAfterNumericLiteral))
        == numeric_literal_follow_error(src, c.0.end as int))) && (c.1 == Some(
        LexError::InvalidIdentifierEscape) ==> (c.0.kind == ElementKind::IdentifierName
        || c.0.kind == ElementKind::PrivateIdentifier)) && (c.0.kind
        == ElementKind::IdentifierName ==> ((c.1 == Some(LexError::InvalidIdentifierEscape))
        == !identifier_name_valid(src, pos as int, c.0.end as int))) && (c.0.kind
        == ElementKind::PrivateIdentifier ==> ((c.1 == Some(LexError::InvalidIdentifierEscape))
        == !identifier_name_valid(src, pos as int + 1, c.0.end as int)))
}

/// The end of a candidate, or `pos` if there is none.
pub open spec fn cand_end(pos: usize, r: Option<Candidate>) -> int {
    match r {
        Some(c) => c.0.end as int,
        None => pos as int,
    }
}

/// [`candidate_ok`], and [`kind_agrees_proven`] in the goal.
pub open spec fn candidate_agrees(
    goal: Goal,
    html: bool,
    src: Seq<u32>,
    pos: usize,
    c: (Element, Option<LexError>),
) -> bool {
    candidate_ok(src, pos, c) && kind_agrees_proven(goal, html, src, c.0) && value_agrees_proven(
        src,
        c.0,
    )
}

/// The longer of two candidates (the first on a tie).
fn longer(a: Option<Candidate>, b: Option<Candidate>) -> (r: Option<Candidate>)
    ensures
        match a {
            Some(x) => match b {
                Some(y) => r == Some(x) || r == Some(y),
                None => r == Some(x),
            },
            None => r == b,
        },
        a is Some ==> r is Some && r.unwrap().0.end >= a.unwrap().0.end,
        b is Some ==> r is Some && r.unwrap().0.end >= b.unwrap().0.end,
{
    match (a, b) {
        (Some(x), Some(y)) => {
            if y.0.end > x.0.end {
                Some(y)
            } else {
                Some(x)
            }
        },
        (Some(x), None) => Some(x),
        (None, y) => y,
    }
}

/// A comment that starts with `/` at `pos`: `//` (§12.4
/// `SingleLineComment`) or `/*` (§12.4 `MultiLineComment`; with `html`,
/// Annex B.1.1's `SingleLineDelimitedComment`, or its `MultiLineComment`
/// with an optional `HTMLCloseComment` after the `*/` when the comment
/// holds a `LineTerminator`).
fn lex_slash_comment(src: &[u32], pos: usize, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x2F,
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind == ElementKind::Comment && (!html
                ==> (comment(src@, pos as int, c.0.end as int, false) && forall|j: int|
                j <= src.len() && #[trigger] comment(src@, pos as int, j, false) ==> j
                    <= c.0.end)),
            None => !html ==> forall|j: int| !comment(src@, pos as int, j, false),
        },
{
    let c1 = peek(src, pos.saturating_add(1));
    if c1 == 0x2F {
        let e = scan_line_chars(src, pos.saturating_add(2));
        proof {
            // `//` and no LineTerminator: `SingleLineComment`; and it cannot
            // be longer, since `src[e]` is a LineTerminator or past the end.
            lemma_single_line_comment_equiv(src@, pos as int, e as int);
            lemma_comment_plain_equiv(src@, pos as int, e as int);
            assert(ind_single_line_comment(src@, pos as int, e as int));
            assert forall|j: int| j <= src.len() && #[trigger] comment(src@, pos as int, j, false)
                implies j <= e by {
                lemma_comment_plain_equiv(src@, pos as int, j);
                lemma_single_line_comment_equiv(src@, pos as int, j);
                if j > e {
                    assert(ind_single_line_comment(src@, pos as int, j) || ind_multi_line_comment(
                        src@,
                        pos as int,
                        j,
                    ));
                    if ind_single_line_comment(src@, pos as int, j) {
                        assert(ind_src_cp(src@[e as int]) && !ind_lt_cp(src@[e as int]));
                    } else {
                        assert(src@[pos as int + 1] == 0x2A);
                    }
                }
            }
        }
        Some((plain(ElementKind::Comment, pos, e), None))
    } else if c1 == 0x2A {
        match scan_block_comment(src, pos.saturating_add(2), true) {
            Some((e, lt)) => {
                proof {
                    lemma_multi_line_comment_equiv(src@, pos as int, e as int);
                    lemma_comment_plain_equiv(src@, pos as int, e as int);
                    assert(ind_multi_line_comment(src@, pos as int, e as int));
                    assert forall|j: int|
                        j <= src.len() && #[trigger] comment(src@, pos as int, j, false)
                            implies j <= e by {
                        lemma_comment_plain_equiv(src@, pos as int, j);
                        lemma_multi_line_comment_equiv(src@, pos as int, j);
                        lemma_single_line_comment_equiv(src@, pos as int, j);
                        if ind_multi_line_comment(src@, pos as int, j) {
                            assert(block_close_ok(src@, pos as int + 2, j, true));
                        }
                    }
                }
                let end = if html && lt {
                    match scan_html_close(src, e) {
                        Some(f) => f,
                        None => e,
                    }
                } else {
                    e
                };
                Some((plain(ElementKind::Comment, pos, end), None))
            },
            None => {
                proof {
                    assert forall|j: int| !comment(src@, pos as int, j, false) by {
                        lemma_comment_plain_equiv(src@, pos as int, j);
                        lemma_multi_line_comment_equiv(src@, pos as int, j);
                        lemma_single_line_comment_equiv(src@, pos as int, j);
                        if ind_multi_line_comment(src@, pos as int, j) {
                            assert(block_close_ok(src@, pos as int + 2, j, true));
                        }
                    }
                }
                None
            },
        }
    } else {
        proof {
            assert forall|j: int| !comment(src@, pos as int, j, false) by {
                lemma_comment_plain_equiv(src@, pos as int, j);
                lemma_multi_line_comment_equiv(src@, pos as int, j);
                lemma_single_line_comment_equiv(src@, pos as int, j);
            }
        }
        None
    }
}

/// `Comment` of §12.4 (not Annex B's) is a `MultiLineComment` or a
/// `SingleLineComment`, in the closed forms of `independent.rs`.
proof fn lemma_comment_plain_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        comment(s, i, j, false) <==> (ind_multi_line_comment(s, i, j) || ind_single_line_comment(
            s,
            i,
            j,
        )),
{
    lemma_multi_line_comment_equiv(s, i, j);
    lemma_single_line_comment_equiv(s, i, j);
}

/// What the dispatch of [`lex_common`] proves of each branch: the candidate
/// agrees with the spec for its kind, no derivation of another proven kind
/// is longer ([`pk_bounded`]), and no numeric literal starts at `pos` unless
/// the candidate is one.
pub open spec fn lex_result_ok(
    src: Seq<u32>,
    pos: usize,
    goal: Goal,
    html: bool,
    r: Option<Candidate>,
) -> bool {
    (match r {
        Some(c) => candidate_agrees(goal, html, src, pos, c),
        None => true,
    }) && pk_bounded(goal, html, src, pos as int, cand_end(pos, r)) && ((r is None
        || r.unwrap().0.kind != ElementKind::NumericLiteral) ==> numeric_absent(src, pos as int))
        && ((r is None || r.unwrap().0.kind != ElementKind::IdentifierName) ==> ident_absent(
        src,
        pos as int,
    )) && ((r is None || r.unwrap().0.kind != ElementKind::PrivateIdentifier) ==> private_absent(
        src,
        pos as int,
    ))
}

/// A `WhiteSpace` at `pos` (§12.2).
fn lex_ws(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        start_ok(ElementKind::WhiteSpace, src@, pos as int),
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (src, goal, html);
    // WhiteSpace
    assert(white_space(src@, pos as int, pos + 1));
    let ws = Some((plain(ElementKind::WhiteSpace, pos, pos.saturating_add(1)), None));
    proof {
        let el = ws.unwrap().0;
        assert forall|j: int|
            j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                el.kind,
                src@,
                pos as int,
                j,
            ) implies j <= el.end by {
            assert(white_space(src@, pos as int, j));
        }
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::WhiteSpace,
                src@,
                pos as int,
                j,
            ) implies j <= pos + 1 by {
            assert(white_space(src@, pos as int, j));
        }
        lemma_ws_lt_not_id_start(src@[pos as int]);
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::WhiteSpace implies !start_ok(k, src@, pos as int) by {}
        lemma_pk_one(goal, html, src@, pos as int, pos as int + 1, ElementKind::WhiteSpace);
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    ws
}

/// A `LineTerminator` at `pos` (§12.3); with `html`, Annex B.1.1's
/// `SingleLineHTMLCloseComment` if it is longer.
fn lex_lt(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        start_ok(ElementKind::LineTerminator, src@, pos as int),
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    // LineTerminator; with `html`, Annex B.1.1's
    // SingleLineHTMLCloseComment :: LineTerminatorSequence
    // HTMLCloseComment, which is longer when it matches.
    let lt = Some((plain(ElementKind::LineTerminator, pos, pos.saturating_add(1)), None));
    proof {
        let el = lt.unwrap().0;
        assert(line_terminator(src@, pos as int, pos + 1));
        assert forall|j: int|
            j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                el.kind,
                src@,
                pos as int,
                j,
            ) implies j <= el.end by {
            assert(line_terminator(src@, pos as int, j));
        }
    }
    let r = if html {
        let s = line_terminator_sequence_end(src, pos);
        longer(lt, html_close_candidate(src, pos, s))
    } else {
        lt
    };
    proof {
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::LineTerminator,
                src@,
                pos as int,
                j,
            ) implies j <= pos + 1 by {
            assert(line_terminator(src@, pos as int, j));
        }
        lemma_ws_lt_not_id_start(src@[pos as int]);
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::LineTerminator implies !start_ok(k, src@, pos as int) by {}
        lemma_pk_one(
            goal,
            html,
            src@,
            pos as int,
            r.unwrap().0.end as int,
            ElementKind::LineTerminator,
        );
    }
    r
}

/// An alternative that starts with `/`: a comment, a regular expression
/// literal or a `DivPunctuator`.
fn lex_slash(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x2F,
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    let c1 = peek(src, pos.saturating_add(1));
    // Comment, RegularExpressionLiteral or DivPunctuator.
    let cmt = lex_slash_comment(src, pos, html);
    proof {
        if let Some(ref cm) = cmt {
            let el = cm.0;
            if !html {
                assert(element_matches(goal, html, ElementKind::Comment, src@, pos as int, el.end as int));
                assert forall|j: int|
                    j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        el.kind,
                        src@,
                        pos as int,
                        j,
                    ) implies j <= el.end by {
                    assert(comment(src@, pos as int, j, false));
                }
            }
        }
    }
    let ghost cmt_end: int = cand_end(pos, cmt);
    let regexp = if goal_regexp(goal) {
        regexp_candidate(src, pos)
    } else {
        None
    };
    let gd = goal_div(goal);
    let div = if gd {
        let e = if c1 == 0x3D {
            // DivPunctuator :: `/=`
            assert(src@.subrange(pos as int, pos + 2) =~= seq!['/', '='].map_values(
                |c: char| c as u32,
            ));
            pos.saturating_add(2)
        } else {
            // DivPunctuator :: `/`
            assert(src@.subrange(pos as int, pos + 1) =~= seq!['/'].map_values(
                |c: char| c as u32,
            ));
            pos.saturating_add(1)
        };
        assert(div_punctuator(src@, pos as int, e as int));
        let d = Some((plain(ElementKind::DivPunctuator, pos, e), None));
        proof {
            let el = d.unwrap().0;
            assert forall|j: int|
                j <= src.len() && #[trigger] element_matches(
                    goal,
                    html,
                    el.kind,
                    src@,
                    pos as int,
                    j,
                ) implies j <= el.end by {
                lemma_div_punctuator_equiv(src@, pos as int, j);
                lemma_div_punctuator_equiv(src@, pos as int, e as int);
            }
        }
        d
    } else {
        None
    };
    let ghost div_end: int = cand_end(pos, div);
    let inner = longer(cmt, regexp);
    let r = longer(inner, div);
    proof {
        let e = cand_end(pos, r);
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::DivPunctuator,
                src@,
                pos as int,
                j,
            ) implies j <= e by {
            // `div` is the DivPunctuator candidate exactly when the goal has one.
            assert(gd);
            assert(div is Some);
            assert(j <= div_end);
        }
        assert forall|j: int|
            pos < j <= src.len() && kind_proven(ElementKind::Comment, html)
                && #[trigger] element_matches(
                goal,
                html,
                ElementKind::Comment,
                src@,
                pos as int,
                j,
            ) implies j <= e by {
            assert(!html);
            assert(comment(src@, pos as int, j, false));
            assert(cmt_end >= j);
        }
        assert forall|k: ElementKind, j: int|
            pos < j <= src.len() && kind_proven(k, html) && k != ElementKind::HashbangComment
                && (k == ElementKind::Comment || k == ElementKind::DivPunctuator)
                && #[trigger] element_matches(goal, html, k, src@, pos as int, j) implies j
            <= e by {}
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && !(k
                == ElementKind::Comment || k == ElementKind::DivPunctuator) implies !start_ok(
            k,
            src@,
            pos as int,
        ) by {}
        lemma_pk_only(
            goal,
            html,
            src@,
            pos as int,
            e,
            ElementKind::Comment,
            ElementKind::DivPunctuator,
        );
    }
    r
}

/// An alternative that starts with `}`: `TemplateMiddle`, `TemplateTail` or
/// `RightBracePunctuator`.
fn lex_brace(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x7D,
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    // TemplateMiddle / TemplateTail or RightBracePunctuator.
    let gt = goal_template_tail(goal);
    let gr = goal_right_brace(goal);
    let r = if gt {
        lex_template(src, pos, true)
    } else if gr {
        // RightBracePunctuator :: `}`
        assert(src@.subrange(pos as int, pos + 1) =~= seq!['}'].map_values(
            |c: char| c as u32,
        ));
        assert(right_brace_punctuator(src@, pos as int, pos + 1));
        let rb = Some((plain(ElementKind::RightBracePunctuator, pos, pos.saturating_add(1)), None));
        proof {
            let el = rb.unwrap().0;
            assert forall|j: int|
                j <= src.len() && #[trigger] element_matches(
                    goal,
                    html,
                    el.kind,
                    src@,
                    pos as int,
                    j,
                ) implies j <= el.end by {
                lemma_right_brace_equiv(src@, pos as int, j);
            }
        }
        rb
    } else {
        None
    };
    proof {
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::RightBracePunctuator,
                src@,
                pos as int,
                j,
            ) implies j <= cand_end(pos, r) by {
            // Only the goals with `RightBracePunctuator` derive it, and then `r` is it.
            assert(gr);
            assert(!gt);
            lemma_right_brace_equiv(src@, pos as int, j);
        }
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::RightBracePunctuator implies !start_ok(
            k,
            src@,
            pos as int,
        ) by {}
        lemma_pk_one(
            goal,
            html,
            src@,
            pos as int,
            cand_end(pos, r),
            ElementKind::RightBracePunctuator,
        );
    }
    r
}

/// `NoSubstitutionTemplate` or `TemplateHead` at `pos`.
fn lex_backtick(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x60,
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    // NoSubstitutionTemplate / TemplateHead
    let r = lex_template(src, pos, false);
    proof {
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment implies !start_ok(
            k,
            src@,
            pos as int,
        ) by {}
        lemma_pk_none(goal, html, src@, pos as int, cand_end(pos, r));
    }
    r
}

/// A `StringLiteral` at `pos`.
fn lex_string(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x22 || src@[pos as int] == 0x27,
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    // StringLiteral
    match scan_string(src, pos) {
        Some((units, e)) => {
            proof {
                assert forall|j: int|
                    pos < j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        ElementKind::StringLiteral,
                        src@,
                        pos as int,
                        j,
                    ) implies j <= e by {}
                assert forall|k: ElementKind|
                    kind_proven(k, html) && k != ElementKind::HashbangComment && k
                        != ElementKind::StringLiteral implies !start_ok(
                    k,
                    src@,
                    pos as int,
                ) by {}
                lemma_pk_one(
                    goal,
                    html,
                    src@,
                    pos as int,
                    e as int,
                    ElementKind::StringLiteral,
                );
            }
            Some(
                (
                    Element {
                        kind: ElementKind::StringLiteral,
                        start: pos,
                        end: e,
                        value: Value::String { units },
                    },
                    None,
                ),
            )
        },
        None => {
            proof {
                assert forall|j: int|
                    pos < j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        ElementKind::StringLiteral,
                        src@,
                        pos as int,
                        j,
                    ) implies j <= pos by {}
                assert forall|k: ElementKind|
                    kind_proven(k, html) && k != ElementKind::HashbangComment && k
                        != ElementKind::StringLiteral implies !start_ok(
                    k,
                    src@,
                    pos as int,
                ) by {}
                lemma_pk_one(
                    goal,
                    html,
                    src@,
                    pos as int,
                    pos as int,
                    ElementKind::StringLiteral,
                );
            }
            None
        },
    }
}

/// A `PrivateIdentifier` at `pos`.
fn lex_hash(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x23,
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    // PrivateIdentifier :: # IdentifierName
    let r = match scan_identifier(src, pos.saturating_add(1)) {
        Some((cps, escaped, valid, e)) => {
            let err = if valid {
                None
            } else {
                Some(LexError::InvalidIdentifierEscape)
            };
            Some(
                (
                    Element {
                        kind: ElementKind::PrivateIdentifier,
                        start: pos,
                        end: e,
                        value: Value::Name { code_points: cps, escaped },
                    },
                    err,
                ),
            )
        },
        None => None,
    };
    proof {
        let s = src@;
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::PrivateIdentifier implies !start_ok(k, s, pos as int) by {}
        lemma_ident_absent_from_class(s, pos as int);
        match r {
            Some((ref el, ref err)) => {
                let e = el.end as int;
                let cps = value_name_cps(el.value);
                assert(identifier_name_cps(s, pos as int + 1, e, cps));
                lemma_name_valid_iff(s, pos as int + 1, e, cps);
                assert(identifier_name(s, pos as int + 1, e));
                assert(private_identifier(s, pos as int, e));
                assert forall|j: int|
                    pos < j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        ElementKind::PrivateIdentifier,
                        s,
                        pos as int,
                        j,
                    ) implies j <= e by {
                    lemma_name_longest(s, pos as int + 1, j, e);
                }
                lemma_pk_one(goal, html, s, pos as int, e, ElementKind::PrivateIdentifier);
            },
            None => {
                assert forall|j: int|
                    pos < j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        ElementKind::PrivateIdentifier,
                        s,
                        pos as int,
                        j,
                    ) implies j <= pos by {
                    lemma_ident_absent_from_scan(s, pos as int + 1);
                    reveal(ident_absent);
                    assert(identifier_name(s, pos as int + 1, j));
                }
                lemma_pk_one(goal, html, s, pos as int, pos as int, ElementKind::PrivateIdentifier);
                lemma_ident_absent_from_scan(s, pos as int + 1);
                lemma_private_absent_from_next(s, pos as int);
            },
        }
    }
    r
}

/// A `NumericLiteral` at `pos`.
fn lex_numeric(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        start_ok(ElementKind::NumericLiteral, src@, pos as int),
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    // NumericLiteral
    proof {
            lemma_numeric_derivable(src@, pos as int);
    }
    match scan_numeric(src, pos) {
        Some((e, bigint, legacy)) => {
            proof {
                assert forall|k: ElementKind, j: int|
                    pos < j <= src.len() && kind_proven(k, html) && k
                        != ElementKind::HashbangComment && (k == ElementKind::NumericLiteral
                        || k == ElementKind::Punctuator) && #[trigger] element_matches(
                        goal,
                        html,
                        k,
                        src@,
                        pos as int,
                        j,
                    ) implies j <= e by {
                    if k == ElementKind::Punctuator {
                        lemma_first_cp(goal, html, k, src@, pos as int, j);
                        if src@[pos as int] == 0x2E {
                            lemma_punct_dot_digit(src@, pos as int, j);
                        }
                    }
                }
                assert forall|k: ElementKind|
                    kind_proven(k, html) && k != ElementKind::HashbangComment && !(k
                        == ElementKind::NumericLiteral || k == ElementKind::Punctuator)
                        implies !start_ok(k, src@, pos as int) by {}
                lemma_pk_only(
                    goal,
                    html,
                    src@,
                    pos as int,
                    e as int,
                    ElementKind::NumericLiteral,
                    ElementKind::Punctuator,
                );
            }
            let follow = numeric_follow_error(src, e);
            let err = if follow {
                Some(LexError::IdentifierAfterNumericLiteral)
            } else {
                None
            };
            Some(
                (
                    Element {
                        kind: ElementKind::NumericLiteral,
                        start: pos,
                        end: e,
                        value: Value::Numeric { bigint, legacy },
                    },
                    err,
                ),
            )
        },
        None => {
            // A numeric literal is derived at every start (`3`, `.5`), so
            // the scanner cannot fail here.
            proof {
                let j = choose|j: int| pos < j <= src.len() && numeric_literal(
                    src@,
                    pos as int,
                    j,
                );
                assert(false);
            }
            None
        },
    }
}

/// An `IdentifierName` at `pos`, if the code point there is `\` or an
/// `IdentifierStartChar`.
fn lex_ident(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        src@[pos as int] == 0x5C || is_identifier_start_char(src@[pos as int]),
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    // IdentifierName
    let r = match scan_identifier(src, pos) {
        Some((cps, escaped, valid, e)) => {
            let err = if valid {
                None
            } else {
                Some(LexError::InvalidIdentifierEscape)
            };
            Some(
                (
                    Element {
                        kind: ElementKind::IdentifierName,
                        start: pos,
                        end: e,
                        value: Value::Name { code_points: cps, escaped },
                    },
                    err,
                ),
            )
        },
        None => None,
    };
    proof {
        let s = src@;
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::IdentifierName implies !start_ok(k, s, pos as int) by {
            if start_ok(k, s, pos as int) {
                if k == ElementKind::WhiteSpace || k == ElementKind::LineTerminator {
                    lemma_ws_lt_not_id_start(s[pos as int]);
                }
            }
        }
        lemma_private_absent_from_class(s, pos as int);
        match r {
            Some((ref el, ref err)) => {
                let e = el.end as int;
                let cps = value_name_cps(el.value);
                assert(identifier_name_cps(s, pos as int, e, cps));
                lemma_name_valid_iff(s, pos as int, e, cps);
                assert(identifier_name(s, pos as int, e));
                assert forall|j: int|
                    pos < j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        ElementKind::IdentifierName,
                        s,
                        pos as int,
                        j,
                    ) implies j <= e by {
                    lemma_name_longest(s, pos as int, j, e);
                }
                lemma_pk_one(goal, html, s, pos as int, e, ElementKind::IdentifierName);
            },
            None => {
                lemma_ident_absent_from_scan(s, pos as int);
                assert forall|j: int|
                    pos < j <= src.len() && #[trigger] element_matches(
                        goal,
                        html,
                        ElementKind::IdentifierName,
                        s,
                        pos as int,
                        j,
                    ) implies j <= pos by {
                    reveal(ident_absent);
                    assert(identifier_name(s, pos as int, j));
                }
                lemma_pk_one(goal, html, s, pos as int, pos as int, ElementKind::IdentifierName);
            },
        }
    }
    r
}

/// Annex B.1.1 `SingleLineHTMLOpenComment` at `pos`.
fn lex_html_open(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        html,
        src@[pos as int] == 0x3C,
        pos + 3 < src.len(),
        src@[pos as int + 1] == 0x21,
        src@[pos as int + 2] == 0x2D,
        src@[pos as int + 3] == 0x2D,
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    // Annex B.1.1 SingleLineHTMLOpenComment :: <!-- SingleLineCommentChars?
    let e = scan_line_chars(src, pos.saturating_add(4));
    proof {
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::Punctuator,
                src@,
                pos as int,
                j,
            ) implies j <= e by {
            lemma_punct_lt_bang(src@, pos as int, j);
        }
        assert forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::Punctuator implies !start_ok(k, src@, pos as int) by {}
        lemma_pk_one(goal, html, src@, pos as int, e as int, ElementKind::Punctuator);
    }
    Some((plain(ElementKind::Comment, pos, e), None))
}

/// A `Punctuator` at `pos`, where no other proven kind can start.
fn lex_punct(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
        forall|k: ElementKind|
            kind_proven(k, html) && k != ElementKind::HashbangComment && k
                != ElementKind::Punctuator ==> !start_ok(k, src@, pos as int),
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let _ = (goal, html);
    proof {
        assert(kind_proven(ElementKind::IdentifierName, html));
        assert(kind_proven(ElementKind::PrivateIdentifier, html));
        let _ = start_ok(ElementKind::IdentifierName, src@, pos as int);
        let _ = start_ok(ElementKind::PrivateIdentifier, src@, pos as int);
        assert(!start_ok(ElementKind::IdentifierName, src@, pos as int));
        assert(!start_ok(ElementKind::PrivateIdentifier, src@, pos as int));
        lemma_ident_absent_from_class(src@, pos as int);
        lemma_private_absent_from_class(src@, pos as int);
    }
    // Punctuator
    let e = scan_punctuator(src, pos);
    let r = if e > pos {
        let pu = Some((plain(ElementKind::Punctuator, pos, e), None));
        proof {
            let el = pu.unwrap().0;
            assert forall|j: int|
                j <= src.len() && #[trigger] element_matches(
                    goal,
                    html,
                    el.kind,
                    src@,
                    pos as int,
                    j,
                ) implies j <= el.end by {
                assert(punctuator(src@, pos as int, j));
            }
        }
        pu
    } else {
        None
    };
    proof {
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::Punctuator,
                src@,
                pos as int,
                j,
            ) implies j <= cand_end(pos, r) by {
            assert(punctuator(src@, pos as int, j));
        }
        lemma_pk_one(
            goal,
            html,
            src@,
            pos as int,
            cand_end(pos, r),
            ElementKind::Punctuator,
        );
    }
    r
}

/// Every alternative of `goal` that can start with the code point at
/// `pos`, the longest of them: the dispatch on the first code point.
fn lex_common(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        lex_result_ok(src@, pos, goal, html, r),
{
    let c = peek(src, pos);
    let c1 = peek(src, pos.saturating_add(1));
    proof {
        assert(at_decimal_digit(src@, pos as int + 1) == is_decimal_digit(c1));
    }
    if is_ws(c) {
        lex_ws(src, pos, goal, html)
    } else if is_lt(c) {
        lex_lt(src, pos, goal, html)
    } else if c == 0x2F {
        lex_slash(src, pos, goal, html)
    } else if c == 0x7D {
        lex_brace(src, pos, goal, html)
    } else if c == 0x60 {
        lex_backtick(src, pos, goal, html)
    } else if c == 0x22 || c == 0x27 {
        lex_string(src, pos, goal, html)
    } else if c == 0x23 {
        lex_hash(src, pos, goal, html)
    } else if is_dec(c) || (c == 0x2E && is_dec(c1)) {
        lex_numeric(src, pos, goal, html)
    } else if c == 0x5C || id_start_char(c) {
        lex_ident(src, pos, goal, html)
    } else if html && c == 0x3C && c1 == 0x21 && peek(src, pos.saturating_add(2)) == 0x2D && peek(
        src,
        pos.saturating_add(3),
    ) == 0x2D {
        lex_html_open(src, pos, goal, html)
    } else {
        proof {
            assert forall|k: ElementKind|
                kind_proven(k, html) && k != ElementKind::HashbangComment && k
                    != ElementKind::Punctuator implies !start_ok(k, src@, pos as int) by {}
        }
        lex_punct(src, pos, goal, html)
    }
}

/// A template component at `pos`: `NoSubstitutionTemplate` or
/// `TemplateHead` after `` ` ``, `TemplateTail` or `TemplateMiddle` after
/// `}` (`substitution_tail`).
fn lex_template(src: &[u32], pos: usize, substitution_tail: bool) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind is Template,
            None => true,
        },
{
    match scan_template(src, pos) {
        Some((closes, cooked, raw, e)) => {
            let kind = if substitution_tail {
                if closes {
                    TemplateKind::Tail
                } else {
                    TemplateKind::Middle
                }
            } else {
                if closes {
                    TemplateKind::NoSubstitution
                } else {
                    TemplateKind::Head
                }
            };
            Some(
                (
                    Element {
                        kind: ElementKind::Template(kind),
                        start: pos,
                        end: e,
                        value: Value::Template { cooked, raw },
                    },
                    None,
                ),
            )
        },
        None => None,
    }
}

/// The alternatives of `InputElementHashbangOrRegExp` that match only at
/// the start of the source text: `HashbangComment` (§12.5) and, with
/// `html`, Annex B.1.1's `HTMLCloseComment`.
fn lex_start(src: &[u32], html: bool) -> (r: Option<Candidate>)
    requires
        0 < src.len(),
    ensures
        match r {
            Some(c) => candidate_agrees(Goal::InputElementHashbangOrRegExp, html, src@, 0, c),
            None => true,
        },
        hb_bounded(Goal::InputElementHashbangOrRegExp, html, src@, 0, cand_end(0, r)),
        (r is Some && r.unwrap().0.kind == ElementKind::HashbangComment) ==> src@[0] == 0x23
            && 1 < src@.len() && src@[1] == 0x21,
        r is Some ==> r.unwrap().0.kind == ElementKind::HashbangComment || (r.unwrap().0.kind
            == ElementKind::Comment && html),
{
    let hashbang = if peek(src, 0) == 0x23 && peek(src, 1) == 0x21 {
        // §12.5 HashbangComment :: `#!` SingleLineCommentChars?
        let e = scan_line_chars(src, 2);
        assert(src@.subrange(0, 2) =~= seq!['#', '!'].map_values(|c: char| c as u32));
        assert(hashbang_comment(src@, 0, e as int));
        Some((plain(ElementKind::HashbangComment, 0, e), None))
    } else {
        None
    };
    let close = if html {
        html_close_candidate(src, 0, 0)
    } else {
        None
    };
    let ghost hb_end: int = cand_end(0, hashbang);
    let r = longer(hashbang, close);
    proof {
        // A hashbang comment is `#!` and the code points up to the first
        // line terminator (or the end); `hashbang` is the longest of them.
        assert forall|j: int|
            0 < j <= src.len() && #[trigger] element_matches(
                Goal::InputElementHashbangOrRegExp,
                html,
                ElementKind::HashbangComment,
                src@,
                0,
                j,
            ) implies j <= cand_end(0, r) by {
            lemma_hashbang_comment_equiv(src@, 0, j);
            assert(hashbang is Some);
            assert(j <= hb_end);
        }
    }
    r
}

/// A `Comment` from `pos` to the end of the Annex B.1.1 `HTMLCloseComment`
/// at `k`, if one is there.
fn html_close_candidate(src: &[u32], pos: usize, k: usize) -> (r: Option<Candidate>)
    requires
        pos <= k <= src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind == ElementKind::Comment,
            None => true,
        },
{
    let e = scan_html_close(src, k)?;
    Some((plain(ElementKind::Comment, pos, e), None))
}

/// A `RegularExpressionLiteral` at `pos`, if one is there.
fn regexp_candidate(src: &[u32], pos: usize) -> (r: Option<Candidate>)
    requires
        pos < src.len(),
    ensures
        match r {
            Some(c) => candidate_ok(src@, pos, c) && c.0.kind
                == ElementKind::RegularExpressionLiteral,
            None => true,
        },
{
    let (b, e) = scan_regexp(src, pos)?;
    Some(
        (
            Element {
                kind: ElementKind::RegularExpressionLiteral,
                start: pos,
                end: e,
                value: Value::RegExp { body_end: b },
            },
            None,
        ),
    )
}

/// The next input element of `goal` at `pos`, trivia included (§12): the
/// longest alternative, then the checks [`lex_error`] makes of it.
///
/// Proven: [`next_input_element_proven`] (totality and span coverage).
/// Not proven: the rest of [`super::contract::next_input_element_ensures`];
/// see the module header.
pub fn next_input_element(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Result<
    Step,
    LexError,
>)
    requires
        pos <= src.len(),
    ensures
        next_input_element_proven(src@, pos, goal, html, r),
{
    if pos >= src.len() {
        return Ok(Step::Eof);
    }
    let common = lex_common(src, pos, goal, html);
    let use_start = pos == 0 && matches!(goal, Goal::InputElementHashbangOrRegExp);
    let start = if use_start {
        lex_start(src, html)
    } else {
        None
    };
    let ghost ce: int = cand_end(pos, common);
    let ghost se: int = cand_end(pos, start);
    let best = if use_start {
        longer(common, start)
    } else {
        common
    };
    proof {
        let be = cand_end(pos, best);
        assert(be >= ce && be >= se);
        lemma_pk_mono(goal, html, src@, pos as int, ce, be);
        assert forall|j: int|
            pos < j <= src.len() && #[trigger] element_matches(
                goal,
                html,
                ElementKind::HashbangComment,
                src@,
                pos as int,
                j,
            ) implies j <= be by {
            // Only the start of the source text has a hashbang comment.
            assert(use_start);
            assert(j <= se);
        }
        if best is Some && kind_proven(best.unwrap().0.kind, html) && best.unwrap().0.kind
            != ElementKind::NumericLiteral {
            if best == common {
                assert(numeric_absent(src@, pos as int));
            } else {
                // `start`'s candidate: a hashbang comment, which starts with `#`.
                assert(best == start);
                assert(use_start);
                assert(src@[0] == 0x23);
                lemma_numeric_absent_from_class(src@, 0);
            }
        }
        if best is Some && kind_proven(best.unwrap().0.kind, html) {
            if best != common {
                // `start`'s candidate: a hashbang comment, `#!`.
                assert(best == start);
                assert(use_start);
                assert(src@[0] == 0x23 && 1 < src@.len() && src@[1] == 0x21);
                lemma_ident_absent_from_class(src@, 0);
                lemma_ident_absent_from_class(src@, 1);
                lemma_private_absent_from_next(src@, 0);
            }
        }
    }
    match best {
        None => {
            proof {
                assert(proven_bounded(goal, html, src@, pos as int, pos as int));
                assert(next_input_element_proven(
                    src@,
                    pos,
                    goal,
                    html,
                    Err::<Step, LexError>(LexError::NoInputElement),
                ));
            }
            Err(LexError::NoInputElement)
        },
        Some((el, None)) => {
            proof {
                assert(candidate_agrees(goal, html, src@, pos, (el, None::<LexError>)));
                assert(candidate_ok(src@, pos, (el, None::<LexError>)));
                assert(kind_agrees_proven(goal, html, src@, el));
                assert(value_agrees_proven(src@, el));
                assert(kind_proven(el.kind, html) ==> proven_bounded(
                    goal,
                    html,
                    src@,
                    pos as int,
                    el.end as int,
                ));
                assert(kind_proven(el.kind, html) && el.kind != ElementKind::NumericLiteral
                    ==> numeric_absent(src@, pos as int));
                assert(el.kind == ElementKind::NumericLiteral ==> !numeric_literal_follow_error(
                    src@,
                    el.end as int,
                ));
                assert(kind_proven(el.kind, html) && el.kind != ElementKind::IdentifierName
                    ==> ident_absent(src@, pos as int));
                assert(kind_proven(el.kind, html) && el.kind != ElementKind::PrivateIdentifier
                    ==> private_absent(src@, pos as int));
                assert(el.kind == ElementKind::IdentifierName ==> identifier_name_valid(
                    src@,
                    pos as int,
                    el.end as int,
                ));
                assert(el.kind == ElementKind::PrivateIdentifier ==> identifier_name_valid(
                    src@,
                    pos as int + 1,
                    el.end as int,
                ));
            }
            Ok(Step::Element(el))
        },
        Some((el, Some(e))) => {
            let _ = &el;
            proof {
                if e == LexError::IdentifierAfterNumericLiteral {
                    // The candidate is the numeric literal, and the bound is the one of `best`.
                    assert(el.kind == ElementKind::NumericLiteral);
                    let end = el.end as int;
                    assert(pos < end <= src.len());
                    assert(element_matches(
                        goal,
                        html,
                        ElementKind::NumericLiteral,
                        src@,
                        pos as int,
                        end,
                    ));
                    assert(proven_bounded(goal, html, src@, pos as int, end));
                    assert(numeric_literal_follow_error(src@, end));
                }
                if e == LexError::InvalidIdentifierEscape {
                    // The candidate is the identifier, and the bound is the one of `best`.
                    assert(el.kind == ElementKind::IdentifierName || el.kind
                        == ElementKind::PrivateIdentifier);
                    assert(kind_proven(el.kind, html));
                    let end = el.end as int;
                    assert(pos < end <= src.len());
                    assert(element_matches(goal, html, el.kind, src@, pos as int, end));
                    assert(proven_bounded(goal, html, src@, pos as int, end));
                    assert(numeric_absent(src@, pos as int));
                    assert(invalid_identifier_at(goal, html, src@, pos as int, end));
                }
            }
            proof {
                assert(candidate_agrees(goal, html, src@, pos, (el, Some(e))));
                assert(e != LexError::NoInputElement);
                assert(next_input_element_proven(src@, pos, goal, html, Err::<Step, LexError>(e)));
            }
            Err(e)
        },
    }
}

/// Whether a code point of `src[i..j)` is a `LineTerminator`: whether the
/// trivia element on that range "is a LineTerminator" for the syntactic
/// grammar (§12.3, §12.4, Annex B.1.1).
fn range_has_lt(src: &[u32], i: usize, j: usize) -> (r: bool)
    requires
        i <= j <= src.len(),
    ensures
        r == contains_line_terminator(src@, i as int, j as int),
{
    let mut k = i;
    while k < j
        invariant
            i <= k <= j <= src.len(),
            forall|m: int| i <= m < k ==> !is_line_terminator(#[trigger] src@[m]),
        decreases j - k,
    {
        if is_lt(peek(src, k)) {
            return true;
        }
        k = k.saturating_add(1);
    }
    false
}

/// Whether an element kind is trivia ([`is_trivia`]).
fn trivia(kind: ElementKind) -> (r: bool)
    ensures
        r == is_trivia(kind),
{
    matches!(
        kind,
        ElementKind::WhiteSpace | ElementKind::LineTerminator | ElementKind::Comment
            | ElementKind::HashbangComment
    )
}

/// The next token of `goal` at `pos`: [`next_input_element`] repeated over
/// trivia, with the line-terminator flag ASI needs (§12.10).
///
/// Proven: [`next_token_proven`]. Not proven: the rest of
/// [`super::contract::next_token_ensures`]; see the module header.
pub fn next_token(src: &[u32], pos: usize, goal: Goal, html: bool) -> (r: Result<Next, LexError>)
    requires
        pos <= src.len(),
    ensures
        next_token_proven(src@, pos, goal, html, r),
{
    let mut p = pos;
    let mut newline = false;
    loop
        invariant
            pos <= p <= src.len(),
            newline == contains_line_terminator(src@, pos as int, p as int),
        decreases src.len() - p,
    {
        match next_input_element(src, p, goal, html) {
            Err(e) => {
                return Err(e);
            },
            Ok(Step::Eof) => {
                return Ok(Next::Eof { newline_before: newline });
            },
            Ok(Step::Element(el)) => {
                if trivia(el.kind) {
                    proof {
                        super::lemmas::lemma_contains_lt_split(
                            src@,
                            pos as int,
                            p as int,
                            el.end as int,
                        );
                    }
                    if range_has_lt(src, el.start, el.end) {
                        newline = true;
                    }
                    p = el.end;
                } else {
                    return Ok(Next::Token(Token { element: el, newline_before: newline }));
                }
            },
        }
    }
}

} // verus!
