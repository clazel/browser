//! Executable-style specification of the ECMAScript lexical grammar,
//! transcribed from ECMA-262, 2026 edition (`es2026`), §11.1 "Source Text",
//! §12 "ECMAScript Language: Lexical Grammar" and Annex B.1.1 "HTML-like
//! Comments", at commit `0248456c758431e4bb8e5d26333ff1865123c9cd` of
//! <https://github.com/tc39/ecma262> (31 March 2026; `SPEC-PIN.md`).
//! Section numbers below are the ones that `spec.html` numbers at that
//! commit. Nothing here runs; it defines what "correct" means. Every
//! definition cites the standard, and each `// N.` comment is the step or
//! alternative number in the cited production or algorithm (a production's
//! alternatives are numbered from 1 in the order the standard lists them).
//!
//! # What this file covers
//!
//! The five lexical goal symbols (§12), `WhiteSpace`, `LineTerminator`,
//! `Comment` (§12.4, and Annex B.1.1's HTML-like comments, which are required
//! of a web browser), `HashbangComment` (§12.5), `CommonToken` (§12.6),
//! `IdentifierName`, `PrivateIdentifier` and `ReservedWord` (§12.7),
//! `Punctuator` (§12.8), `NumericLiteral` with separators, BigInt and legacy
//! forms (§12.9.3), `StringLiteral` and the string value SV (§12.9.4),
//! `RegularExpressionLiteral`, lexical part only (§12.9.5), the template
//! literal lexical components with TV and TRV (§12.9.6), and the rule that
//! the lexer takes the longest input element (§12 intro).
//!
//! # What it leaves out
//!
//! - The MV and NumericValue of numeric literals (§12.9.3.2, §12.9.3.3). A
//!   token carries its span; the number's value is computed from the span by
//!   the numbers item (phase-7.md 7.11, with StringToNumber), not by the
//!   lexer, so it is not part of what the lexer is proven to produce.
//! - Automatic semicolon insertion (§12.10), strict-mode early errors, the
//!   parse of a regular expression's body, and `NullLiteral` and
//!   `BooleanLiteral` (§12.9.1, §12.9.2), which are the keywords `null`,
//!   `true` and `false`, tokens the lexer returns as `IdentifierName`.
//! - Annex B.1.2 (regular expression patterns): a body is not parsed here.
//!
//! # Modelling choices
//!
//! Each one is a deliberate difference in form, never in meaning.
//!
//! - **Source text** is a `Seq<u32>` of code points (§11.1), the type
//!   `clazel-encoding` decodes to. `SourceCharacter` is `c <= 0x10FFFF`
//!   ([`is_source_character`]), surrogate code points included, so every
//!   `Seq<u32>` is a legal argument: a value above U+10FFFF matches no
//!   production and is a lexical error, rather than a precondition.
//! - **A production is a relation on a range.** `X(s, i, j)` says that the
//!   code points `s[i..j)` are derived by nonterminal `X` in the source text
//!   `s`. All nonterminals derive a non-empty range except those the
//!   standard writes with an `[empty]` alternative; an optional symbol
//!   `Y?` is `a == b || Y(s, a, b)` over its range `[a, b)`. A right-hand
//!   side that is a sequence `A B` is an existential over the split point.
//!   This is the grammar as the standard gives it, so every production can
//!   be compared with the standard's line by line, and it is the only place
//!   where "derived by" is defined; no deterministic scanner appears here.
//! - **Lookahead** `[lookahead != x]`, `[lookahead ∈ S]` reads `s[j]`, the code
//!   point after the derived range, in the whole source text (the
//!   "immediately following input"); it fails to match at the end of the
//!   source text.
//! - **Parameters** `[Sep]` on the digit productions are the Boolean `sep`
//!   (`[+Sep]` is `true`). `BinaryDigits`, `OctalDigits`, `DecimalDigits` and
//!   `HexDigits` have the same three alternatives over different digit
//!   classes, and are one function [`digits`] with the radix as a parameter;
//!   [`binary_digits`] and the others name the instances the standard names.
//!   `DoubleStringCharacter` and `SingleStringCharacter` differ only in the
//!   excluded quote, so they are one function with a `quote` parameter.
//! - **Values** (`IdentifierCodePoints`, SV, TV, TRV) are attributes of a
//!   derivation. They are written as relations too: `identifier_name_cps(s,
//!   i, j, cps)` says "`IdentifierName` derives `s[i..j)` and its
//!   IdentifierCodePoints is `cps`", `string_characters_sv(.., v)` says the
//!   same for SV, and so on. Each clause is the standard's rule for that
//!   production. The relation holds for exactly one value for each range
//!   the grammar derives; that is not assumed, and it is not needed for the
//!   contracts, which only say that the value returned stands in the
//!   relation to the range.
//! - **Template TRV of an escape sequence.** The TRV rules for
//!   `TemplateEscapeSequence` and `NotEscapeSequence` (§12.9.6.2) list, for
//!   each alternative, the string-concatenation of the code units of the
//!   code points it matches (a digit's TRV is UTF16EncodeCodePoint of that
//!   digit, and so on through `Hex4Digits`, `HexDigits`, `CodePoint`,
//!   `NotCodePoint`, `SingleEscapeCharacter` and `NonEscapeCharacter`). The
//!   twenty-odd rules therefore fold into [`utf16_of`], the UTF-16 encoding
//!   of the matched range, used at the one step that holds them
//!   ([`template_character`] alternatives 2 and 3).
//! - **Strings are UTF-16.** String values are `Seq<u16>` code units, built
//!   with UTF16EncodeCodePoint (§11.1.1) and never decoded, so a lone
//!   surrogate (from `"\uD800"`, or a lone surrogate code point in the
//!   source) is an ordinary element.
//! - **Unicode properties.** The spec needs three properties of code points:
//!   `Space_Separator` (Zs), `ID_Start` and `ID_Continue`. Zs is a closed
//!   list of 17 code points that has not changed since Unicode 6.3, and is
//!   written out ([`unicode_space_separator`]). `ID_Start` and `ID_Continue`
//!   are large and change with every Unicode version; the standard says "the
//!   latest version of the Unicode Standard", with later additions
//!   permitted, so they are uninterpreted functions of the non-ASCII code
//!   points ([`unicode_id_start_non_ascii`] and
//!   [`unicode_id_continue_non_ascii`]), and the ASCII part, which does not
//!   change, is defined. The implementation (phase-7.md 7.2, second half)
//!   fixes a Unicode version in a generated table and has to tie it to
//!   these two functions; until then nothing is claimed about them.
//! - **The longest input element** (§12 intro: "repeatedly taking the
//!   longest possible sequence of code points as the next input element") is
//!   [`longest_len`], the largest length for which some alternative of the
//!   goal symbol derives the range, and the two checks that the standard
//!   words as constraints on a chosen element rather than as grammar:
//!   §12.9.3 "The SourceCharacter immediately following a NumericLiteral
//!   must not be an IdentifierStart or DecimalDigit" and §12.7.1.1's early
//!   errors for `IdentifierStart :: \ UnicodeEscapeSequence` and
//!   `IdentifierPart :: \ UnicodeEscapeSequence`. They are checked after the
//!   longest element is chosen, not used to pick a shorter one: `1.e` is an
//!   error, not `1` `.` `e`, as in every engine. A failure is a
//!   [`LexError`]; those two rules are the only early errors the lexer
//!   raises, because they depend on one token alone (the others, such as
//!   strict-mode octal, depend on context the parser has).
//! - **"IdentifierStart" after a numeric literal** is read as the
//!   nonterminal: the following code points must not start a derivation of
//!   `IdentifierStart`, so `3a` is an error as well as `3a`.
//! - **Goal symbols are alternatives, per the standard.** The goal is a
//!   parameter of every function. `HashbangComment` and Annex B's
//!   `HTMLCloseComment` alternative of `InputElementHashbangOrRegExp` match
//!   only at index 0: the standard says they are "location-sensitive" and
//!   the goal "is used at the start of a Script or Module".
//! - **Annex B.1.1 is a mode.** The boolean `html` says the source is parsed
//!   as a `Script`, where Annex B's `Comment` replaces §12.4's; it is
//!   `false` for a `Module`, which does not allow HTML-like comments.
//! - **A line terminator for the parser** (§12.4: "if a MultiLineComment
//!   contains a line terminator code point, then the entire comment is
//!   considered to be a LineTerminator", and Annex B: a
//!   `SingleLineHTMLCloseComment` is too) is [`contains_line_terminator`] on
//!   the range of a trivia element: the other trivia elements contain no
//!   line terminator code point except the `LineTerminator` itself.
//! - **Trivia** (white space, line terminators, comments) are input elements
//!   the syntactic grammar never sees. [`skip_trivia`] repeats the same goal
//!   symbol over them; that is sound because the goal depends on the
//!   syntactic context of the next token, which trivia do not change.
//!   `ReservedWord` is [`is_reserved_word`], a function of an identifier's
//!   code points; whether a given escape-free name is one is for the parser
//!   (§12.7.2: the early errors of §13.1.1).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §11.1 `ECMAScript source text` is a sequence of code points.
pub type Src = Seq<u32>;

// ---------------------------------------------------------------------
// Small helpers for reading the standard's notation.
// ---------------------------------------------------------------------

/// `s[k]` exists and is the code point `c`: a terminal symbol at `k`, and
/// the test of a `[lookahead = c]` (false at the end of the source text).
pub open spec fn at(s: Src, k: int, c: char) -> bool {
    0 <= k < s.len() && s[k] == c as u32
}

/// `s[i..j)` is exactly the code points of `lit`: a sequence of terminal
/// symbols such as `` `//` `` (and `[lookahead = ...]` of a string).
pub open spec fn is_lit(s: Src, i: int, j: int, lit: Seq<char>) -> bool {
    0 <= i && j <= s.len() && j - i == lit.len()
        && s.subrange(i, j) =~= lit.map_values(|c: char| c as u32)
}

/// `Y?` over the range `[a, b)` of a symbol that derives a non-empty range:
/// the range is empty, or `y` holds.
pub open spec fn opt(a: int, b: int, y: bool) -> bool {
    a == b || y
}

/// The range `[i, j)` is non-empty and inside the source text.
pub open spec fn nonempty(s: Src, i: int, j: int) -> bool {
    0 <= i && i < j && j <= s.len()
}

/// Every code point of `s[i..j)` satisfies `p`.
pub open spec fn all_of(s: Src, i: int, j: int, p: spec_fn(u32) -> bool) -> bool {
    forall|k: int| i <= k < j ==> p(#[trigger] s[k])
}

// ---------------------------------------------------------------------
// §11.1 Source Text
// ---------------------------------------------------------------------

/// §11.1 `SourceCharacter :: any Unicode code point`: U+0000 to U+10FFFF,
/// surrogate code points included.
pub open spec fn is_source_character(c: u32) -> bool {
    c <= 0x10FFFF
}

/// §11.1.1 UTF16EncodeCodePoint (_cp_).
pub open spec fn utf16_encode_code_point(cp: int) -> Seq<u16> {
    // 1. Assert: 0 ≤ cp ≤ 0x10FFFF.
    // 2. "If cp ≤ 0xFFFF, return the String value consisting of the code unit
    //    whose numeric value is cp."
    if cp <= 0xFFFF {
        seq![cp as u16]
    } else {
        // 3. Let cu1 be the code unit whose numeric value is
        //    floor((cp - 0x10000) / 0x400) + 0xD800.
        let cu1 = ((cp - 0x10000) / 0x400 + 0xD800) as u16;
        // 4. Let cu2 be the code unit whose numeric value is
        //    ((cp - 0x10000) modulo 0x400) + 0xDC00.
        let cu2 = ((cp - 0x10000) % 0x400 + 0xDC00) as u16;
        // 5. Return the string-concatenation of cu1 and cu2.
        seq![cu1, cu2]
    }
}

/// The UTF-16 encoding of `s[i..j)`: the string-concatenation of
/// UTF16EncodeCodePoint of each code point, as in §11.1.2 CodePointsToString.
pub open spec fn utf16_of(s: Src, i: int, j: int) -> Seq<u16>
    decreases j - i,
{
    if i >= j {
        seq![]
    } else {
        utf16_encode_code_point(s[i] as int) + utf16_of(s, i + 1, j)
    }
}

// ---------------------------------------------------------------------
// §12 Lexical grammar: the goal symbols.
// ---------------------------------------------------------------------

/// The lexical goal symbols (§12): which input elements the next element may
/// be. The syntactic grammar chooses one for every token.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Goal {
    /// `InputElementDiv`: the default.
    InputElementDiv,
    /// `InputElementRegExp`: a `RegularExpressionLiteral` is permitted.
    InputElementRegExp,
    /// `InputElementRegExpOrTemplateTail`: a `RegularExpressionLiteral`,
    /// `TemplateMiddle` or `TemplateTail` is permitted.
    InputElementRegExpOrTemplateTail,
    /// `InputElementTemplateTail`: a `TemplateMiddle` or `TemplateTail` is
    /// permitted.
    InputElementTemplateTail,
    /// `InputElementHashbangOrRegExp`: the start of a `Script` or `Module`.
    InputElementHashbangOrRegExp,
}

/// The kind of a template literal lexical component (§12.9.6).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TemplateKind {
    /// `NoSubstitutionTemplate :: ` TemplateCharacters? ```.
    NoSubstitution,
    /// `TemplateHead :: ` TemplateCharacters? ${`.
    Head,
    /// `TemplateMiddle :: } TemplateCharacters? ${`.
    Middle,
    /// `TemplateTail :: } TemplateCharacters? ```.
    Tail,
}

/// The input elements a goal symbol derives (§12). The standard's
/// alternatives that are tokens named by `CommonToken` are listed
/// separately, so that a result says which one it is.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ElementKind {
    /// `WhiteSpace`.
    WhiteSpace,
    /// `LineTerminator`.
    LineTerminator,
    /// `Comment`, and Annex B's `HTMLCloseComment` where the goal has it.
    Comment,
    /// `HashbangComment`.
    HashbangComment,
    /// `IdentifierName` (`CommonToken`).
    IdentifierName,
    /// `PrivateIdentifier` (`CommonToken`).
    PrivateIdentifier,
    /// `Punctuator` (`CommonToken`).
    Punctuator,
    /// `NumericLiteral` (`CommonToken`).
    NumericLiteral,
    /// `StringLiteral` (`CommonToken`).
    StringLiteral,
    /// `Template` (`CommonToken`): `NoSubstitution` or `Head`; or
    /// `TemplateSubstitutionTail`: `Middle` or `Tail`.
    Template(TemplateKind),
    /// `DivPunctuator`.
    DivPunctuator,
    /// `RightBracePunctuator`.
    RightBracePunctuator,
    /// `RegularExpressionLiteral`.
    RegularExpressionLiteral,
}

// ---------------------------------------------------------------------
// §12.2 White Space; §12.3 Line Terminators
// ---------------------------------------------------------------------

/// Table "White Space Code Points" (§12.2), the `<USP>` row: any code point
/// in general category "Space_Separator". The category is the closed list
/// of Zs code points (Unicode 6.3 and later).
pub open spec fn unicode_space_separator(c: u32) -> bool {
    c == 0x0020 || c == 0x00A0 || c == 0x1680 || (0x2000 <= c <= 0x200A) || c == 0x202F
        || c == 0x205F || c == 0x3000
}

/// §12.2 `WhiteSpace :: <TAB> | <VT> | <FF> | <ZWNBSP> | <USP>`.
pub open spec fn white_space(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && j == i + 1 && (
        // 1. <TAB>
        s[i] == 0x0009
        // 2. <VT>
        || s[i] == 0x000B
        // 3. <FF>
        || s[i] == 0x000C
        // 4. <ZWNBSP>
        || s[i] == 0xFEFF
        // 5. <USP>
        || unicode_space_separator(s[i]))
}

/// §12.3 `LineTerminator :: <LF> | <CR> | <LS> | <PS>` as a code point.
pub open spec fn is_line_terminator(c: u32) -> bool {
    // <LF>, <CR>, <LS>, <PS>
    c == 0x000A || c == 0x000D || c == 0x2028 || c == 0x2029
}

/// §12.3 `LineTerminator`.
pub open spec fn line_terminator(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && j == i + 1 && is_line_terminator(s[i])
}

/// §12.3 `LineTerminatorSequence`.
pub open spec fn line_terminator_sequence(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. <LF>
        (j == i + 1 && s[i] == 0x000A)
        // 2. <CR> [lookahead != <LF>]
        || (j == i + 1 && s[i] == 0x000D && !at(s, j, '\n'))
        // 3. <LS>
        || (j == i + 1 && s[i] == 0x2028)
        // 4. <PS>
        || (j == i + 1 && s[i] == 0x2029)
        // 5. <CR> <LF>
        || (j == i + 2 && s[i] == 0x000D && s[i + 1] == 0x000A))
}

/// `SourceCharacter but not LineTerminator`.
pub open spec fn is_not_line_terminator(c: u32) -> bool {
    is_source_character(c) && !is_line_terminator(c)
}

// ---------------------------------------------------------------------
// §12.4 Comments, §12.5 Hashbang Comments
// ---------------------------------------------------------------------

/// §12.4 `SingleLineCommentChars :: SingleLineCommentChar
/// SingleLineCommentChars?`, with `SingleLineCommentChar :: SourceCharacter
/// but not LineTerminator`: one or more such code points (the right
/// recursion of a list of a one-code-point class is that class, repeated).
pub open spec fn single_line_comment_chars(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && all_of(s, i, j, |c: u32| is_not_line_terminator(c))
}

/// §12.4 `SingleLineComment :: `//` SingleLineCommentChars?`.
pub open spec fn single_line_comment(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, i + 2, seq!['/', '/']) && j >= i + 2
        && opt(i + 2, j, single_line_comment_chars(s, i + 2, j))
}

/// §12.4 `MultiLineCommentChars`.
pub open spec fn multi_line_comment_chars(s: Src, i: int, j: int) -> bool
    decreases j - i, 0int,
{
    nonempty(s, i, j) && (
        // 1. MultiLineNotAsteriskChar MultiLineCommentChars?
        (is_source_character(s[i]) && s[i] != '*' as u32
            && (j == i + 1 || multi_line_comment_chars(s, i + 1, j)))
        // 2. `*` PostAsteriskCommentChars?
        || (s[i] == '*' as u32 && (j == i + 1 || post_asterisk_comment_chars(s, i + 1, j))))
}

/// §12.4 `PostAsteriskCommentChars`.
pub open spec fn post_asterisk_comment_chars(s: Src, i: int, j: int) -> bool
    decreases j - i, 1int,
{
    nonempty(s, i, j) && (
        // 1. MultiLineNotForwardSlashOrAsteriskChar MultiLineCommentChars?
        (is_source_character(s[i]) && s[i] != '/' as u32 && s[i] != '*' as u32
            && (j == i + 1 || multi_line_comment_chars(s, i + 1, j)))
        // 2. `*` PostAsteriskCommentChars?
        || (s[i] == '*' as u32 && (j == i + 1 || post_asterisk_comment_chars(s, i + 1, j))))
}

/// §12.4 `MultiLineComment :: `/*` MultiLineCommentChars? `*/``.
pub open spec fn multi_line_comment(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, i + 2, seq!['/', '*']) && is_lit(s, j - 2, j, seq!['*', '/']) && i + 2 <= j - 2
        && opt(i + 2, j - 2, multi_line_comment_chars(s, i + 2, j - 2))
}

/// §12.5 `HashbangComment :: `#!` SingleLineCommentChars?`. The goal symbols
/// that have it apply it at index 0 only (see [`element_matches`]).
pub open spec fn hashbang_comment(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, i + 2, seq!['#', '!']) && j >= i + 2
        && opt(i + 2, j, single_line_comment_chars(s, i + 2, j))
}

// Annex B.1.1 HTML-like Comments (the grammar that extends §12.4).

/// Annex B.1.1 `SingleLineDelimitedCommentChars`.
pub open spec fn single_line_delimited_comment_chars(s: Src, i: int, j: int) -> bool
    decreases j - i, 0int,
{
    nonempty(s, i, j) && (
        // 1. SingleLineNotAsteriskChar SingleLineDelimitedCommentChars?
        //    with SingleLineNotAsteriskChar :: SourceCharacter but not one of
        //    `*` or LineTerminator
        (is_not_line_terminator(s[i]) && s[i] != '*' as u32
            && (j == i + 1 || single_line_delimited_comment_chars(s, i + 1, j)))
        // 2. `*` SingleLinePostAsteriskCommentChars?
        || (s[i] == '*' as u32
            && (j == i + 1 || single_line_post_asterisk_comment_chars(s, i + 1, j))))
}

/// Annex B.1.1 `SingleLinePostAsteriskCommentChars`.
pub open spec fn single_line_post_asterisk_comment_chars(s: Src, i: int, j: int) -> bool
    decreases j - i, 1int,
{
    nonempty(s, i, j) && (
        // 1. SingleLineNotForwardSlashOrAsteriskChar
        //    SingleLineDelimitedCommentChars?
        //    with SingleLineNotForwardSlashOrAsteriskChar :: SourceCharacter
        //    but not one of `/` or `*` or LineTerminator
        (is_not_line_terminator(s[i]) && s[i] != '/' as u32 && s[i] != '*' as u32
            && (j == i + 1 || single_line_delimited_comment_chars(s, i + 1, j)))
        // 2. `*` SingleLinePostAsteriskCommentChars?
        || (s[i] == '*' as u32
            && (j == i + 1 || single_line_post_asterisk_comment_chars(s, i + 1, j))))
}

/// Annex B.1.1 `SingleLineDelimitedComment :: `/*`
/// SingleLineDelimitedCommentChars? `*/``.
pub open spec fn single_line_delimited_comment(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, i + 2, seq!['/', '*']) && is_lit(s, j - 2, j, seq!['*', '/']) && i + 2 <= j - 2
        && opt(i + 2, j - 2, single_line_delimited_comment_chars(s, i + 2, j - 2))
}

/// Annex B.1.1 `WhiteSpaceSequence :: WhiteSpace WhiteSpaceSequence?`.
pub open spec fn white_space_sequence(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && white_space(s, i, i + 1)
        && (j == i + 1 || white_space_sequence(s, i + 1, j))
}

/// Annex B.1.1 `SingleLineDelimitedCommentSequence ::
/// SingleLineDelimitedComment WhiteSpaceSequence?
/// SingleLineDelimitedCommentSequence?`: a delimited comment on `[i, a)`,
/// optional white space on `[a, b)`, and the rest on `[b, j)` (optional).
pub open spec fn single_line_delimited_comment_sequence(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    nonempty(s, i, j)
        && exists|a: int, b: int| #![auto]
            i < a && a <= b && b <= j && single_line_delimited_comment(s, i, a)
                && opt(a, b, white_space_sequence(s, a, b))
                && opt(b, j, single_line_delimited_comment_sequence(s, b, j))
}

/// Annex B.1.1 `HTMLCloseComment :: WhiteSpaceSequence?
/// SingleLineDelimitedCommentSequence? `-->` SingleLineCommentChars?`.
pub open spec fn html_close_comment_split(s: Src, i: int, a: int, b: int, j: int) -> bool {
    i <= a && a <= b && b + 3 <= j && j <= s.len()
        && opt(i, a, white_space_sequence(s, i, a))
        && opt(a, b, single_line_delimited_comment_sequence(s, a, b))
        && is_lit(s, b, b + 3, seq!['-', '-', '>'])
        && opt(b + 3, j, single_line_comment_chars(s, b + 3, j))
}

/// Annex B.1.1 `HTMLCloseComment`.
pub open spec fn html_close_comment(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && exists|a: int, b: int| html_close_comment_split(s, i, a, b, j)
}

/// Annex B.1.1 `SingleLineHTMLOpenComment :: `<!--` SingleLineCommentChars?`.
pub open spec fn single_line_html_open_comment(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, i + 4, seq!['<', '!', '-', '-']) && j >= i + 4
        && opt(i + 4, j, single_line_comment_chars(s, i + 4, j))
}

/// Annex B.1.1 `SingleLineHTMLCloseComment :: LineTerminatorSequence
/// HTMLCloseComment`.
pub open spec fn single_line_html_close_comment(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j)
        && exists|a: int| i < a && a < j && line_terminator_sequence(s, i, a)
            && html_close_comment(s, a, j)
}

/// Annex B.1.1 `MultiLineComment :: `/*` FirstCommentLine? LineTerminator
/// MultiLineCommentChars? `*/` HTMLCloseComment?`, with `FirstCommentLine ::
/// SingleLineDelimitedCommentChars`.
pub open spec fn annex_b_multi_line_comment_split(
    s: Src,
    i: int,
    a: int,
    c: int,
    j: int,
) -> bool {
    // `/*`, then [i + 2, a) the optional FirstCommentLine, then the
    // LineTerminator at a, then [a + 1, c) the optional chars, then `*/`
    // at [c, c + 2), then the optional HTMLCloseComment on [c + 2, j).
    is_lit(s, i, i + 2, seq!['/', '*']) && i + 2 <= a && a < c && c + 2 <= j && j <= s.len()
        && opt(i + 2, a, single_line_delimited_comment_chars(s, i + 2, a))
        && line_terminator(s, a, a + 1)
        && opt(a + 1, c, multi_line_comment_chars(s, a + 1, c))
        && is_lit(s, c, c + 2, seq!['*', '/'])
        && opt(c + 2, j, html_close_comment(s, c + 2, j))
}

/// Annex B.1.1 `MultiLineComment`.
pub open spec fn annex_b_multi_line_comment(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && exists|a: int, c: int| annex_b_multi_line_comment_split(s, i, a, c, j)
}

/// §12.4 `Comment`; with `html`, Annex B.1.1's `Comment`, which has
/// `SingleLineHTMLOpenComment`, `SingleLineHTMLCloseComment` and
/// `SingleLineDelimitedComment` besides, and its own `MultiLineComment`.
pub open spec fn comment(s: Src, i: int, j: int, html: bool) -> bool {
    nonempty(s, i, j) && if html {
        // Annex B.1.1 Comment ::
        // 1. MultiLineComment
        annex_b_multi_line_comment(s, i, j)
        // 2. SingleLineComment
        || single_line_comment(s, i, j)
        // 3. SingleLineHTMLOpenComment
        || single_line_html_open_comment(s, i, j)
        // 4. SingleLineHTMLCloseComment
        || single_line_html_close_comment(s, i, j)
        // 5. SingleLineDelimitedComment
        || single_line_delimited_comment(s, i, j)
    } else {
        // §12.4 Comment ::
        // 1. MultiLineComment
        multi_line_comment(s, i, j)
        // 2. SingleLineComment
        || single_line_comment(s, i, j)
    }
}

/// §12.4: a comment that "contains a line terminator code point" is
/// "considered to be a LineTerminator for purposes of parsing by the
/// syntactic grammar"; so is a `SingleLineHTMLCloseComment` (Annex B.1.1),
/// which always begins with one. See the modelling choices.
pub open spec fn contains_line_terminator(s: Src, i: int, j: int) -> bool {
    exists|k: int| i <= k < j && is_line_terminator(#[trigger] s[k])
}

// ---------------------------------------------------------------------
// §12.9.3 numeric digits (needed by escapes and identifiers below).
// ---------------------------------------------------------------------

/// `DecimalDigit`, `OctalDigit`, `BinaryDigit` and `HexDigit` as a class of
/// one code point, by radix (10, 8, 2, 16).
pub open spec fn is_radix_digit(radix: int, c: u32) -> bool {
    if radix == 2 {
        c == '0' as u32 || c == '1' as u32
    } else if radix == 8 {
        '0' as u32 <= c <= '7' as u32
    } else if radix == 10 {
        '0' as u32 <= c <= '9' as u32
    } else {
        radix == 16 && (('0' as u32 <= c <= '9' as u32) || ('a' as u32 <= c <= 'f' as u32)
            || ('A' as u32 <= c <= 'F' as u32))
    }
}

/// §12.9.3 `DecimalDigit :: one of 0 1 2 3 4 5 6 7 8 9`.
pub open spec fn is_decimal_digit(c: u32) -> bool {
    is_radix_digit(10, c)
}

/// §12.9.3 `HexDigit`.
pub open spec fn is_hex_digit(c: u32) -> bool {
    is_radix_digit(16, c)
}

/// §12.9.3 `OctalDigit :: one of 0 1 2 3 4 5 6 7`.
pub open spec fn is_octal_digit(c: u32) -> bool {
    is_radix_digit(8, c)
}

/// §12.9.3 `NonZeroDigit :: one of 1 2 3 4 5 6 7 8 9`.
pub open spec fn is_non_zero_digit(c: u32) -> bool {
    is_decimal_digit(c) && c != '0' as u32
}

/// §12.9.3 `NonOctalDigit :: one of 8 9`.
pub open spec fn is_non_octal_digit(c: u32) -> bool {
    c == '8' as u32 || c == '9' as u32
}

/// The MV of a `HexDigit` (§12.9.3.2: 0 to 15; `a` and `A` are 10, and so on).
pub open spec fn hex_digit_value(c: u32) -> int {
    if '0' as u32 <= c <= '9' as u32 {
        c as int - '0' as int
    } else if 'a' as u32 <= c <= 'f' as u32 {
        c as int - 'a' as int + 10
    } else {
        c as int - 'A' as int + 10
    }
}

/// §12.9.3 `DecimalDigits[Sep]`, `BinaryDigits[Sep]`, `OctalDigits[Sep]` and
/// `HexDigits[Sep]`, by radix.
pub open spec fn digits(radix: int, sep: bool, s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. Digit
        (j == i + 1 && is_radix_digit(radix, s[i]))
        // 2. Digits[?Sep] Digit
        || (i + 1 < j && is_radix_digit(radix, s[j - 1]) && digits(radix, sep, s, i, j - 1))
        // 3. [+Sep] Digits[+Sep] NumericLiteralSeparator Digit
        || (sep && i + 2 < j && s[j - 2] == '_' as u32 && is_radix_digit(radix, s[j - 1])
            && digits(radix, true, s, i, j - 2)))
}

/// §12.9.3 `DecimalDigits[Sep]`.
pub open spec fn decimal_digits(sep: bool, s: Src, i: int, j: int) -> bool {
    digits(10, sep, s, i, j)
}

/// §12.9.3 `BinaryDigits[Sep]`.
pub open spec fn binary_digits(sep: bool, s: Src, i: int, j: int) -> bool {
    digits(2, sep, s, i, j)
}

/// §12.9.3 `OctalDigits[Sep]`.
pub open spec fn octal_digits(sep: bool, s: Src, i: int, j: int) -> bool {
    digits(8, sep, s, i, j)
}

/// §12.9.3 `HexDigits[Sep]`.
pub open spec fn hex_digits(sep: bool, s: Src, i: int, j: int) -> bool {
    digits(16, sep, s, i, j)
}

/// The MV of `HexDigits[~Sep]` (§12.9.3.2: "the MV of HexDigits × 16 plus the
/// MV of HexDigit").
pub open spec fn hex_digits_mv(s: Src, i: int, j: int) -> int
    decreases j - i,
{
    if i >= j {
        0
    } else {
        hex_digits_mv(s, i, j - 1) * 16 + hex_digit_value(s[j - 1])
    }
}

// ---------------------------------------------------------------------
// §12.9.4 String escapes (shared by identifiers, strings and templates).
// ---------------------------------------------------------------------

/// §12.9.4 `Hex4Digits :: HexDigit HexDigit HexDigit HexDigit`.
pub open spec fn hex4_digits(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && j == i + 4 && is_hex_digit(s[i]) && is_hex_digit(s[i + 1])
        && is_hex_digit(s[i + 2]) && is_hex_digit(s[i + 3])
}

/// §12.9.6 `CodePoint :: HexDigits[~Sep] [> but only if the MV of HexDigits
/// ≤ 0x10FFFF]`.
pub open spec fn code_point(s: Src, i: int, j: int) -> bool {
    hex_digits(false, s, i, j) && hex_digits_mv(s, i, j) <= 0x10FFFF
}

/// §12.9.6 `NotCodePoint :: HexDigits[~Sep] [> but only if the MV of
/// HexDigits > 0x10FFFF]`.
pub open spec fn not_code_point(s: Src, i: int, j: int) -> bool {
    hex_digits(false, s, i, j) && hex_digits_mv(s, i, j) > 0x10FFFF
}

/// §12.9.4 `UnicodeEscapeSequence :: `u` Hex4Digits | `u{` CodePoint `}``,
/// the range after the backslash.
pub open spec fn unicode_escape_sequence(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. `u` Hex4Digits
        (s[i] == 'u' as u32 && hex4_digits(s, i + 1, j))
        // 2. `u{` CodePoint `}`
        || (i + 3 < j && is_lit(s, i, i + 2, seq!['u', '{']) && s[j - 1] == '}' as u32
            && code_point(s, i + 2, j - 1)))
}

/// §12.7.1.3 IdentifierCodePoint of a `UnicodeEscapeSequence`: "the code
/// point whose numeric value is the MV of Hex4Digits" (or of CodePoint).
pub open spec fn unicode_escape_code_point(s: Src, i: int, j: int) -> int {
    if s[i + 1] == '{' as u32 {
        hex_digits_mv(s, i + 2, j - 1)
    } else {
        hex_digits_mv(s, i + 1, j)
    }
}

/// §12.9.4.2 SV of a `UnicodeEscapeSequence`.
pub open spec fn unicode_escape_sv(s: Src, i: int, j: int) -> Seq<u16> {
    if s[i + 1] == '{' as u32 {
        // The SV of `u{` CodePoint `}` is the result of performing
        // UTF16EncodeCodePoint on the MV of CodePoint.
        utf16_encode_code_point(hex_digits_mv(s, i + 2, j - 1))
    } else {
        // The SV of Hex4Digits is the String value consisting of the code
        // unit whose numeric value is the MV of Hex4Digits.
        seq![hex_digits_mv(s, i + 1, j) as u16]
    }
}

// ---------------------------------------------------------------------
// §12.7 Names and Keywords
// ---------------------------------------------------------------------

/// The ASCII letters, `AsciiLetter` (§12.7).
pub open spec fn is_ascii_letter(c: u32) -> bool {
    ('a' as u32 <= c <= 'z' as u32) || ('A' as u32 <= c <= 'Z' as u32)
}

/// The code points above U+007F with Unicode property "ID_Start" (§12.7
/// `UnicodeIDStart`). Uninterpreted: see the modelling choices.
pub uninterp spec fn unicode_id_start_non_ascii(c: u32) -> bool;

/// The code points above U+007F with Unicode property "ID_Continue" (§12.7
/// `UnicodeIDContinue`). Uninterpreted.
pub uninterp spec fn unicode_id_continue_non_ascii(c: u32) -> bool;

/// §12.7 `UnicodeIDStart :: any Unicode code point with the Unicode property
/// "ID_Start"`. In ASCII, the letters.
pub open spec fn unicode_id_start(c: u32) -> bool {
    if c < 0x80 {
        is_ascii_letter(c)
    } else {
        unicode_id_start_non_ascii(c)
    }
}

/// §12.7 `UnicodeIDContinue :: any Unicode code point with the Unicode
/// property "ID_Continue"`. In ASCII, the letters, digits and `_`.
pub open spec fn unicode_id_continue(c: u32) -> bool {
    if c < 0x80 {
        is_ascii_letter(c) || is_decimal_digit(c) || c == '_' as u32
    } else {
        unicode_id_continue_non_ascii(c)
    }
}

/// §12.7 `IdentifierStartChar :: UnicodeIDStart | `$` | `_``.
pub open spec fn is_identifier_start_char(c: u32) -> bool {
    unicode_id_start(c) || c == '$' as u32 || c == '_' as u32
}

/// §12.7 `IdentifierPartChar :: UnicodeIDContinue | `$``.
pub open spec fn is_identifier_part_char(c: u32) -> bool {
    unicode_id_continue(c) || c == '$' as u32
}

/// §12.7 `IdentifierStart :: IdentifierStartChar | `\` UnicodeEscapeSequence`.
pub open spec fn identifier_start(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. IdentifierStartChar
        (j == i + 1 && is_identifier_start_char(s[i]))
        // 2. `\` UnicodeEscapeSequence
        || (s[i] == '\\' as u32 && unicode_escape_sequence(s, i + 1, j)))
}

/// §12.7 `IdentifierPart :: IdentifierPartChar | `\` UnicodeEscapeSequence`.
pub open spec fn identifier_part(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. IdentifierPartChar
        (j == i + 1 && is_identifier_part_char(s[i]))
        // 2. `\` UnicodeEscapeSequence
        || (s[i] == '\\' as u32 && unicode_escape_sequence(s, i + 1, j)))
}

/// §12.7.1.3 IdentifierCodePoint of an `IdentifierStart` or `IdentifierPart`
/// (the two have the same two alternatives): "the code point matched by
/// IdentifierStartChar" (or IdentifierPartChar), or the code point of the
/// `UnicodeEscapeSequence`.
pub open spec fn identifier_code_point(s: Src, i: int, j: int) -> u32 {
    if s[i] == '\\' as u32 {
        unicode_escape_code_point(s, i + 1, j) as u32
    } else {
        s[i]
    }
}

/// §12.7 `IdentifierName`, with its IdentifierCodePoints `cps` (§12.7.1.2).
pub open spec fn identifier_name_cps(s: Src, i: int, j: int, cps: Seq<u32>) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. IdentifierName :: IdentifierStart
        //    IdentifierCodePoints, step 1: "Let cp be the IdentifierCodePoint
        //    of IdentifierStart." Step 2: "Return « cp »."
        (identifier_start(s, i, j) && cps =~= seq![identifier_code_point(s, i, j)])
        // 2. IdentifierName :: IdentifierName IdentifierPart
        //    IdentifierCodePoints, step 1: "Let cps be the IdentifierCodePoints
        //    of the derived IdentifierName." Step 2: "Let cp be the
        //    IdentifierCodePoint of IdentifierPart." Step 3: "Return the
        //    list-concatenation of cps and « cp »."
        || (cps.len() >= 2 && exists|k: int| #![auto] i < k < j && identifier_name_cps(s, i, k, cps.drop_last())
            && identifier_part(s, k, j) && cps.last() == identifier_code_point(s, k, j)))
}

/// §12.7 `IdentifierName`.
pub open spec fn identifier_name(s: Src, i: int, j: int) -> bool {
    exists|cps: Seq<u32>| identifier_name_cps(s, i, j, cps)
}

/// §12.7 `PrivateIdentifier :: `#` IdentifierName`.
pub open spec fn private_identifier(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && s[i] == '#' as u32 && identifier_name(s, i + 1, j)
}

/// §12.7.1.1 Static Semantics: Early Errors, for the code points `cps` of an
/// `IdentifierName`. The two rules say that the IdentifierCodePoint of an
/// escape must be matched by `IdentifierStartChar` (as the first code
/// point) or `IdentifierPartChar` (after it). A code point written without
/// an escape is derived through those very productions, so the rule holds
/// of it already; checking every code point is the same as checking the
/// escapes.
pub open spec fn identifier_early_errors_ok(cps: Seq<u32>) -> bool {
    cps.len() >= 1 && is_identifier_start_char(cps[0])
        && forall|k: int| 1 <= k < cps.len() ==> is_identifier_part_char(#[trigger] cps[k])
}

/// The `IdentifierName` over `s[i..j)` (starting at `i`) has no early
/// error (§12.7.1.1).
pub open spec fn identifier_name_valid(s: Src, i: int, j: int) -> bool {
    exists|cps: Seq<u32>| #![auto] identifier_name_cps(s, i, j, cps) && identifier_early_errors_ok(cps)
}

/// The `IdentifierName` over `s[i..j)` was written with at least one
/// `UnicodeEscapeSequence`. "A code point in a keyword cannot be expressed by
/// a `\` UnicodeEscapeSequence" (§12.7.2 note): an escaped name is never a
/// `ReservedWord`.
pub open spec fn identifier_has_escape(s: Src, i: int, j: int) -> bool {
    exists|k: int| i <= k < j && s[k] == '\\' as u32
}

/// The code points of an ASCII word, for comparing with an identifier.
pub open spec fn word(w: Seq<char>) -> Seq<u32> {
    w.map_values(|c: char| c as u32)
}

/// §12.7.2 `ReservedWord :: one of await break case catch class const
/// continue debugger default delete do else enum export extends false
/// finally for function if import in instanceof new null return super switch
/// this throw true try typeof var void while with yield`.
pub open spec fn reserved_words() -> Seq<Seq<char>> {
    seq![
        seq!['a', 'w', 'a', 'i', 't'],
        seq!['b', 'r', 'e', 'a', 'k'],
        seq!['c', 'a', 's', 'e'],
        seq!['c', 'a', 't', 'c', 'h'],
        seq!['c', 'l', 'a', 's', 's'],
        seq!['c', 'o', 'n', 's', 't'],
        seq!['c', 'o', 'n', 't', 'i', 'n', 'u', 'e'],
        seq!['d', 'e', 'b', 'u', 'g', 'g', 'e', 'r'],
        seq!['d', 'e', 'f', 'a', 'u', 'l', 't'],
        seq!['d', 'e', 'l', 'e', 't', 'e'],
        seq!['d', 'o'],
        seq!['e', 'l', 's', 'e'],
        seq!['e', 'n', 'u', 'm'],
        seq!['e', 'x', 'p', 'o', 'r', 't'],
        seq!['e', 'x', 't', 'e', 'n', 'd', 's'],
        seq!['f', 'a', 'l', 's', 'e'],
        seq!['f', 'i', 'n', 'a', 'l', 'l', 'y'],
        seq!['f', 'o', 'r'],
        seq!['f', 'u', 'n', 'c', 't', 'i', 'o', 'n'],
        seq!['i', 'f'],
        seq!['i', 'm', 'p', 'o', 'r', 't'],
        seq!['i', 'n'],
        seq!['i', 'n', 's', 't', 'a', 'n', 'c', 'e', 'o', 'f'],
        seq!['n', 'e', 'w'],
        seq!['n', 'u', 'l', 'l'],
        seq!['r', 'e', 't', 'u', 'r', 'n'],
        seq!['s', 'u', 'p', 'e', 'r'],
        seq!['s', 'w', 'i', 't', 'c', 'h'],
        seq!['t', 'h', 'i', 's'],
        seq!['t', 'h', 'r', 'o', 'w'],
        seq!['t', 'r', 'u', 'e'],
        seq!['t', 'r', 'y'],
        seq!['t', 'y', 'p', 'e', 'o', 'f'],
        seq!['v', 'a', 'r'],
        seq!['v', 'o', 'i', 'd'],
        seq!['w', 'h', 'i', 'l', 'e'],
        seq!['w', 'i', 't', 'h'],
        seq!['y', 'i', 'e', 'l', 'd'],
    ]
}

/// §12.7.2 the code points `cps` of an `IdentifierName`, written without
/// escapes (`escaped` is false), are a `ReservedWord`. A `ReservedWord`
/// matches literal source characters; whether it may be used as an
/// identifier depends on context (§12.7.2, §13.1.1), which is the parser's.
pub open spec fn is_reserved_word(cps: Seq<u32>, escaped: bool) -> bool {
    !escaped && exists|n: int| 0 <= n < reserved_words().len()
        && cps =~= word(#[trigger] reserved_words()[n])
}

// ---------------------------------------------------------------------
// §12.8 Punctuators
// ---------------------------------------------------------------------

/// §12.8 `OtherPunctuator :: one of ...`, the alternatives listed.
pub open spec fn other_punctuators() -> Seq<Seq<char>> {
    seq![
        seq!['{'], seq!['('], seq![')'], seq!['['], seq![']'],
        seq!['.'], seq!['.', '.', '.'], seq![';'], seq![','],
        seq!['<'], seq!['>'], seq!['<', '='], seq!['>', '='],
        seq!['=', '='], seq!['!', '='], seq!['=', '=', '='], seq!['!', '=', '='],
        seq!['+'], seq!['-'], seq!['*'], seq!['%'], seq!['*', '*'],
        seq!['+', '+'], seq!['-', '-'],
        seq!['<', '<'], seq!['>', '>'], seq!['>', '>', '>'],
        seq!['&'], seq!['|'], seq!['^'],
        seq!['!'], seq!['~'],
        seq!['&', '&'], seq!['|', '|'], seq!['?', '?'],
        seq!['?'], seq![':'],
        seq!['='], seq!['+', '='], seq!['-', '='], seq!['*', '='], seq!['%', '='],
        seq!['*', '*', '='], seq!['<', '<', '='], seq!['>', '>', '='],
        seq!['>', '>', '>', '='], seq!['&', '='], seq!['|', '='], seq!['^', '='],
        seq!['&', '&', '='], seq!['|', '|', '='], seq!['?', '?', '='],
        seq!['=', '>'],
    ]
}

/// §12.8 `OptionalChainingPunctuator :: `?.` [lookahead ∉ DecimalDigit]`.
pub open spec fn optional_chaining_punctuator(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, j, seq!['?', '.']) && 0 <= i
        && !(j < s.len() && is_decimal_digit(s[j]))
}

/// §12.8 `OtherPunctuator`.
pub open spec fn other_punctuator(s: Src, i: int, j: int) -> bool {
    exists|n: int| 0 <= n < other_punctuators().len()
        && is_lit(s, i, j, #[trigger] other_punctuators()[n])
}

/// §12.8 `Punctuator :: OptionalChainingPunctuator | OtherPunctuator`.
pub open spec fn punctuator(s: Src, i: int, j: int) -> bool {
    // 1. OptionalChainingPunctuator
    optional_chaining_punctuator(s, i, j)
    // 2. OtherPunctuator
    || other_punctuator(s, i, j)
}

/// §12.8 `DivPunctuator :: `/` | `/=``.
pub open spec fn div_punctuator(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, j, seq!['/']) || is_lit(s, i, j, seq!['/', '='])
}

/// §12.8 `RightBracePunctuator :: `}``.
pub open spec fn right_brace_punctuator(s: Src, i: int, j: int) -> bool {
    is_lit(s, i, j, seq!['}'])
}

// ---------------------------------------------------------------------
// §12.9.3 Numeric Literals
// ---------------------------------------------------------------------

/// §12.9.3 `NonOctalDecimalIntegerLiteral`, `LegacyOctalLikeDecimalIntegerLiteral`
/// and `LegacyOctalIntegerLiteral` are three left-recursive lists of digits
/// that start with `0` and an `OctalDigit` or `NonOctalDigit`.
///
/// `LegacyOctalLikeDecimalIntegerLiteral :: `0` OctalDigit |
/// LegacyOctalLikeDecimalIntegerLiteral OctalDigit`.
pub open spec fn legacy_octal_like_decimal_integer_literal(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. `0` OctalDigit
        (j == i + 2 && s[i] == '0' as u32 && is_octal_digit(s[i + 1]))
        // 2. LegacyOctalLikeDecimalIntegerLiteral OctalDigit
        || (i + 2 < j && is_octal_digit(s[j - 1])
            && legacy_octal_like_decimal_integer_literal(s, i, j - 1)))
}

/// §12.9.3 `NonOctalDecimalIntegerLiteral`.
pub open spec fn non_octal_decimal_integer_literal(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. `0` NonOctalDigit
        (j == i + 2 && s[i] == '0' as u32 && is_non_octal_digit(s[i + 1]))
        // 2. LegacyOctalLikeDecimalIntegerLiteral NonOctalDigit
        || (i + 2 < j && is_non_octal_digit(s[j - 1])
            && legacy_octal_like_decimal_integer_literal(s, i, j - 1))
        // 3. NonOctalDecimalIntegerLiteral DecimalDigit
        || (i + 2 < j && is_decimal_digit(s[j - 1])
            && non_octal_decimal_integer_literal(s, i, j - 1)))
}

/// §12.9.3 `LegacyOctalIntegerLiteral :: `0` OctalDigit |
/// LegacyOctalIntegerLiteral OctalDigit`.
pub open spec fn legacy_octal_integer_literal(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. `0` OctalDigit
        (j == i + 2 && s[i] == '0' as u32 && is_octal_digit(s[i + 1]))
        // 2. LegacyOctalIntegerLiteral OctalDigit
        || (i + 2 < j && is_octal_digit(s[j - 1]) && legacy_octal_integer_literal(s, i, j - 1)))
}

/// §12.9.3 `DecimalIntegerLiteral`.
pub open spec fn decimal_integer_literal(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. `0`
        (j == i + 1 && s[i] == '0' as u32)
        // 2. NonZeroDigit
        || (j == i + 1 && is_non_zero_digit(s[i]))
        // 3. NonZeroDigit NumericLiteralSeparator? DecimalDigits[+Sep]
        || (i + 1 < j && is_non_zero_digit(s[i])
            && (decimal_digits(true, s, i + 1, j)
                || (s[i + 1] == '_' as u32 && decimal_digits(true, s, i + 2, j))))
        // 4. NonOctalDecimalIntegerLiteral
        || non_octal_decimal_integer_literal(s, i, j))
}

/// §12.9.3 `SignedInteger[Sep]`.
pub open spec fn signed_integer(sep: bool, s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. DecimalDigits[?Sep]
        decimal_digits(sep, s, i, j)
        // 2. `+` DecimalDigits[?Sep]
        || (s[i] == '+' as u32 && decimal_digits(sep, s, i + 1, j))
        // 3. `-` DecimalDigits[?Sep]
        || (s[i] == '-' as u32 && decimal_digits(sep, s, i + 1, j)))
}

/// §12.9.3 `ExponentPart[Sep] :: ExponentIndicator SignedInteger[?Sep]`,
/// with `ExponentIndicator :: one of e E`.
pub open spec fn exponent_part(sep: bool, s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (s[i] == 'e' as u32 || s[i] == 'E' as u32)
        && signed_integer(sep, s, i + 1, j)
}

/// `DecimalLiteral :: DecimalIntegerLiteral `.` DecimalDigits[+Sep]?
/// ExponentPart[+Sep]?`: the integer on `[i, a)`, `.` at `a`, the digits on
/// `[a + 1, b)` and the exponent on `[b, j)`.
pub open spec fn decimal_literal_1(s: Src, i: int, a: int, b: int, j: int) -> bool {
    i < a && a < b && b <= j && j <= s.len() && decimal_integer_literal(s, i, a)
        && s[a] == '.' as u32 && opt(a + 1, b, decimal_digits(true, s, a + 1, b))
        && opt(b, j, exponent_part(true, s, b, j))
}

/// §12.9.3 `DecimalLiteral`.
pub open spec fn decimal_literal(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. DecimalIntegerLiteral `.` DecimalDigits[+Sep]? ExponentPart[+Sep]?
        (exists|a: int, b: int| decimal_literal_1(s, i, a, b, j))
        // 2. `.` DecimalDigits[+Sep] ExponentPart[+Sep]?
        || (s[i] == '.' as u32
            && exists|b: int| #![auto] i + 1 < b && b <= j && decimal_digits(true, s, i + 1, b)
                && opt(b, j, exponent_part(true, s, b, j)))
        // 3. DecimalIntegerLiteral ExponentPart[+Sep]?
        || exists|a: int| #![auto] i < a && a <= j && decimal_integer_literal(s, i, a)
            && opt(a, j, exponent_part(true, s, a, j)))
}

/// §12.9.3 `DecimalBigIntegerLiteral`.
pub open spec fn decimal_big_integer_literal(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && i + 1 < j && s[j - 1] == 'n' as u32 && (
        // 1. `0` BigIntLiteralSuffix
        (j == i + 2 && s[i] == '0' as u32)
        // 2. NonZeroDigit DecimalDigits[+Sep]? BigIntLiteralSuffix
        || (is_non_zero_digit(s[i]) && opt(i + 1, j - 1, decimal_digits(true, s, i + 1, j - 1)))
        // 3. NonZeroDigit NumericLiteralSeparator DecimalDigits[+Sep]
        //    BigIntLiteralSuffix
        || (is_non_zero_digit(s[i]) && i + 2 < j - 1 && s[i + 1] == '_' as u32
            && decimal_digits(true, s, i + 2, j - 1)))
}

/// §12.9.3 `BinaryIntegerLiteral[Sep]`, `OctalIntegerLiteral[Sep]` and
/// `HexIntegerLiteral[Sep]` (`0b` `0B`, `0o` `0O`, `0x` `0X` and digits), as
/// `NonDecimalIntegerLiteral[Sep]`.
pub open spec fn non_decimal_integer_literal(sep: bool, s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && i + 2 < j && s[i] == '0' as u32 && (
        // BinaryIntegerLiteral
        ((s[i + 1] == 'b' as u32 || s[i + 1] == 'B' as u32) && binary_digits(sep, s, i + 2, j))
        // OctalIntegerLiteral
        || ((s[i + 1] == 'o' as u32 || s[i + 1] == 'O' as u32) && octal_digits(sep, s, i + 2, j))
        // HexIntegerLiteral
        || ((s[i + 1] == 'x' as u32 || s[i + 1] == 'X' as u32) && hex_digits(sep, s, i + 2, j)))
}

/// §12.9.3 `NumericLiteral`.
pub open spec fn numeric_literal(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. DecimalLiteral
        decimal_literal(s, i, j)
        // 2. DecimalBigIntegerLiteral
        || decimal_big_integer_literal(s, i, j)
        // 3. NonDecimalIntegerLiteral[+Sep]
        || non_decimal_integer_literal(true, s, i, j)
        // 4. NonDecimalIntegerLiteral[+Sep] BigIntLiteralSuffix
        || (i + 1 < j && s[j - 1] == 'n' as u32 && non_decimal_integer_literal(true, s, i, j - 1))
        // 5. LegacyOctalIntegerLiteral
        || legacy_octal_integer_literal(s, i, j))
}

/// The `NumericLiteral` over `s[i..j)` is a BigInt literal (alternatives 2
/// and 4, which end in `BigIntLiteralSuffix`).
pub open spec fn numeric_literal_is_bigint(s: Src, i: int, j: int) -> bool {
    decimal_big_integer_literal(s, i, j)
        || (i + 1 < j && s[j - 1] == 'n' as u32 && non_decimal_integer_literal(true, s, i, j - 1))
}

/// §12.9.3.1: "NumericLiteral :: LegacyOctalIntegerLiteral" and
/// "DecimalIntegerLiteral :: NonOctalDecimalIntegerLiteral" are Syntax Errors
/// if IsStrict, and Legacy otherwise. The literal over `s[i..j)` uses one of
/// them. The parser applies the rule: it knows whether the code is strict.
pub open spec fn numeric_literal_is_legacy(s: Src, i: int, j: int) -> bool {
    legacy_octal_integer_literal(s, i, j)
        || (decimal_literal(s, i, j)
            && exists|k: int| i < k <= j && non_octal_decimal_integer_literal(s, i, k))
}

/// §12.9.3: "The SourceCharacter immediately following a NumericLiteral must
/// not be an IdentifierStart or DecimalDigit." A `NumericLiteral` ending at
/// `j` violates it. See the modelling choices for the reading of
/// IdentifierStart.
pub open spec fn numeric_literal_follow_error(s: Src, j: int) -> bool {
    (0 <= j < s.len() && is_decimal_digit(s[j]))
        || exists|k: int| j < k <= s.len() && identifier_start(s, j, k)
}

// ---------------------------------------------------------------------
// §12.9.4 String Literals
// ---------------------------------------------------------------------

/// §12.9.4 `LineContinuation :: `\` LineTerminatorSequence`.
pub open spec fn line_continuation(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && s[i] == '\\' as u32 && line_terminator_sequence(s, i + 1, j)
}

/// §12.9.4 `SingleEscapeCharacter :: one of ' " \ b f n r t v`.
pub open spec fn is_single_escape_character(c: u32) -> bool {
    c == '\'' as u32 || c == '"' as u32 || c == '\\' as u32 || c == 'b' as u32
        || c == 'f' as u32 || c == 'n' as u32 || c == 'r' as u32 || c == 't' as u32
        || c == 'v' as u32
}

/// §12.9.4.2 Table "String Single Character Escape Sequences": the code unit
/// of a `SingleEscapeCharacter`.
pub open spec fn single_escape_code_unit(c: u32) -> u16 {
    if c == 'b' as u32 {
        0x0008
    } else if c == 't' as u32 {
        0x0009
    } else if c == 'n' as u32 {
        0x000A
    } else if c == 'v' as u32 {
        0x000B
    } else if c == 'f' as u32 {
        0x000C
    } else if c == 'r' as u32 {
        0x000D
    } else {
        // `"`, `'`, `\`: the code unit of the character itself.
        c as u16
    }
}

/// §12.9.4 `EscapeCharacter :: SingleEscapeCharacter | DecimalDigit | `x` |
/// `u``.
pub open spec fn is_escape_character(c: u32) -> bool {
    is_single_escape_character(c) || is_decimal_digit(c) || c == 'x' as u32 || c == 'u' as u32
}

/// §12.9.4 `NonEscapeCharacter :: SourceCharacter but not one of
/// EscapeCharacter or LineTerminator`.
pub open spec fn is_non_escape_character(c: u32) -> bool {
    is_source_character(c) && !is_escape_character(c) && !is_line_terminator(c)
}

/// §12.9.4 `CharacterEscapeSequence`, and its SV (§12.9.4.2).
pub open spec fn character_escape_sequence_sv(s: Src, i: int, j: int, v: Seq<u16>) -> bool {
    nonempty(s, i, j) && j == i + 1 && (
        // 1. SingleEscapeCharacter: the code unit in the table.
        (is_single_escape_character(s[i]) && v =~= seq![single_escape_code_unit(s[i])])
        // 2. NonEscapeCharacter: UTF16EncodeCodePoint of the code point.
        || (is_non_escape_character(s[i]) && v =~= utf16_encode_code_point(s[i] as int)))
}

/// §12.9.4 `HexEscapeSequence :: `x` HexDigit HexDigit`.
pub open spec fn hex_escape_sequence(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && j == i + 3 && s[i] == 'x' as u32 && is_hex_digit(s[i + 1])
        && is_hex_digit(s[i + 2])
}

/// §12.9.4 `LegacyOctalEscapeSequence`.
pub open spec fn legacy_octal_escape_sequence(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. `0` [lookahead ∈ { `8`, `9` }]
        (j == i + 1 && s[i] == '0' as u32 && at_non_octal_digit(s, j))
        // 2. NonZeroOctalDigit [lookahead ∉ OctalDigit]
        || (j == i + 1 && is_octal_digit(s[i]) && s[i] != '0' as u32 && !at_octal_digit(s, j))
        // 3. ZeroToThree OctalDigit [lookahead ∉ OctalDigit]
        || (j == i + 2 && '0' as u32 <= s[i] <= '3' as u32 && is_octal_digit(s[i + 1])
            && !at_octal_digit(s, j))
        // 4. FourToSeven OctalDigit
        || (j == i + 2 && '4' as u32 <= s[i] <= '7' as u32 && is_octal_digit(s[i + 1]))
        // 5. ZeroToThree OctalDigit OctalDigit
        || (j == i + 3 && '0' as u32 <= s[i] <= '3' as u32 && is_octal_digit(s[i + 1])
            && is_octal_digit(s[i + 2])))
}

/// `[lookahead ∈ { `8`, `9` }]` at `j`.
pub open spec fn at_non_octal_digit(s: Src, j: int) -> bool {
    0 <= j < s.len() && is_non_octal_digit(s[j])
}

/// `[lookahead ∈ OctalDigit]` at `j`.
pub open spec fn at_octal_digit(s: Src, j: int) -> bool {
    0 <= j < s.len() && is_octal_digit(s[j])
}

/// `[lookahead ∈ DecimalDigit]` at `j`.
pub open spec fn at_decimal_digit(s: Src, j: int) -> bool {
    0 <= j < s.len() && is_decimal_digit(s[j])
}

/// `[lookahead ∈ HexDigit]` at `j`.
pub open spec fn at_hex_digit(s: Src, j: int) -> bool {
    0 <= j < s.len() && is_hex_digit(s[j])
}

/// §12.9.4.3 the MV of a `LegacyOctalEscapeSequence`. The standard states it
/// for alternatives 3, 4 and 5 only ("ZeroToThree OctalDigit", "FourToSeven
/// OctalDigit", "ZeroToThree OctalDigit OctalDigit"). Alternative 2 is a
/// chain production, so it has its `NonZeroOctalDigit`'s MV (the digit).
/// Alternative 1 has no nonterminal, so the standard does not give it an
/// MV; its evident intent is 0 (docs/ERRATA.md).
pub open spec fn legacy_octal_escape_sequence_mv(s: Src, i: int, j: int) -> int {
    if j == i + 1 {
        // 1. `0`: 0 (ERRATA.md). 2. NonZeroOctalDigit: the MV of the digit.
        s[i] as int - '0' as int
    } else if j == i + 2 {
        // 3, 4. (8 times the MV of ZeroToThree/FourToSeven) plus the MV of
        // OctalDigit.
        8 * (s[i] as int - '0' as int) + (s[i + 1] as int - '0' as int)
    } else {
        // 5. (64 times the MV of ZeroToThree) plus (8 times the MV of the
        // first OctalDigit) plus the MV of the second OctalDigit.
        64 * (s[i] as int - '0' as int) + 8 * (s[i + 1] as int - '0' as int)
            + (s[i + 2] as int - '0' as int)
    }
}

/// §12.9.4 `EscapeSequence` as a string literal uses it, with its SV
/// (§12.9.4.2). The range is after the backslash. Its first, second, fifth
/// and sixth alternatives are `TemplateEscapeSequence`'s four, which have the
/// same SV: [`template_escape_sequence_sv`].
pub open spec fn escape_sequence_sv(s: Src, i: int, j: int, v: Seq<u16>) -> bool {
    nonempty(s, i, j) && (
        // 1, 2, 5, 6. CharacterEscapeSequence; `0` [lookahead ∉ DecimalDigit];
        //             HexEscapeSequence; UnicodeEscapeSequence
        template_escape_sequence_sv(s, i, j, v)
        // 3. LegacyOctalEscapeSequence: "the String value consisting of the
        //    code unit whose numeric value is the MV of
        //    LegacyOctalEscapeSequence"
        || (legacy_octal_escape_sequence(s, i, j)
            && v =~= seq![legacy_octal_escape_sequence_mv(s, i, j) as u16])
        // 4. NonOctalDecimalEscapeSequence :: one of `8` `9`: "the String
        //    value consisting of the code unit 0x0038" (or 0x0039).
        || (j == i + 1 && is_non_octal_digit(s[i]) && v =~= seq![s[i] as u16]))
}

/// §12.9.6 `TemplateEscapeSequence`, with its SV (§12.9.4.2, which gives the
/// SV of `0`, `CharacterEscapeSequence`, `HexEscapeSequence` and
/// `UnicodeEscapeSequence`). The range is after the backslash.
pub open spec fn template_escape_sequence_sv(s: Src, i: int, j: int, v: Seq<u16>) -> bool {
    nonempty(s, i, j) && (
        // 1. CharacterEscapeSequence
        character_escape_sequence_sv(s, i, j, v)
        // 2. `0` [lookahead ∉ DecimalDigit]: "the String value consisting of
        //    the code unit 0x0000 (NULL)"
        || (j == i + 1 && s[i] == '0' as u32 && !at_decimal_digit(s, j) && v =~= seq![0u16])
        // 3. HexEscapeSequence: "the code unit whose numeric value is the MV
        //    of HexEscapeSequence", (16 times the MV of the first HexDigit)
        //    plus the MV of the second HexDigit
        || (hex_escape_sequence(s, i, j) && v =~= seq![hex_digits_mv(s, i + 1, j) as u16])
        // 4. UnicodeEscapeSequence
        || (unicode_escape_sequence(s, i, j) && v =~= unicode_escape_sv(s, i, j)))
}

/// §12.9.4 `DoubleStringCharacter` and `SingleStringCharacter` (the same
/// four alternatives, with `quote` the excluded quote), with the SV `v`
/// (§12.9.4.2).
pub open spec fn string_character_sv(s: Src, i: int, j: int, quote: u32, v: Seq<u16>) -> bool {
    nonempty(s, i, j) && (
        // 1. SourceCharacter but not one of `"` (or `'`) or `\` or
        //    LineTerminator: UTF16EncodeCodePoint of the code point.
        (j == i + 1 && is_not_line_terminator(s[i]) && s[i] != quote && s[i] != '\\' as u32
            && v =~= utf16_encode_code_point(s[i] as int))
        // 2. <LS>: "the String value consisting of the code unit 0x2028".
        || (j == i + 1 && s[i] == 0x2028 && v =~= seq![0x2028u16])
        // 3. <PS>: "the String value consisting of the code unit 0x2029".
        || (j == i + 1 && s[i] == 0x2029 && v =~= seq![0x2029u16])
        // 4. `\` EscapeSequence
        || (s[i] == '\\' as u32 && escape_sequence_sv(s, i + 1, j, v))
        // 5. LineContinuation: "the empty String".
        || (line_continuation(s, i, j) && v.len() == 0))
}

/// §12.9.4 `DoubleStringCharacters` and `SingleStringCharacters`, with SV
/// `v` (§12.9.4.2): the SV of `DoubleStringCharacter DoubleStringCharacters`
/// is "the string-concatenation of the SV of DoubleStringCharacter and the SV
/// of DoubleStringCharacters".
pub open spec fn string_characters_sv(s: Src, i: int, j: int, quote: u32, v: Seq<u16>) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. DoubleStringCharacter (`DoubleStringCharacters?` is empty): the
        //    SV of the character.
        string_character_sv(s, i, j, quote, v)
        // 2. DoubleStringCharacter DoubleStringCharacters
        || exists|k: int, v1: Seq<u16>, v2: Seq<u16>| #![auto]
            i < k < j && string_character_sv(s, i, k, quote, v1)
                && string_characters_sv(s, k, j, quote, v2) && v =~= v1 + v2)
}

/// §12.9.4 `StringLiteral`, with its SV `v`.
pub open spec fn string_literal_sv(s: Src, i: int, j: int, v: Seq<u16>) -> bool {
    nonempty(s, i, j) && i + 1 < j && (
        // 1. `"` DoubleStringCharacters? `"`: "the SV of StringLiteral :: `"`
        //    `"` is the empty String" and otherwise the SV of the characters
        ((s[i] == '"' as u32 && s[j - 1] == '"' as u32)
            && (if j == i + 2 {
                v.len() == 0
            } else {
                string_characters_sv(s, i + 1, j - 1, '"' as u32, v)
            }))
        // 2. `'` SingleStringCharacters? `'`
        || ((s[i] == '\'' as u32 && s[j - 1] == '\'' as u32)
            && (if j == i + 2 {
                v.len() == 0
            } else {
                string_characters_sv(s, i + 1, j - 1, '\'' as u32, v)
            })))
}

/// §12.9.4 `StringLiteral`.
pub open spec fn string_literal(s: Src, i: int, j: int) -> bool {
    exists|v: Seq<u16>| string_literal_sv(s, i, j, v)
}

// ---------------------------------------------------------------------
// §12.9.5 Regular Expression Literals (lexical part)
// ---------------------------------------------------------------------

/// §12.9.5 `RegularExpressionNonTerminator :: SourceCharacter but not
/// LineTerminator`.
pub open spec fn is_regexp_non_terminator(c: u32) -> bool {
    is_not_line_terminator(c)
}

/// §12.9.5 `RegularExpressionBackslashSequence :: `\`
/// RegularExpressionNonTerminator`.
pub open spec fn regexp_backslash_sequence(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && j == i + 2 && s[i] == '\\' as u32 && is_regexp_non_terminator(s[i + 1])
}

/// §12.9.5 `RegularExpressionClassChar`.
pub open spec fn regexp_class_char(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. RegularExpressionNonTerminator but not one of `]` or `\`
        (j == i + 1 && is_regexp_non_terminator(s[i]) && s[i] != ']' as u32
            && s[i] != '\\' as u32)
        // 2. RegularExpressionBackslashSequence
        || regexp_backslash_sequence(s, i, j))
}

/// §12.9.5 `RegularExpressionClassChars :: [empty] |
/// RegularExpressionClassChars RegularExpressionClassChar`.
pub open spec fn regexp_class_chars(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    // 1. [empty]
    i == j
    // 2. RegularExpressionClassChars RegularExpressionClassChar
    || (0 <= i && i < j && j <= s.len()
        && exists|k: int| i <= k < j && regexp_class_chars(s, i, k) && regexp_class_char(s, k, j))
}

/// §12.9.5 `RegularExpressionClass :: `[` RegularExpressionClassChars `]``.
pub open spec fn regexp_class(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && i + 1 < j && s[i] == '[' as u32 && s[j - 1] == ']' as u32
        && regexp_class_chars(s, i + 1, j - 1)
}

/// §12.9.5 `RegularExpressionFirstChar`.
pub open spec fn regexp_first_char(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. RegularExpressionNonTerminator but not one of `*` or `\` or `/`
        //    or `[`
        (j == i + 1 && is_regexp_non_terminator(s[i]) && s[i] != '*' as u32
            && s[i] != '\\' as u32 && s[i] != '/' as u32 && s[i] != '[' as u32)
        // 2. RegularExpressionBackslashSequence
        || regexp_backslash_sequence(s, i, j)
        // 3. RegularExpressionClass
        || regexp_class(s, i, j))
}

/// §12.9.5 `RegularExpressionChar`.
pub open spec fn regexp_char(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. RegularExpressionNonTerminator but not one of `\` or `/` or `[`
        (j == i + 1 && is_regexp_non_terminator(s[i]) && s[i] != '\\' as u32
            && s[i] != '/' as u32 && s[i] != '[' as u32)
        // 2. RegularExpressionBackslashSequence
        || regexp_backslash_sequence(s, i, j)
        // 3. RegularExpressionClass
        || regexp_class(s, i, j))
}

/// §12.9.5 `RegularExpressionChars :: [empty] | RegularExpressionChars
/// RegularExpressionChar`.
pub open spec fn regexp_chars(s: Src, i: int, j: int) -> bool
    decreases j - i,
{
    // 1. [empty]
    i == j
    // 2. RegularExpressionChars RegularExpressionChar
    || (0 <= i && i < j && j <= s.len()
        && exists|k: int| i <= k < j && regexp_chars(s, i, k) && regexp_char(s, k, j))
}

/// §12.9.5 `RegularExpressionBody :: RegularExpressionFirstChar
/// RegularExpressionChars`.
pub open spec fn regexp_body(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j)
        && exists|k: int| i < k <= j && regexp_first_char(s, i, k) && regexp_chars(s, k, j)
}

/// §12.9.5 `RegularExpressionFlags :: [empty] | RegularExpressionFlags
/// IdentifierPartChar`.
pub open spec fn regexp_flags(s: Src, i: int, j: int) -> bool {
    0 <= i && i <= j && j <= s.len() && all_of(s, i, j, |c: u32| is_identifier_part_char(c))
}

/// §12.9.5 `RegularExpressionLiteral :: `/` RegularExpressionBody `/`
/// RegularExpressionFlags`, where `b` is the index of the closing `/`.
/// BodyText is `s[i + 1..b)` (§12.9.5.1) and FlagText is `s[b + 1..j)`
/// (§12.9.5.2).
pub open spec fn regexp_literal(s: Src, i: int, j: int, b: int) -> bool {
    nonempty(s, i, j) && s[i] == '/' as u32 && i + 1 < b && b < j && s[b] == '/' as u32
        && regexp_body(s, i + 1, b) && regexp_flags(s, b + 1, j)
}

// ---------------------------------------------------------------------
// §12.9.6 Template Literal Lexical Components
// ---------------------------------------------------------------------

/// "TV: a String or undefined": `Some` is a String, `None` is *undefined*.
pub type Tv = Option<Seq<u16>>;

/// §12.9.6.1 the TV of `TemplateCharacters :: TemplateCharacter
/// TemplateCharacters`: "undefined if the TV of TemplateCharacter is
/// undefined or the TV of TemplateCharacters is undefined. Otherwise, it is
/// the string-concatenation of the TV of TemplateCharacter and the TV of
/// TemplateCharacters."
pub open spec fn tv_concat(a: Tv, b: Tv) -> Tv {
    match (a, b) {
        (Some(x), Some(y)) => Some(x + y),
        _ => None,
    }
}

/// §12.9.6.2 TRV of a `LineTerminatorSequence`: `<LF>`, `<CR>` and
/// `<CR><LF>` are all `<LF>`; `<LS>` and `<PS>` are themselves.
pub open spec fn line_terminator_sequence_trv(s: Src, i: int, j: int) -> Seq<u16> {
    if j == i + 2 {
        // <CR> <LF>: "the code unit 0x000A (LINE FEED)"
        seq![0x000Au16]
    } else if s[i] == 0x2028 {
        // <LS>: 0x2028
        seq![0x2028u16]
    } else if s[i] == 0x2029 {
        // <PS>: 0x2029
        seq![0x2029u16]
    } else {
        // <LF>, <CR>: 0x000A
        seq![0x000Au16]
    }
}

/// §12.9.6 `NotEscapeSequence`, the range after the backslash.
pub open spec fn not_escape_sequence(s: Src, i: int, j: int) -> bool {
    nonempty(s, i, j) && (
        // 1. `0` DecimalDigit
        (j == i + 2 && s[i] == '0' as u32 && is_decimal_digit(s[i + 1]))
        // 2. DecimalDigit but not `0`
        || (j == i + 1 && is_non_zero_digit(s[i]))
        // 3. `x` [lookahead ∉ HexDigit]
        || (j == i + 1 && s[i] == 'x' as u32 && !at_hex_digit(s, j))
        // 4. `x` HexDigit [lookahead ∉ HexDigit]
        || (j == i + 2 && s[i] == 'x' as u32 && is_hex_digit(s[i + 1]) && !at_hex_digit(s, j))
        // 5. `u` [lookahead ∉ HexDigit] [lookahead != `{`]
        || (j == i + 1 && s[i] == 'u' as u32 && !at_hex_digit(s, j) && !at(s, j, '{'))
        // 6. `u` HexDigit [lookahead ∉ HexDigit]
        || (j == i + 2 && s[i] == 'u' as u32 && is_hex_digit(s[i + 1]) && !at_hex_digit(s, j))
        // 7. `u` HexDigit HexDigit [lookahead ∉ HexDigit]
        || (j == i + 3 && s[i] == 'u' as u32 && is_hex_digit(s[i + 1]) && is_hex_digit(s[i + 2])
            && !at_hex_digit(s, j))
        // 8. `u` HexDigit HexDigit HexDigit [lookahead ∉ HexDigit]
        || (j == i + 4 && s[i] == 'u' as u32 && is_hex_digit(s[i + 1]) && is_hex_digit(s[i + 2])
            && is_hex_digit(s[i + 3]) && !at_hex_digit(s, j))
        // 9. `u` `{` [lookahead ∉ HexDigit]
        || (j == i + 2 && s[i] == 'u' as u32 && s[i + 1] == '{' as u32 && !at_hex_digit(s, j))
        // 10. `u` `{` NotCodePoint [lookahead ∉ HexDigit]
        || (i + 2 < j && s[i] == 'u' as u32 && s[i + 1] == '{' as u32
            && not_code_point(s, i + 2, j) && !at_hex_digit(s, j))
        // 11. `u` `{` CodePoint [lookahead ∉ HexDigit] [lookahead != `}`]
        || (i + 2 < j && s[i] == 'u' as u32 && s[i + 1] == '{' as u32
            && code_point(s, i + 2, j) && !at_hex_digit(s, j) && !at(s, j, '}')))
}

/// §12.9.6 `TemplateCharacter`, with its TV (§12.9.6.1) and TRV (§12.9.6.2).
pub open spec fn template_character(s: Src, i: int, j: int, tv: Tv, trv: Seq<u16>) -> bool {
    nonempty(s, i, j) && (
        // 1. `$` [lookahead != `{`]: both are "the code unit 0x0024".
        (j == i + 1 && s[i] == '$' as u32 && !at(s, j, '{')
            && tv == Some(seq![0x0024u16]) && trv =~= seq![0x0024u16])
        // 2. `\` TemplateEscapeSequence: TV is the SV of it; TRV is `\`
        //    followed by the TRV of the escape sequence, which (see the
        //    modelling choices) is the UTF-16 of the matched code points.
        || (s[i] == '\\' as u32
            && exists|v: Seq<u16>| template_escape_sequence_sv(s, i + 1, j, v)
                && tv == Some(v) && trv =~= utf16_of(s, i, j))
        // 3. `\` NotEscapeSequence: TV is *undefined*; TRV is `\` followed
        //    by the TRV of it (the same UTF-16).
        || (s[i] == '\\' as u32 && not_escape_sequence(s, i + 1, j)
            && tv == None::<Seq<u16>> && trv =~= utf16_of(s, i, j))
        // 4. LineContinuation: TV is "the empty String"; TRV is `\`
        //    followed by the TRV of the LineTerminatorSequence.
        || (line_continuation(s, i, j) && tv == Some(Seq::<u16>::empty())
            && trv =~= seq![0x005Cu16] + line_terminator_sequence_trv(s, i + 1, j))
        // 5. LineTerminatorSequence: TV is its TRV.
        || (line_terminator_sequence(s, i, j) && tv == Some(line_terminator_sequence_trv(s, i, j))
            && trv =~= line_terminator_sequence_trv(s, i, j))
        // 6. SourceCharacter but not one of ` or \ or $ or LineTerminator:
        //    UTF16EncodeCodePoint of the code point.
        || (j == i + 1 && is_not_line_terminator(s[i]) && s[i] != '`' as u32
            && s[i] != '\\' as u32 && s[i] != '$' as u32
            && tv == Some(utf16_encode_code_point(s[i] as int))
            && trv =~= utf16_encode_code_point(s[i] as int)))
}

/// §12.9.6 `TemplateCharacters :: TemplateCharacter TemplateCharacters?`,
/// with its TV and TRV (§12.9.6.1, §12.9.6.2: the TRV is "the
/// string-concatenation of the TRV of TemplateCharacter and the TRV of
/// TemplateCharacters").
pub open spec fn template_characters(s: Src, i: int, j: int, tv: Tv, trv: Seq<u16>) -> bool
    decreases j - i,
{
    nonempty(s, i, j) && (
        // 1. TemplateCharacter (`TemplateCharacters?` is empty)
        template_character(s, i, j, tv, trv)
        // 2. TemplateCharacter TemplateCharacters
        || exists|k: int, tv1: Option<Seq<u16>>, trv1: Seq<u16>, tv2: Option<Seq<u16>>, trv2: Seq<u16>|
            i < k < j && template_character(s, i, k, tv1, trv1)
                && template_characters(s, k, j, tv2, trv2) && tv =~= tv_concat(tv1, tv2)
                && trv =~= trv1 + trv2)
}

/// §12.9.6 the four template components, with TV and TRV: `NoSubstitutionTemplate`,
/// `TemplateHead`, `TemplateMiddle` and `TemplateTail` (§12.9.6.1: "The TV
/// of NoSubstitutionTemplate :: `` is the empty String", and likewise for
/// the other three; with characters, the TV of the characters).
pub open spec fn template_part(
    s: Src,
    i: int,
    j: int,
    kind: TemplateKind,
    tv: Tv,
    trv: Seq<u16>,
) -> bool {
    let close_len: int = match kind {
        TemplateKind::NoSubstitution | TemplateKind::Tail => 1,
        TemplateKind::Head | TemplateKind::Middle => 2,
    };
    nonempty(s, i, j) && i + 1 + close_len <= j
        // The opening: ` for NoSubstitutionTemplate and TemplateHead, } for
        // TemplateMiddle and TemplateTail.
        && (match kind {
            TemplateKind::NoSubstitution | TemplateKind::Head => s[i] == '`' as u32,
            TemplateKind::Middle | TemplateKind::Tail => s[i] == '}' as u32,
        })
        // The closing: ` for NoSubstitutionTemplate and TemplateTail, ${ for
        // TemplateHead and TemplateMiddle.
        && (match kind {
            TemplateKind::NoSubstitution | TemplateKind::Tail => s[j - 1] == '`' as u32,
            TemplateKind::Head | TemplateKind::Middle => is_lit(s, j - 2, j, seq!['$', '{']),
        })
        // TemplateCharacters? between.
        && (if i + 1 + close_len == j {
            tv == Some(Seq::<u16>::empty()) && trv.len() == 0
        } else {
            template_characters(s, i + 1, j - close_len, tv, trv)
        })
}

// ---------------------------------------------------------------------
// §12 The goal symbols and the longest input element.
// ---------------------------------------------------------------------

/// §12 `InputElementDiv`, `InputElementRegExp`,
/// `InputElementRegExpOrTemplateTail`, `InputElementTemplateTail` and
/// `InputElementHashbangOrRegExp`: whether the range `s[i..j)` is an input
/// element of kind `kind` for `goal`. `html` is Annex B.1.1's mode.
pub open spec fn element_matches(
    goal: Goal,
    html: bool,
    kind: ElementKind,
    s: Src,
    i: int,
    j: int,
) -> bool {
    match kind {
        // Every goal has WhiteSpace, LineTerminator and CommonToken.
        ElementKind::WhiteSpace => white_space(s, i, j),
        ElementKind::LineTerminator => line_terminator(s, i, j),
        // Every goal has Comment. InputElementHashbangOrRegExp has Annex B's
        // HTMLCloseComment too (at the start of the source text only).
        ElementKind::Comment => comment(s, i, j, html)
            || (html && goal == Goal::InputElementHashbangOrRegExp && i == 0
                && html_close_comment(s, i, j)),
        // Only InputElementHashbangOrRegExp has HashbangComment (the start
        // of the source text only).
        ElementKind::HashbangComment => goal == Goal::InputElementHashbangOrRegExp && i == 0
            && hashbang_comment(s, i, j),
        // CommonToken :: IdentifierName | PrivateIdentifier | Punctuator |
        // NumericLiteral | StringLiteral | Template
        ElementKind::IdentifierName => identifier_name(s, i, j),
        ElementKind::PrivateIdentifier => private_identifier(s, i, j),
        ElementKind::Punctuator => punctuator(s, i, j),
        ElementKind::NumericLiteral => numeric_literal(s, i, j),
        ElementKind::StringLiteral => string_literal(s, i, j),
        ElementKind::Template(TemplateKind::NoSubstitution) => exists|
            tv: Tv,
            trv: Seq<u16>,
        | template_part(s, i, j, TemplateKind::NoSubstitution, tv, trv),
        ElementKind::Template(TemplateKind::Head) => exists|tv: Tv, trv: Seq<u16>|
            template_part(s, i, j, TemplateKind::Head, tv, trv),
        // TemplateSubstitutionTail: InputElementRegExpOrTemplateTail and
        // InputElementTemplateTail.
        ElementKind::Template(TemplateKind::Middle) => (goal
            == Goal::InputElementRegExpOrTemplateTail || goal == Goal::InputElementTemplateTail)
            && exists|tv: Tv, trv: Seq<u16>| template_part(s, i, j, TemplateKind::Middle, tv, trv),
        ElementKind::Template(TemplateKind::Tail) => (goal
            == Goal::InputElementRegExpOrTemplateTail || goal == Goal::InputElementTemplateTail)
            && exists|tv: Tv, trv: Seq<u16>| template_part(s, i, j, TemplateKind::Tail, tv, trv),
        // DivPunctuator: InputElementDiv and InputElementTemplateTail.
        ElementKind::DivPunctuator => (goal == Goal::InputElementDiv
            || goal == Goal::InputElementTemplateTail) && div_punctuator(s, i, j),
        // RightBracePunctuator: InputElementDiv and InputElementRegExp.
        ElementKind::RightBracePunctuator => (goal == Goal::InputElementDiv
            || goal == Goal::InputElementRegExp) && right_brace_punctuator(s, i, j),
        // RegularExpressionLiteral: InputElementRegExp,
        // InputElementRegExpOrTemplateTail and InputElementHashbangOrRegExp.
        ElementKind::RegularExpressionLiteral => (goal == Goal::InputElementRegExp
            || goal == Goal::InputElementRegExpOrTemplateTail
            || goal == Goal::InputElementHashbangOrRegExp)
            && exists|b: int| regexp_literal(s, i, j, b),
    }
}

/// Some alternative of the goal symbol derives `s[i..j)`.
pub open spec fn any_element_matches(goal: Goal, html: bool, s: Src, i: int, j: int) -> bool {
    element_matches(goal, html, ElementKind::WhiteSpace, s, i, j)
        || element_matches(goal, html, ElementKind::LineTerminator, s, i, j)
        || element_matches(goal, html, ElementKind::Comment, s, i, j)
        || element_matches(goal, html, ElementKind::HashbangComment, s, i, j)
        || element_matches(goal, html, ElementKind::IdentifierName, s, i, j)
        || element_matches(goal, html, ElementKind::PrivateIdentifier, s, i, j)
        || element_matches(goal, html, ElementKind::Punctuator, s, i, j)
        || element_matches(goal, html, ElementKind::NumericLiteral, s, i, j)
        || element_matches(goal, html, ElementKind::StringLiteral, s, i, j)
        || element_matches(goal, html, ElementKind::Template(TemplateKind::NoSubstitution), s, i, j)
        || element_matches(goal, html, ElementKind::Template(TemplateKind::Head), s, i, j)
        || element_matches(goal, html, ElementKind::Template(TemplateKind::Middle), s, i, j)
        || element_matches(goal, html, ElementKind::Template(TemplateKind::Tail), s, i, j)
        || element_matches(goal, html, ElementKind::DivPunctuator, s, i, j)
        || element_matches(goal, html, ElementKind::RightBracePunctuator, s, i, j)
        || element_matches(goal, html, ElementKind::RegularExpressionLiteral, s, i, j)
}

/// The largest `n` in `1..=m` such that some alternative of the goal derives
/// `s[i..i + n)`, and 0 if there is none.
pub open spec fn longest_len_upto(goal: Goal, html: bool, s: Src, i: int, m: int) -> int
    decreases m,
{
    if m <= 0 {
        0
    } else if i + m <= s.len() && any_element_matches(goal, html, s, i, i + m) {
        m
    } else {
        longest_len_upto(goal, html, s, i, m - 1)
    }
}

/// §12: "The source text is scanned from left to right, repeatedly taking
/// the longest possible sequence of code points as the next input element."
/// The length of the longest input element of `goal` that starts at `i`,
/// or 0 if no alternative derives a prefix of `s[i..]`.
pub open spec fn longest_len(goal: Goal, html: bool, s: Src, i: int) -> int {
    longest_len_upto(goal, html, s, i, s.len() - i)
}

/// The ways a lexical step can fail.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LexError {
    /// No input element of the goal symbol starts at this position (an
    /// unterminated string, comment or template, a stray `@`, a malformed
    /// escape in a string, a code point above U+10FFFF, and so on).
    NoInputElement,
    /// §12.9.3: the code point after a `NumericLiteral` is an
    /// `IdentifierStart` or `DecimalDigit` (`3in`).
    IdentifierAfterNumericLiteral,
    /// §12.7.1.1: a `UnicodeEscapeSequence` in an `IdentifierName` that is
    /// not matched by `IdentifierStartChar` (first) or `IdentifierPartChar`.
    InvalidIdentifierEscape,
}

/// The error, if any, of lexing one input element of `goal` at `i`
/// (`0 <= i <= s.len()`): `None` if `i` is the end of the source text (there
/// is no element), or if the longest element is fine.
pub open spec fn lex_error(goal: Goal, html: bool, s: Src, i: int) -> Option<LexError> {
    let n = longest_len(goal, html, s, i);
    if i >= s.len() {
        None
    } else if n == 0 {
        Some(LexError::NoInputElement)
    } else if element_matches(goal, html, ElementKind::NumericLiteral, s, i, i + n)
        && numeric_literal_follow_error(s, i + n) {
        Some(LexError::IdentifierAfterNumericLiteral)
    } else if (element_matches(goal, html, ElementKind::IdentifierName, s, i, i + n)
        && !identifier_name_valid(s, i, i + n))
        || (element_matches(goal, html, ElementKind::PrivateIdentifier, s, i, i + n)
        && !identifier_name_valid(s, i + 1, i + n)) {
        Some(LexError::InvalidIdentifierEscape)
    } else {
        None
    }
}

/// An element kind that the syntactic grammar never sees: white space, line
/// terminators and comments (§12: "Comments behave like white space and are
/// discarded").
pub open spec fn is_trivia(kind: ElementKind) -> bool {
    kind == ElementKind::WhiteSpace || kind == ElementKind::LineTerminator
        || kind == ElementKind::Comment || kind == ElementKind::HashbangComment
}

/// The length of the trivia element at `i`: the longest element, if it is
/// trivia, else 0.
pub open spec fn trivia_len(goal: Goal, html: bool, s: Src, i: int) -> int {
    let n = longest_len(goal, html, s, i);
    if n > 0 && i + n <= s.len()
        && (element_matches(goal, html, ElementKind::WhiteSpace, s, i, i + n)
        || element_matches(goal, html, ElementKind::LineTerminator, s, i, i + n)
        || element_matches(goal, html, ElementKind::Comment, s, i, i + n)
        || element_matches(goal, html, ElementKind::HashbangComment, s, i, i + n)) {
        n
    } else {
        0
    }
}

/// The end of the trivia that starts at `i`, and whether it holds a line
/// terminator: the elements of `s[i..end)` are consecutive trivia elements
/// of `goal`, and `newline` is whether any of them "is a LineTerminator"
/// for the syntactic grammar (§12.3, §12.4, Annex B.1.1).
pub open spec fn skip_trivia(goal: Goal, html: bool, s: Src, i: int) -> (int, bool)
    decreases s.len() - i,
{
    let n = trivia_len(goal, html, s, i);
    if 0 < n && i + n <= s.len() {
        let rest = skip_trivia(goal, html, s, i + n);
        (rest.0, rest.1 || contains_line_terminator(s, i, i + n))
    } else {
        (i, false)
    }
}

} // verus!
