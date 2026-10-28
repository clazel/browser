//! An independent transcription of the HTML tokenizer, from a different
//! document than [`super::spec`], written without reading that file (or the
//! other files of the first transcription) (docs/VERIFICATION.md, "Trust
//! without reviewers", item 2).
//!
//! Source: HTML 5.2, W3C Recommendation, 14 December 2017,
//! <https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html>:
//! §8.2.2.5 "Preprocessing the input stream" (only for what the next and
//! current input characters and EOF are) and §8.2.4 "Tokenization", states
//! 8.2.4.1 "Data state" to 8.2.4.79 "Character reference end state". The
//! character classes ("ASCII letter", "ASCII hex digit", "alphanumeric
//! ASCII characters", "ASCII case-insensitive") are the definitions the
//! section links to in `infrastructure.html`. The named character
//! references table (§8.5) is the crate's shared table,
//! `crate::charref::spec::entity_name` / `entity_code_points`; only the
//! table is shared, the longest-match rule over it is transcribed here.
//!
//! W3C HTML 5.2 has 79 tokenizer states (8.2.4.1 to 8.2.4.79), not 80:
//! [`W3cState`] has one variant for each, and there is one `w3c_<state>`
//! spec function for each.
//!
//! Modelling choices (each a difference of form, not of meaning):
//! - The input stream is `input: Seq<u32>`, the code points after
//!   preprocessing (§8.2.2.5: no CR characters remain). The tokenizer
//!   holds `pos: nat`: the next input character is `input[pos]`, and the
//!   EOF character is "the lack of any further characters", `pos ==
//!   input.len()`. Script-created parsers and `document.write()` are not
//!   modelled, so the input is fixed and EOF is its end.
//! - "Consume the next input character" reads `input[pos]` (or EOF) and
//!   advances `pos` by one ([`w3c_switch`]); "reconsume in X" switches to X
//!   and leaves `pos` where it was ([`w3c_reconsume`]), which is the same
//!   thing as "provide it with the current input character instead",
//!   because the current input character is exactly `input[pos]`. Consuming
//!   EOF also advances `pos` (to `input.len() + 1`); every EOF that is not
//!   reconsumed emits an end-of-file token in the same step, so that
//!   position is never read.
//! - A step is one state's handling of one consumed character, with what
//!   it emits returned in order as a `Seq<Token>`. A state that consumes
//!   nothing first (8.2.4.42, 8.2.4.78) is a step that does not move `pos`.
//! - Parse errors are not modelled (they do not change the tokens); each is
//!   kept as a "Parse error." comment where the standard says it.
//! - A character token carries one code point: "emit the characters of the
//!   temporary buffer" emits one `Token::Character` per character, in
//!   order.
//! - The tokenizer stops ([`w3c_stopped`]) once it has emitted the
//!   end-of-file token (`done`); nothing after that is tokenized.
//! - The tree construction stage is not modelled. Its two inputs to the
//!   tokenizer are fields fixed for the run: the tag name of the last start
//!   tag emitted before the run (for "appropriate end tag token", updated
//!   by every start tag the run emits), and whether "there is an adjusted
//!   current node and it is not an element in the HTML namespace" (for
//!   8.2.4.42's CDATA case). [`w3c_initial`] sets the latter to false (no
//!   adjusted current node). The parser pause flag is never set.
//! - The return state is a [`W3cReturnState`], an enum of the five states
//!   the standard ever sets it to (data 8.2.4.1, RCDATA 8.2.4.2, and the
//!   three attribute value states 8.2.4.36 to 8.2.4.38): every "Set the
//!   return state to" in §8.2.4 names one of these, so the type holds every
//!   value the return state can have. [`w3c_return_state`] maps it to the
//!   state it names.
//! - The character reference code is a `nat`: the standard's number is
//!   unbounded and only compared with values up to 0x10FFFF. After 8.2.4.78
//!   it is at most 0x10FFFF, so it fits the `u32` of a code point.
//! - The current tag token's attributes: `current_token`'s attribute list
//!   holds the attributes started before the current one;
//!   `current_attribute` is the current attribute ("Start a new attribute"
//!   sets it), and `current_attribute_removed` records that it was removed
//!   as a duplicate. The standard's tag token is the list plus the current
//!   attribute unless it was removed ([`w3c_tag_with_current_attribute`]);
//!   the current attribute is added to the list when the next one starts or
//!   the tag is emitted. The duplicate rule ("When the user agent leaves
//!   the attribute name state ... if there is already an attribute on the
//!   token with the exact same name, ... the new attribute must be removed
//!   from the token") is applied on each transition out of 8.2.4.33
//!   ([`w3c_leave_attribute_name`]), comparing the name with the list,
//!   which is "the other attributes on the same token". A removed attribute
//!   stays current ("Removing the attribute in this way does not change its
//!   status as the current attribute"), so later appends to its value still
//!   go to it and are discarded with it. Names do not change after the
//!   attribute name state, so comparing then is comparing at emission.
//! - "Create a new start/end tag token" also clears `current_attribute`:
//!   a new token has an empty attribute list and so no current attribute.
//! - The current token is one `Token`; before any is created it is
//!   `Token::EndOfFile`, a placeholder that no state emits as "the current
//!   token" before creating one. The current tag token, comment token and
//!   DOCTYPE token are all this field (the standard has one at a time).
//!   Operations on a token of the wrong kind leave it unchanged (never
//!   reached).
//! - "Append to the current DOCTYPE token's name" when the name is missing
//!   makes the name the appended character. Never reached: every state that
//!   appends to the name is entered after the name was set.
//! - Equality of strings (temporary buffer is "script", appropriate end tag,
//!   duplicate attribute names, the matches of 8.2.4.42, 8.2.4.56 and
//!   8.2.4.72) is written as recursion over indices, not `==` on sequences
//!   or quantifiers, so that Verus's evaluator can run the functions on
//!   concrete input; [`w3c_same`] is code-point-by-code-point equality.
//! - 8.2.4.72, "Anything else": the state has already consumed the current
//!   input character when it says "Consume the maximum number of characters
//!   possible, with the consumed characters matching one of the
//!   identifiers". This is read as a match that starts with the current
//!   input character (it is one of "the consumed characters"), so the match
//!   is taken at `pos` before the consumption, and when "no match can be
//!   made" no character has been consumed: the character reference end
//!   state then consumes that same character and reconsumes it in the
//!   return state. The other reading (match from the character after the
//!   current one, so `&amp;` would try to match `mp;` and an unmatched
//!   current character would be dropped) is not what the text, which
//!   appends "each character" of the match to the temporary buffer after the
//!   `&`, describes. "Consume the maximum number of characters possible" is
//!   the longest table name that is a prefix of the input from there
//!   ([`w3c_longest_match`]; names are unique, so there is at most one of
//!   a given length).
//! - 8.2.4.79 consumes the next input character and then reconsumes it in
//!   the return state: the step leaves `pos` unchanged.
//!
//! W3C text, read literally (transcribed as written, not corrected):
//! - 8.2.4.77 "Decimal character reference state", ASCII digit: "Multiply
//!   the character reference code by 16." A decimal reference evidently
//!   multiplies by 10; this transcription multiplies by 16, as the text
//!   says (so `&#10;` gives code 0x10).
//! - 8.2.4.78's table includes "0x00 → U+FFFD", so `&#0;` gives U+FFFD
//!   through the table (with a parse error), before the range checks.
//! - 8.2.4.24 "Script data escaped end tag open state", ASCII letter:
//!   "Create a new end tag token." does not say "set its tag name to the
//!   empty string" as 8.2.4.7, 8.2.4.10, 8.2.4.13 and 8.2.4.16 do, and §8.2.4
//!   does not give a new tag token's name. It is created with the empty
//!   name here, like the others.
//!
//! Nothing here uses `super::spec` other than the `Token` and `Attribute`
//! data types.

use super::spec::{Attribute, Token};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The tokenizer's state.
// ---------------------------------------------------------------------------

/// The 79 states of HTML 5.2 §8.2.4, in section order (8.2.4.1 to
/// 8.2.4.79).
pub enum W3cState {
    /// 8.2.4.1 Data state
    Data,
    /// 8.2.4.2 RCDATA state
    Rcdata,
    /// 8.2.4.3 RAWTEXT state
    Rawtext,
    /// 8.2.4.4 Script data state
    ScriptData,
    /// 8.2.4.5 PLAINTEXT state
    Plaintext,
    /// 8.2.4.6 Tag open state
    TagOpen,
    /// 8.2.4.7 End tag open state
    EndTagOpen,
    /// 8.2.4.8 Tag name state
    TagName,
    /// 8.2.4.9 RCDATA less-than sign state
    RcdataLessThanSign,
    /// 8.2.4.10 RCDATA end tag open state
    RcdataEndTagOpen,
    /// 8.2.4.11 RCDATA end tag name state
    RcdataEndTagName,
    /// 8.2.4.12 RAWTEXT less-than sign state
    RawtextLessThanSign,
    /// 8.2.4.13 RAWTEXT end tag open state
    RawtextEndTagOpen,
    /// 8.2.4.14 RAWTEXT end tag name state
    RawtextEndTagName,
    /// 8.2.4.15 Script data less-than sign state
    ScriptDataLessThanSign,
    /// 8.2.4.16 Script data end tag open state
    ScriptDataEndTagOpen,
    /// 8.2.4.17 Script data end tag name state
    ScriptDataEndTagName,
    /// 8.2.4.18 Script data escape start state
    ScriptDataEscapeStart,
    /// 8.2.4.19 Script data escape start dash state
    ScriptDataEscapeStartDash,
    /// 8.2.4.20 Script data escaped state
    ScriptDataEscaped,
    /// 8.2.4.21 Script data escaped dash state
    ScriptDataEscapedDash,
    /// 8.2.4.22 Script data escaped dash dash state
    ScriptDataEscapedDashDash,
    /// 8.2.4.23 Script data escaped less-than sign state
    ScriptDataEscapedLessThanSign,
    /// 8.2.4.24 Script data escaped end tag open state
    ScriptDataEscapedEndTagOpen,
    /// 8.2.4.25 Script data escaped end tag name state
    ScriptDataEscapedEndTagName,
    /// 8.2.4.26 Script data double escape start state
    ScriptDataDoubleEscapeStart,
    /// 8.2.4.27 Script data double escaped state
    ScriptDataDoubleEscaped,
    /// 8.2.4.28 Script data double escaped dash state
    ScriptDataDoubleEscapedDash,
    /// 8.2.4.29 Script data double escaped dash dash state
    ScriptDataDoubleEscapedDashDash,
    /// 8.2.4.30 Script data double escaped less-than sign state
    ScriptDataDoubleEscapedLessThanSign,
    /// 8.2.4.31 Script data double escape end state
    ScriptDataDoubleEscapeEnd,
    /// 8.2.4.32 Before attribute name state
    BeforeAttributeName,
    /// 8.2.4.33 Attribute name state
    AttributeName,
    /// 8.2.4.34 After attribute name state
    AfterAttributeName,
    /// 8.2.4.35 Before attribute value state
    BeforeAttributeValue,
    /// 8.2.4.36 Attribute value (double-quoted) state
    AttributeValueDoubleQuoted,
    /// 8.2.4.37 Attribute value (single-quoted) state
    AttributeValueSingleQuoted,
    /// 8.2.4.38 Attribute value (unquoted) state
    AttributeValueUnquoted,
    /// 8.2.4.39 After attribute value (quoted) state
    AfterAttributeValueQuoted,
    /// 8.2.4.40 Self-closing start tag state
    SelfClosingStartTag,
    /// 8.2.4.41 Bogus comment state
    BogusComment,
    /// 8.2.4.42 Markup declaration open state
    MarkupDeclarationOpen,
    /// 8.2.4.43 Comment start state
    CommentStart,
    /// 8.2.4.44 Comment start dash state
    CommentStartDash,
    /// 8.2.4.45 Comment state
    Comment,
    /// 8.2.4.46 Comment less-than sign state
    CommentLessThanSign,
    /// 8.2.4.47 Comment less-than sign bang state
    CommentLessThanSignBang,
    /// 8.2.4.48 Comment less-than sign bang dash state
    CommentLessThanSignBangDash,
    /// 8.2.4.49 Comment less-than sign bang dash dash state
    CommentLessThanSignBangDashDash,
    /// 8.2.4.50 Comment end dash state
    CommentEndDash,
    /// 8.2.4.51 Comment end state
    CommentEnd,
    /// 8.2.4.52 Comment end bang state
    CommentEndBang,
    /// 8.2.4.53 DOCTYPE state
    Doctype,
    /// 8.2.4.54 Before DOCTYPE name state
    BeforeDoctypeName,
    /// 8.2.4.55 DOCTYPE name state
    DoctypeName,
    /// 8.2.4.56 After DOCTYPE name state
    AfterDoctypeName,
    /// 8.2.4.57 After DOCTYPE public keyword state
    AfterDoctypePublicKeyword,
    /// 8.2.4.58 Before DOCTYPE public identifier state
    BeforeDoctypePublicIdentifier,
    /// 8.2.4.59 DOCTYPE public identifier (double-quoted) state
    DoctypePublicIdentifierDoubleQuoted,
    /// 8.2.4.60 DOCTYPE public identifier (single-quoted) state
    DoctypePublicIdentifierSingleQuoted,
    /// 8.2.4.61 After DOCTYPE public identifier state
    AfterDoctypePublicIdentifier,
    /// 8.2.4.62 Between DOCTYPE public and system identifiers state
    BetweenDoctypePublicAndSystemIdentifiers,
    /// 8.2.4.63 After DOCTYPE system keyword state
    AfterDoctypeSystemKeyword,
    /// 8.2.4.64 Before DOCTYPE system identifier state
    BeforeDoctypeSystemIdentifier,
    /// 8.2.4.65 DOCTYPE system identifier (double-quoted) state
    DoctypeSystemIdentifierDoubleQuoted,
    /// 8.2.4.66 DOCTYPE system identifier (single-quoted) state
    DoctypeSystemIdentifierSingleQuoted,
    /// 8.2.4.67 After DOCTYPE system identifier state
    AfterDoctypeSystemIdentifier,
    /// 8.2.4.68 Bogus DOCTYPE state
    BogusDoctype,
    /// 8.2.4.69 CDATA section state
    CdataSection,
    /// 8.2.4.70 CDATA section bracket state
    CdataSectionBracket,
    /// 8.2.4.71 CDATA section end state
    CdataSectionEnd,
    /// 8.2.4.72 Character reference state
    CharacterReference,
    /// 8.2.4.73 Numeric character reference state
    NumericCharacterReference,
    /// 8.2.4.74 Hexadecimal character reference start state
    HexadecimalCharacterReferenceStart,
    /// 8.2.4.75 Decimal character reference start state
    DecimalCharacterReferenceStart,
    /// 8.2.4.76 Hexadecimal character reference state
    HexadecimalCharacterReference,
    /// 8.2.4.77 Decimal character reference state
    DecimalCharacterReference,
    /// 8.2.4.78 Numeric character reference end state
    NumericCharacterReferenceEnd,
    /// 8.2.4.79 Character reference end state
    CharacterReferenceEnd,
}

/// The values the "return state" is ever set to (see the header).
pub enum W3cReturnState {
    /// 8.2.4.1 Data state
    Data,
    /// 8.2.4.2 RCDATA state
    Rcdata,
    /// 8.2.4.36 Attribute value (double-quoted) state
    AttributeValueDoubleQuoted,
    /// 8.2.4.37 Attribute value (single-quoted) state
    AttributeValueSingleQuoted,
    /// 8.2.4.38 Attribute value (unquoted) state
    AttributeValueUnquoted,
}

/// The state a [`W3cReturnState`] names.
pub open spec fn w3c_return_state(r: W3cReturnState) -> W3cState {
    match r {
        W3cReturnState::Data => W3cState::Data,
        W3cReturnState::Rcdata => W3cState::Rcdata,
        W3cReturnState::AttributeValueDoubleQuoted => W3cState::AttributeValueDoubleQuoted,
        W3cReturnState::AttributeValueSingleQuoted => W3cState::AttributeValueSingleQuoted,
        W3cReturnState::AttributeValueUnquoted => W3cState::AttributeValueUnquoted,
    }
}

/// "the character reference was consumed as part of an attribute (return
/// state is either attribute value (double-quoted) state, attribute value
/// (single-quoted) state or attribute value (unquoted) state)".
pub open spec fn w3c_return_state_is_attribute(r: W3cReturnState) -> bool {
    match r {
        W3cReturnState::AttributeValueDoubleQuoted => true,
        W3cReturnState::AttributeValueSingleQuoted => true,
        W3cReturnState::AttributeValueUnquoted => true,
        _ => false,
    }
}

/// The tokenizer: the state machine's state and the data §8.2.4 says its
/// states share.
pub struct W3cTokenizer {
    /// The state the machine is in.
    pub state: W3cState,
    /// "the character reference state uses a return state to return to the
    /// state it was invoked from".
    pub return_state: W3cReturnState,
    /// "a temporary buffer to track progress".
    pub temporary_buffer: Seq<u32>,
    /// "the character reference code" (8.2.4.73 to 8.2.4.78), unbounded.
    pub character_reference_code: nat,
    /// The current tag, comment or DOCTYPE token (see the header). For a
    /// tag token, its attribute list holds the attributes before the
    /// current one.
    pub current_token: Token,
    /// "the current attribute" of the current tag token, `None` until one
    /// is started in that token.
    pub current_attribute: Option<Attribute>,
    /// The current attribute was removed from the token as a duplicate when
    /// the tokenizer left the attribute name state.
    pub current_attribute_removed: bool,
    /// The tag name of "the last start tag to have been emitted from this
    /// tokenizer", `None` if there is none.
    pub last_start_tag_name: Option<Seq<u32>>,
    /// "there is an adjusted current node and it is not an element in the
    /// HTML namespace" (8.2.4.42), fixed for the run.
    pub adjusted_current_node_not_html: bool,
    /// The position of the next input character in the input.
    pub pos: nat,
    /// The end-of-file token has been emitted.
    pub done: bool,
}

/// What one step returns: the new tokenizer and the tokens emitted, in
/// order.
pub type W3cStep = (W3cTokenizer, Seq<Token>);

// ---------------------------------------------------------------------------
// Input characters and character classes.
// ---------------------------------------------------------------------------

/// The next input character at `pos`, `None` for EOF (§8.2.2.5).
pub open spec fn w3c_next(input: Seq<u32>, pos: nat) -> Option<u32> {
    if pos < input.len() {
        Some(input[pos as int])
    } else {
        None
    }
}

/// `c` is the EOF character.
pub open spec fn w3c_is_eof(c: Option<u32>) -> bool {
    match c {
        Some(_) => false,
        None => true,
    }
}

/// The code point of a character that is not EOF (0 for EOF, never used).
pub open spec fn w3c_cp(c: Option<u32>) -> u32 {
    match c {
        Some(x) => x,
        None => 0,
    }
}

/// `c` is a character in the range `lo` to `hi`, inclusive.
pub open spec fn w3c_in_range(c: Option<u32>, lo: u32, hi: u32) -> bool {
    match c {
        Some(x) => lo <= x && x <= hi,
        None => false,
    }
}

/// U+0009 CHARACTER TABULATION, U+000A LINE FEED, U+000C FORM FEED or
/// U+0020 SPACE: the four entries that share an action in many states.
pub open spec fn w3c_is_tab_lf_ff_space(c: Option<u32>) -> bool {
    c == Some(0x0009u32) || c == Some(0x000Au32) || c == Some(0x000Cu32) || c == Some(0x0020u32)
}

/// "Uppercase ASCII letter": U+0041 (A) to U+005A (Z)
/// (`infrastructure.html#uppercase-ascii-letters`).
pub open spec fn w3c_is_upper_letter(c: Option<u32>) -> bool {
    w3c_in_range(c, 0x41, 0x5A)
}

/// "Lowercase ASCII letter": U+0061 (a) to U+007A (z)
/// (`infrastructure.html#lowercase-ascii-letters`).
pub open spec fn w3c_is_lower_letter(c: Option<u32>) -> bool {
    w3c_in_range(c, 0x61, 0x7A)
}

/// "ASCII letter": an uppercase or lowercase ASCII letter
/// (`infrastructure.html#ascii-letters`).
pub open spec fn w3c_is_letter(c: Option<u32>) -> bool {
    w3c_is_upper_letter(c) || w3c_is_lower_letter(c)
}

/// "ASCII digit": U+0030 (0) to U+0039 (9)
/// (`infrastructure.html#ascii-digits`).
pub open spec fn w3c_is_digit(c: Option<u32>) -> bool {
    w3c_in_range(c, 0x30, 0x39)
}

/// "Uppercase ASCII hex digit": an ASCII digit or U+0041 (A) to U+0046 (F)
/// (`infrastructure.html#uppercase-ascii-hex-digits`). In 8.2.4.76 the
/// ASCII digit entry comes first, so its entry for this class only sees
/// A to F.
pub open spec fn w3c_is_upper_hex_letter(c: Option<u32>) -> bool {
    w3c_in_range(c, 0x41, 0x46)
}

/// "Lowercase ASCII hex digit": an ASCII digit or U+0061 (a) to U+0066 (f)
/// (`infrastructure.html#lowercase-ascii-hex-digits`); as above, its
/// entry in 8.2.4.76 only sees a to f.
pub open spec fn w3c_is_lower_hex_letter(c: Option<u32>) -> bool {
    w3c_in_range(c, 0x61, 0x66)
}

/// "ASCII hex digit": an ASCII digit, A to F or a to f
/// (`infrastructure.html#ascii-hex-digits`).
pub open spec fn w3c_is_hex_digit(c: Option<u32>) -> bool {
    w3c_is_digit(c) || w3c_is_upper_hex_letter(c) || w3c_is_lower_hex_letter(c)
}

/// "alphanumeric ASCII characters": ASCII digits and ASCII letters
/// (`infrastructure.html#alphanumeric-ascii-characters`).
pub open spec fn w3c_is_alphanumeric(c: Option<u32>) -> bool {
    w3c_is_digit(c) || w3c_is_letter(c)
}

/// "the lowercase version of the current input character (add 0x0020 to
/// the character's code point)", for an uppercase ASCII letter.
pub open spec fn w3c_lower(c: u32) -> u32 {
    (c + 0x20) as u32
}

/// ASCII lowercase of any code point (for "ASCII case-insensitive":
/// uppercase ASCII letters compared as their lowercase).
pub open spec fn w3c_ascii_fold(c: u32) -> u32 {
    if 0x41 <= c && c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// `word[k..]` equals `input[pos + k ..]` code point by code point, as far
/// as `word` goes (and `input` is long enough).
pub open spec fn w3c_match_from(input: Seq<u32>, pos: nat, word: Seq<u32>, k: nat) -> bool
    decreases word.len() - k,
{
    if k >= word.len() {
        true
    } else {
        pos + k < input.len() && input[(pos + k) as int] == word[k as int] && w3c_match_from(input, pos, word, k + 1)
    }
}

/// As [`w3c_match_from`], comparing ASCII case-insensitively.
pub open spec fn w3c_match_ci_from(input: Seq<u32>, pos: nat, word: Seq<u32>, k: nat) -> bool
    decreases word.len() - k,
{
    if k >= word.len() {
        true
    } else {
        pos + k < input.len() && w3c_ascii_fold(input[(pos + k) as int]) == w3c_ascii_fold(word[k as int])
            && w3c_match_ci_from(input, pos, word, k + 1)
    }
}

/// The characters of `input` from `pos` are a case-sensitive match for
/// `word`.
pub open spec fn w3c_word_at(input: Seq<u32>, pos: nat, word: Seq<u32>) -> bool {
    pos + word.len() <= input.len() && w3c_match_from(input, pos, word, 0)
}

/// The characters of `input` from `pos` are an ASCII case-insensitive
/// match for `word`.
pub open spec fn w3c_word_at_ci(input: Seq<u32>, pos: nat, word: Seq<u32>) -> bool {
    pos + word.len() <= input.len() && w3c_match_ci_from(input, pos, word, 0)
}

/// Two strings are the same string.
pub open spec fn w3c_same(a: Seq<u32>, b: Seq<u32>) -> bool {
    a.len() == b.len() && w3c_match_from(a, 0, b, 0)
}

/// "DOCTYPE".
pub open spec fn w3c_word_doctype() -> Seq<u32> {
    seq![0x44u32, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45]
}

/// "[CDATA[".
pub open spec fn w3c_word_cdata() -> Seq<u32> {
    seq![0x5Bu32, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B]
}

/// "PUBLIC".
pub open spec fn w3c_word_public() -> Seq<u32> {
    seq![0x50u32, 0x55, 0x42, 0x4C, 0x49, 0x43]
}

/// "SYSTEM".
pub open spec fn w3c_word_system() -> Seq<u32> {
    seq![0x53u32, 0x59, 0x53, 0x54, 0x45, 0x4D]
}

/// "script".
pub open spec fn w3c_word_script() -> Seq<u32> {
    seq![0x73u32, 0x63, 0x72, 0x69, 0x70, 0x74]
}

// ---------------------------------------------------------------------------
// Moving between states.
// ---------------------------------------------------------------------------

/// Go to state `s` with the next input character at `pos`.
pub open spec fn w3c_go(t: W3cTokenizer, s: W3cState, pos: nat) -> W3cTokenizer {
    W3cTokenizer { state: s, pos, ..t }
}

/// The current input character was consumed; "switch to" `s` (or stay in
/// a state, when `s` is the current one), which consumes the next one.
pub open spec fn w3c_switch(t: W3cTokenizer, s: W3cState) -> W3cTokenizer {
    w3c_go(t, s, t.pos + 1)
}

/// "Reconsume in" `s`: switch to `s` without advancing.
pub open spec fn w3c_reconsume(t: W3cTokenizer, s: W3cState) -> W3cTokenizer {
    w3c_go(t, s, t.pos)
}

/// "Emit an end-of-file token" after `before`, having consumed the EOF.
pub open spec fn w3c_emit_eof(t: W3cTokenizer, before: Seq<Token>) -> W3cStep {
    (W3cTokenizer { done: true, ..w3c_switch(t, t.state) }, before.push(Token::EndOfFile))
}

/// A character token for each character of `s`, in order.
pub open spec fn w3c_characters(s: Seq<u32>) -> Seq<Token> {
    s.map_values(|c: u32| Token::Character(c))
}

// ---------------------------------------------------------------------------
// Tag tokens and attributes.
// ---------------------------------------------------------------------------

/// "Create a new start tag token, set its tag name to the empty string":
/// "its self-closing flag must be unset ... and its attributes list must
/// be empty".
pub open spec fn w3c_new_start_tag() -> Token {
    Token::StartTag { tag_name: seq![], self_closing: false, attributes: seq![] }
}

/// "Create a new end tag token, set its tag name to the empty string".
pub open spec fn w3c_new_end_tag() -> Token {
    Token::EndTag { tag_name: seq![], self_closing: false, attributes: seq![] }
}

/// Make `tok` the current tag token; it has no current attribute yet.
pub open spec fn w3c_create_tag(t: W3cTokenizer, tok: Token) -> W3cTokenizer {
    W3cTokenizer { current_token: tok, current_attribute: None, current_attribute_removed: false, ..t }
}

/// Append `c` to a tag token's tag name.
pub open spec fn w3c_tag_name_append(tok: Token, c: u32) -> Token {
    match tok {
        Token::StartTag { tag_name, self_closing, attributes } => Token::StartTag {
            tag_name: tag_name.push(c),
            self_closing,
            attributes,
        },
        Token::EndTag { tag_name, self_closing, attributes } => Token::EndTag {
            tag_name: tag_name.push(c),
            self_closing,
            attributes,
        },
        _ => tok,
    }
}

/// "Set the self-closing flag of the current tag token."
pub open spec fn w3c_tag_set_self_closing(tok: Token) -> Token {
    match tok {
        Token::StartTag { tag_name, self_closing, attributes } => Token::StartTag {
            tag_name,
            self_closing: true,
            attributes,
        },
        Token::EndTag { tag_name, self_closing, attributes } => Token::EndTag {
            tag_name,
            self_closing: true,
            attributes,
        },
        _ => tok,
    }
}

/// A tag token's list of attributes.
pub open spec fn w3c_tag_attributes(tok: Token) -> Seq<Attribute> {
    match tok {
        Token::StartTag { attributes, .. } => attributes,
        Token::EndTag { attributes, .. } => attributes,
        _ => seq![],
    }
}

/// A tag token with its list of attributes replaced by `attrs`.
pub open spec fn w3c_tag_set_attributes(tok: Token, attrs: Seq<Attribute>) -> Token {
    match tok {
        Token::StartTag { tag_name, self_closing, attributes } => Token::StartTag {
            tag_name,
            self_closing,
            attributes: attrs,
        },
        Token::EndTag { tag_name, self_closing, attributes } => Token::EndTag {
            tag_name,
            self_closing,
            attributes: attrs,
        },
        _ => tok,
    }
}

/// The current tag token as the standard has it: its list, then the
/// current attribute unless that was removed as a duplicate.
pub open spec fn w3c_tag_with_current_attribute(t: W3cTokenizer) -> Token {
    match t.current_attribute {
        Some(a) => if t.current_attribute_removed {
            t.current_token
        } else {
            w3c_tag_set_attributes(t.current_token, w3c_tag_attributes(t.current_token).push(a))
        },
        None => t.current_token,
    }
}

/// "Start a new attribute in the current tag token", with name `name` and
/// value the empty string. The previous current attribute, unless
/// removed, is now part of the token's list.
pub open spec fn w3c_start_attribute(t: W3cTokenizer, name: Seq<u32>) -> W3cTokenizer {
    W3cTokenizer {
        current_token: w3c_tag_with_current_attribute(t),
        current_attribute: Some(Attribute { name, value: seq![] }),
        current_attribute_removed: false,
        ..t
    }
}

/// Some attribute of `attrs` from index `k` on has the name `name`.
pub open spec fn w3c_name_taken(attrs: Seq<Attribute>, name: Seq<u32>, k: nat) -> bool
    decreases attrs.len() - k,
{
    if k >= attrs.len() {
        false
    } else {
        w3c_same(attrs[k as int].name, name) || w3c_name_taken(attrs, name, k + 1)
    }
}

/// "When the user agent leaves the attribute name state (and before
/// emitting the tag token, if appropriate), the complete attribute's name
/// must be compared to the other attributes on the same token; if there is
/// already an attribute on the token with the exact same name, then this is
/// a parse error and the new attribute must be removed from the token."
pub open spec fn w3c_leave_attribute_name(t: W3cTokenizer) -> W3cTokenizer {
    match t.current_attribute {
        Some(a) => W3cTokenizer {
            current_attribute_removed: w3c_name_taken(w3c_tag_attributes(t.current_token), a.name, 0),
            ..t
        },
        None => t,
    }
}

/// Append `c` to the current attribute's name.
pub open spec fn w3c_attribute_name_append(t: W3cTokenizer, c: u32) -> W3cTokenizer {
    match t.current_attribute {
        Some(a) => W3cTokenizer {
            current_attribute: Some(Attribute { name: a.name.push(c), value: a.value }),
            ..t
        },
        None => t,
    }
}

/// Append the characters `s` to the current attribute's value.
pub open spec fn w3c_attribute_value_append(t: W3cTokenizer, s: Seq<u32>) -> W3cTokenizer {
    match t.current_attribute {
        Some(a) => W3cTokenizer {
            current_attribute: Some(Attribute { name: a.name, value: a.value + s }),
            ..t
        },
        None => t,
    }
}

/// "the current end tag token is an appropriate end tag token": "an end
/// tag token whose tag name matches the tag name of the last start tag to
/// have been emitted from this tokenizer, if any. If no start tag has been
/// emitted from this tokenizer, then no end tag token is appropriate."
pub open spec fn w3c_is_appropriate_end_tag(t: W3cTokenizer) -> bool {
    match t.current_token {
        Token::EndTag { tag_name, .. } => match t.last_start_tag_name {
            Some(last) => w3c_same(tag_name, last),
            None => false,
        },
        _ => false,
    }
}

/// The tokenizer after "Emit the current tag token": the token as emitted
/// ([`w3c_tag_with_current_attribute`]) is the current token, and a start
/// tag becomes the last start tag emitted.
pub open spec fn w3c_after_emit_tag(t: W3cTokenizer) -> W3cTokenizer {
    let tok = w3c_tag_with_current_attribute(t);
    W3cTokenizer {
        current_token: tok,
        current_attribute: None,
        current_attribute_removed: false,
        last_start_tag_name: match tok {
            Token::StartTag { tag_name, .. } => Some(tag_name),
            _ => t.last_start_tag_name,
        },
        ..t
    }
}

/// "Switch to the data state. Emit the current tag token." (the current
/// input character was consumed).
pub open spec fn w3c_emit_tag_to_data(t: W3cTokenizer) -> W3cStep {
    (w3c_switch(w3c_after_emit_tag(t), W3cState::Data), seq![w3c_tag_with_current_attribute(t)])
}

// ---------------------------------------------------------------------------
// Comment and DOCTYPE tokens.
// ---------------------------------------------------------------------------

/// "Create a comment token whose data is the empty string."
pub open spec fn w3c_new_comment() -> Token {
    Token::Comment { data: seq![] }
}

/// Append `s` to the comment token's data.
pub open spec fn w3c_comment_append(tok: Token, s: Seq<u32>) -> Token {
    match tok {
        Token::Comment { data } => Token::Comment { data: data + s },
        _ => tok,
    }
}

/// [`w3c_comment_append`] on the tokenizer's current token.
pub open spec fn w3c_append_to_comment(t: W3cTokenizer, s: Seq<u32>) -> W3cTokenizer {
    W3cTokenizer { current_token: w3c_comment_append(t.current_token, s), ..t }
}

/// "Create a new DOCTYPE token": "its name, public identifier, and system
/// identifier must be marked as missing ... and the force-quirks flag must
/// be set to off".
pub open spec fn w3c_new_doctype() -> Token {
    Token::Doctype { name: None, public_identifier: None, system_identifier: None, force_quirks: false }
}

/// Append `c` to `s`, a missing string becoming the one character.
pub open spec fn w3c_optional_append(s: Option<Seq<u32>>, c: u32) -> Option<Seq<u32>> {
    match s {
        Some(v) => Some(v.push(c)),
        None => Some(seq![c]),
    }
}

/// Set the DOCTYPE token's name to `s`.
pub open spec fn w3c_doctype_set_name(tok: Token, s: Seq<u32>) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name: Some(s),
            public_identifier,
            system_identifier,
            force_quirks,
        },
        _ => tok,
    }
}

/// Append `c` to the DOCTYPE token's name.
pub open spec fn w3c_doctype_append_name(tok: Token, c: u32) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name: w3c_optional_append(name, c),
            public_identifier,
            system_identifier,
            force_quirks,
        },
        _ => tok,
    }
}

/// "Set the DOCTYPE token's public identifier to the empty string (not
/// missing)".
pub open spec fn w3c_doctype_empty_public(tok: Token) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name,
            public_identifier: Some(seq![]),
            system_identifier,
            force_quirks,
        },
        _ => tok,
    }
}

/// Append `c` to the DOCTYPE token's public identifier.
pub open spec fn w3c_doctype_append_public(tok: Token, c: u32) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name,
            public_identifier: w3c_optional_append(public_identifier, c),
            system_identifier,
            force_quirks,
        },
        _ => tok,
    }
}

/// "Set the DOCTYPE token's system identifier to the empty string (not
/// missing)".
pub open spec fn w3c_doctype_empty_system(tok: Token) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name,
            public_identifier,
            system_identifier: Some(seq![]),
            force_quirks,
        },
        _ => tok,
    }
}

/// Append `c` to the DOCTYPE token's system identifier.
pub open spec fn w3c_doctype_append_system(tok: Token, c: u32) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name,
            public_identifier,
            system_identifier: w3c_optional_append(system_identifier, c),
            force_quirks,
        },
        _ => tok,
    }
}

/// "Set the DOCTYPE token's force-quirks flag to on."
pub open spec fn w3c_doctype_force_quirks(tok: Token) -> Token {
    match tok {
        Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
            name,
            public_identifier,
            system_identifier,
            force_quirks: true,
        },
        _ => tok,
    }
}

/// [`w3c_doctype_force_quirks`] on the tokenizer's current token.
pub open spec fn w3c_force_quirks(t: W3cTokenizer) -> W3cTokenizer {
    W3cTokenizer { current_token: w3c_doctype_force_quirks(t.current_token), ..t }
}

/// "Parse error. Set the DOCTYPE token's force-quirks flag to on. Emit that
/// DOCTYPE token. Emit an end-of-file token." (the EOF entry of most
/// DOCTYPE states).
pub open spec fn w3c_doctype_eof(t: W3cTokenizer) -> W3cStep {
    let t1 = w3c_force_quirks(t);
    w3c_emit_eof(t1, seq![t1.current_token])
}

/// "Parse error. Set the DOCTYPE token's force-quirks flag to on. Switch to
/// the data state. Emit that DOCTYPE token."
pub open spec fn w3c_doctype_quirks_to_data(t: W3cTokenizer) -> W3cStep {
    let t1 = w3c_force_quirks(t);
    (w3c_switch(t1, W3cState::Data), seq![t1.current_token])
}

/// "Parse error. Set the DOCTYPE token's force-quirks flag to on. Switch to
/// the bogus DOCTYPE state."
pub open spec fn w3c_doctype_quirks_to_bogus(t: W3cTokenizer) -> W3cStep {
    (w3c_switch(w3c_force_quirks(t), W3cState::BogusDoctype), seq![])
}

// ---------------------------------------------------------------------------
// 8.2.4.1 to 8.2.4.5: the content states.
// ---------------------------------------------------------------------------

/// 8.2.4.1 Data state.
pub open spec fn w3c_data(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0026u32) {
        // U+0026 AMPERSAND (&): "Set the return state to the data state.
        // Switch to the character reference state."
        (
            W3cTokenizer { return_state: W3cReturnState::Data, ..w3c_switch(t, W3cState::CharacterReference) },
            seq![],
        )
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the tag open state."
        (w3c_switch(t, W3cState::TagOpen), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit the current input character as a
        // character token."
        (w3c_switch(t, W3cState::Data), seq![Token::Character(0x0000)])
    } else if w3c_is_eof(c) {
        // EOF: "Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::Data), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.2 RCDATA state.
pub open spec fn w3c_rcdata(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0026u32) {
        // U+0026 AMPERSAND (&): "Set the return state to the RCDATA state.
        // Switch to the character reference state."
        (
            W3cTokenizer { return_state: W3cReturnState::Rcdata, ..w3c_switch(t, W3cState::CharacterReference) },
            seq![],
        )
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the RCDATA less-than sign
        // state."
        (w3c_switch(t, W3cState::RcdataLessThanSign), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit a U+FFFD REPLACEMENT CHARACTER
        // character token."
        (w3c_switch(t, W3cState::Rcdata), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::Rcdata), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.3 RAWTEXT state.
pub open spec fn w3c_rawtext(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the RAWTEXT less-than sign
        // state."
        (w3c_switch(t, W3cState::RawtextLessThanSign), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit a U+FFFD REPLACEMENT CHARACTER
        // character token."
        (w3c_switch(t, W3cState::Rawtext), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::Rawtext), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.4 Script data state.
pub open spec fn w3c_script_data(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data less-than
        // sign state."
        (w3c_switch(t, W3cState::ScriptDataLessThanSign), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit a U+FFFD REPLACEMENT CHARACTER
        // character token."
        (w3c_switch(t, W3cState::ScriptData), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::ScriptData), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.5 PLAINTEXT state.
pub open spec fn w3c_plaintext(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit a U+FFFD REPLACEMENT CHARACTER
        // character token."
        (w3c_switch(t, W3cState::Plaintext), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::Plaintext), seq![Token::Character(w3c_cp(c))])
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.6 to 8.2.4.8: tags.
// ---------------------------------------------------------------------------

/// 8.2.4.6 Tag open state.
pub open spec fn w3c_tag_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0021u32) {
        // U+0021 EXCLAMATION MARK (!): "Switch to the markup declaration
        // open state."
        (w3c_switch(t, W3cState::MarkupDeclarationOpen), seq![])
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Switch to the end tag open state."
        (w3c_switch(t, W3cState::EndTagOpen), seq![])
    } else if w3c_is_letter(c) {
        // ASCII letter: "Create a new start tag token, set its tag name to
        // the empty string. Reconsume in the tag name state."
        (w3c_reconsume(w3c_create_tag(t, w3c_new_start_tag()), W3cState::TagName), seq![])
    } else if c == Some(0x003Fu32) {
        // U+003F QUESTION MARK (?): "Parse error. Create a comment token
        // whose data is the empty string. Reconsume in the bogus comment
        // state."
        (
            w3c_reconsume(W3cTokenizer { current_token: w3c_new_comment(), ..t }, W3cState::BogusComment),
            seq![],
        )
    } else {
        // Anything else: "Parse error. Emit a U+003C LESS-THAN SIGN
        // character token. Reconsume in the data state."
        (w3c_reconsume(t, W3cState::Data), seq![Token::Character(0x003C)])
    }
}

/// 8.2.4.7 End tag open state.
pub open spec fn w3c_end_tag_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_letter(c) {
        // ASCII letter: "Create a new end tag token, set its tag name to
        // the empty string. Reconsume in the tag name state."
        (w3c_reconsume(w3c_create_tag(t, w3c_new_end_tag()), W3cState::TagName), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Switch to the data
        // state."
        (w3c_switch(t, W3cState::Data), seq![])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit a U+003C LESS-THAN SIGN character token, a
        // U+002F SOLIDUS character token and an end-of-file token."
        w3c_emit_eof(t, seq![Token::Character(0x003C), Token::Character(0x002F)])
    } else {
        // Anything else: "Parse error. Create a comment token whose data is
        // the empty string. Reconsume in the bogus comment state."
        (
            w3c_reconsume(W3cTokenizer { current_token: w3c_new_comment(), ..t }, W3cState::BogusComment),
            seq![],
        )
    }
}

/// 8.2.4.8 Tag name state.
pub open spec fn w3c_tag_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the before attribute name state."
        (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Switch to the self-closing start tag state."
        (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current tag token."
        w3c_emit_tag_to_data(t)
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter: "Append the lowercase version of the
        // current input character (add 0x0020 to the character's code
        // point) to the current tag token's tag name."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_tag_name_append(t.current_token, w3c_lower(w3c_cp(c))), ..t },
                W3cState::TagName,
            ),
            seq![],
        )
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current tag token's tag name."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_tag_name_append(t.current_token, 0xFFFD), ..t },
                W3cState::TagName,
            ),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Append the current input character to the current
        // tag token's tag name."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_tag_name_append(t.current_token, w3c_cp(c)), ..t },
                W3cState::TagName,
            ),
            seq![],
        )
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.9 to 8.2.4.17: end tags in RCDATA, RAWTEXT and script data.
// ---------------------------------------------------------------------------

/// The "Anything else" entry of the end tag name states (8.2.4.11,
/// 8.2.4.14, 8.2.4.17, 8.2.4.25): "Emit a U+003C LESS-THAN SIGN character
/// token, a U+002F SOLIDUS character token, and a character token for each
/// of the characters in the temporary buffer (in the order they were added
/// to the buffer). Reconsume in the" `text` state.
pub open spec fn w3c_end_tag_name_anything_else(t: W3cTokenizer, text: W3cState) -> W3cStep {
    (
        w3c_reconsume(t, text),
        seq![Token::Character(0x003C), Token::Character(0x002F)] + w3c_characters(t.temporary_buffer),
    )
}

/// The uppercase ASCII letter entry of the end tag name states: "Append the
/// lowercase version of the current input character (add 0x0020 to the
/// character's code point) to the current tag token's tag name. Append the
/// current input character to the temporary buffer."
pub open spec fn w3c_end_tag_name_upper(t: W3cTokenizer, c: u32) -> W3cStep {
    (
        w3c_switch(
            W3cTokenizer {
                current_token: w3c_tag_name_append(t.current_token, w3c_lower(c)),
                temporary_buffer: t.temporary_buffer.push(c),
                ..t
            },
            t.state,
        ),
        seq![],
    )
}

/// The lowercase ASCII letter entry of the end tag name states: "Append
/// the current input character to the current tag token's tag name. Append
/// the current input character to the temporary buffer."
pub open spec fn w3c_end_tag_name_lower(t: W3cTokenizer, c: u32) -> W3cStep {
    (
        w3c_switch(
            W3cTokenizer {
                current_token: w3c_tag_name_append(t.current_token, c),
                temporary_buffer: t.temporary_buffer.push(c),
                ..t
            },
            t.state,
        ),
        seq![],
    )
}

/// 8.2.4.9 RCDATA less-than sign state.
pub open spec fn w3c_rcdata_less_than_sign(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Set the temporary buffer to the empty string.
        // Switch to the RCDATA end tag open state."
        (
            w3c_switch(W3cTokenizer { temporary_buffer: seq![], ..t }, W3cState::RcdataEndTagOpen),
            seq![],
        )
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the RCDATA state."
        (w3c_reconsume(t, W3cState::Rcdata), seq![Token::Character(0x003C)])
    }
}

/// 8.2.4.10 RCDATA end tag open state.
pub open spec fn w3c_rcdata_end_tag_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_letter(c) {
        // ASCII letter: "Create a new end tag token, set its tag name to
        // the empty string. Reconsume in RCDATA end tag name state."
        (w3c_reconsume(w3c_create_tag(t, w3c_new_end_tag()), W3cState::RcdataEndTagName), seq![])
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token and a
        // U+002F SOLIDUS character token. Reconsume in the RCDATA state."
        (w3c_reconsume(t, W3cState::Rcdata), seq![Token::Character(0x003C), Token::Character(0x002F)])
    }
}

/// 8.2.4.11 RCDATA end tag name state.
pub open spec fn w3c_rcdata_end_tag_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "If the current end tag token is an
        // appropriate end tag token, then switch to the before attribute
        // name state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::Rcdata)
        }
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "If the current end tag token is an
        // appropriate end tag token, then switch to the self-closing start
        // tag state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::Rcdata)
        }
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "If the current end tag token is an
        // appropriate end tag token, then switch to the data state and emit
        // the current tag token. Otherwise, treat it as per the "anything
        // else" entry below."
        if w3c_is_appropriate_end_tag(t) {
            w3c_emit_tag_to_data(t)
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::Rcdata)
        }
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter (see w3c_end_tag_name_upper).
        w3c_end_tag_name_upper(t, w3c_cp(c))
    } else if w3c_is_lower_letter(c) {
        // Lowercase ASCII letter (see w3c_end_tag_name_lower).
        w3c_end_tag_name_lower(t, w3c_cp(c))
    } else {
        // Anything else: "Emit ... Reconsume in the RCDATA state."
        w3c_end_tag_name_anything_else(t, W3cState::Rcdata)
    }
}

/// 8.2.4.12 RAWTEXT less-than sign state.
pub open spec fn w3c_rawtext_less_than_sign(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Set the temporary buffer to the empty string.
        // Switch to the RAWTEXT end tag open state."
        (
            w3c_switch(W3cTokenizer { temporary_buffer: seq![], ..t }, W3cState::RawtextEndTagOpen),
            seq![],
        )
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the RAWTEXT state."
        (w3c_reconsume(t, W3cState::Rawtext), seq![Token::Character(0x003C)])
    }
}

/// 8.2.4.13 RAWTEXT end tag open state.
pub open spec fn w3c_rawtext_end_tag_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_letter(c) {
        // ASCII letter: "Create a new end tag token, set its tag name to
        // the empty string. Reconsume in the RAWTEXT end tag name state."
        (w3c_reconsume(w3c_create_tag(t, w3c_new_end_tag()), W3cState::RawtextEndTagName), seq![])
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token and a
        // U+002F SOLIDUS character token. Reconsume in the RAWTEXT state."
        (w3c_reconsume(t, W3cState::Rawtext), seq![Token::Character(0x003C), Token::Character(0x002F)])
    }
}

/// 8.2.4.14 RAWTEXT end tag name state.
pub open spec fn w3c_rawtext_end_tag_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "If the current end tag token is an
        // appropriate end tag token, then switch to the before attribute
        // name state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::Rawtext)
        }
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "If the current end tag token is an
        // appropriate end tag token, then switch to the self-closing start
        // tag state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::Rawtext)
        }
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "If the current end tag token is an
        // appropriate end tag token, then switch to the data state and emit
        // the current tag token. Otherwise, treat it as per the "anything
        // else" entry below."
        if w3c_is_appropriate_end_tag(t) {
            w3c_emit_tag_to_data(t)
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::Rawtext)
        }
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter (see w3c_end_tag_name_upper).
        w3c_end_tag_name_upper(t, w3c_cp(c))
    } else if w3c_is_lower_letter(c) {
        // Lowercase ASCII letter (see w3c_end_tag_name_lower).
        w3c_end_tag_name_lower(t, w3c_cp(c))
    } else {
        // Anything else: "Emit ... Reconsume in the RAWTEXT state."
        w3c_end_tag_name_anything_else(t, W3cState::Rawtext)
    }
}

/// 8.2.4.15 Script data less-than sign state.
pub open spec fn w3c_script_data_less_than_sign(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Set the temporary buffer to the empty string.
        // Switch to the script data end tag open state."
        (
            w3c_switch(W3cTokenizer { temporary_buffer: seq![], ..t }, W3cState::ScriptDataEndTagOpen),
            seq![],
        )
    } else if c == Some(0x0021u32) {
        // U+0021 EXCLAMATION MARK (!): "Switch to the script data escape
        // start state. Emit a U+003C LESS-THAN SIGN character token and a
        // U+0021 EXCLAMATION MARK character token."
        (
            w3c_switch(t, W3cState::ScriptDataEscapeStart),
            seq![Token::Character(0x003C), Token::Character(0x0021)],
        )
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the script data state."
        (w3c_reconsume(t, W3cState::ScriptData), seq![Token::Character(0x003C)])
    }
}

/// 8.2.4.16 Script data end tag open state.
pub open spec fn w3c_script_data_end_tag_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_letter(c) {
        // ASCII letter: "Create a new end tag token, set its tag name to
        // the empty string. Reconsume in the script data end tag name
        // state."
        (w3c_reconsume(w3c_create_tag(t, w3c_new_end_tag()), W3cState::ScriptDataEndTagName), seq![])
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token and a
        // U+002F SOLIDUS character token. Reconsume in the script data
        // state."
        (w3c_reconsume(t, W3cState::ScriptData), seq![Token::Character(0x003C), Token::Character(0x002F)])
    }
}

/// 8.2.4.17 Script data end tag name state.
pub open spec fn w3c_script_data_end_tag_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "If the current end tag token is an
        // appropriate end tag token, then switch to the before attribute
        // name state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::ScriptData)
        }
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "If the current end tag token is an
        // appropriate end tag token, then switch to the self-closing start
        // tag state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::ScriptData)
        }
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "If the current end tag token is an
        // appropriate end tag token, then switch to the data state and emit
        // the current tag token. Otherwise, treat it as per the "anything
        // else" entry below."
        if w3c_is_appropriate_end_tag(t) {
            w3c_emit_tag_to_data(t)
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::ScriptData)
        }
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter (see w3c_end_tag_name_upper).
        w3c_end_tag_name_upper(t, w3c_cp(c))
    } else if w3c_is_lower_letter(c) {
        // Lowercase ASCII letter (see w3c_end_tag_name_lower).
        w3c_end_tag_name_lower(t, w3c_cp(c))
    } else {
        // Anything else: "Emit ... Reconsume in the script data state."
        w3c_end_tag_name_anything_else(t, W3cState::ScriptData)
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.18 to 8.2.4.31: escaped script data.
// ---------------------------------------------------------------------------

/// 8.2.4.18 Script data escape start state.
pub open spec fn w3c_script_data_escape_start(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the script data escape start
        // dash state. Emit a U+002D HYPHEN-MINUS character token."
        (w3c_switch(t, W3cState::ScriptDataEscapeStartDash), seq![Token::Character(0x002D)])
    } else {
        // Anything else: "Reconsume in the script data state."
        (w3c_reconsume(t, W3cState::ScriptData), seq![])
    }
}

/// 8.2.4.19 Script data escape start dash state.
pub open spec fn w3c_script_data_escape_start_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the script data escaped dash
        // dash state. Emit a U+002D HYPHEN-MINUS character token."
        (w3c_switch(t, W3cState::ScriptDataEscapedDashDash), seq![Token::Character(0x002D)])
    } else {
        // Anything else: "Reconsume in the script data state."
        (w3c_reconsume(t, W3cState::ScriptData), seq![])
    }
}

/// 8.2.4.20 Script data escaped state.
pub open spec fn w3c_script_data_escaped(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the script data escaped dash
        // state. Emit a U+002D HYPHEN-MINUS character token."
        (w3c_switch(t, W3cState::ScriptDataEscapedDash), seq![Token::Character(0x002D)])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data escaped
        // less-than sign state."
        (w3c_switch(t, W3cState::ScriptDataEscapedLessThanSign), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit a U+FFFD REPLACEMENT CHARACTER
        // character token."
        (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.21 Script data escaped dash state.
pub open spec fn w3c_script_data_escaped_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the script data escaped dash
        // dash state. Emit a U+002D HYPHEN-MINUS character token."
        (w3c_switch(t, W3cState::ScriptDataEscapedDashDash), seq![Token::Character(0x002D)])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data escaped
        // less-than sign state."
        (w3c_switch(t, W3cState::ScriptDataEscapedLessThanSign), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Switch to the script data escaped
        // state. Emit a U+FFFD REPLACEMENT CHARACTER character token."
        (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Switch to the script data escaped state. Emit the
        // current input character as a character token."
        (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.22 Script data escaped dash dash state.
pub open spec fn w3c_script_data_escaped_dash_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Emit a U+002D HYPHEN-MINUS character
        // token."
        (w3c_switch(t, W3cState::ScriptDataEscapedDashDash), seq![Token::Character(0x002D)])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data escaped
        // less-than sign state."
        (w3c_switch(t, W3cState::ScriptDataEscapedLessThanSign), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the script data state.
        // Emit a U+003E GREATER-THAN SIGN character token."
        (w3c_switch(t, W3cState::ScriptData), seq![Token::Character(0x003E)])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Switch to the script data escaped
        // state. Emit a U+FFFD REPLACEMENT CHARACTER character token."
        (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Switch to the script data escaped state. Emit the
        // current input character as a character token."
        (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.23 Script data escaped less-than sign state.
pub open spec fn w3c_script_data_escaped_less_than_sign(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Set the temporary buffer to the empty string.
        // Switch to the script data escaped end tag open state."
        (
            w3c_switch(W3cTokenizer { temporary_buffer: seq![], ..t }, W3cState::ScriptDataEscapedEndTagOpen),
            seq![],
        )
    } else if w3c_is_letter(c) {
        // ASCII letter: "Set the temporary buffer to the empty string. Emit a
        // U+003C LESS-THAN SIGN character token. Reconsume in the script
        // data double escape start state."
        (
            w3c_reconsume(W3cTokenizer { temporary_buffer: seq![], ..t }, W3cState::ScriptDataDoubleEscapeStart),
            seq![Token::Character(0x003C)],
        )
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the script data escaped state."
        (w3c_reconsume(t, W3cState::ScriptDataEscaped), seq![Token::Character(0x003C)])
    }
}

/// 8.2.4.24 Script data escaped end tag open state.
pub open spec fn w3c_script_data_escaped_end_tag_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_letter(c) {
        // ASCII letter: "Create a new end tag token. Reconsume in the script
        // data escaped end tag name state." The tag name is not given; it
        // is the empty string here (see the header).
        (
            w3c_reconsume(w3c_create_tag(t, w3c_new_end_tag()), W3cState::ScriptDataEscapedEndTagName),
            seq![],
        )
    } else {
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token and a
        // U+002F SOLIDUS character token. Reconsume in the script data
        // escaped state."
        (
            w3c_reconsume(t, W3cState::ScriptDataEscaped),
            seq![Token::Character(0x003C), Token::Character(0x002F)],
        )
    }
}

/// 8.2.4.25 Script data escaped end tag name state.
pub open spec fn w3c_script_data_escaped_end_tag_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "If the current end tag token is an
        // appropriate end tag token, then switch to the before attribute
        // name state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::ScriptDataEscaped)
        }
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "If the current end tag token is an
        // appropriate end tag token, then switch to the self-closing start
        // tag state. Otherwise, treat it as per the "anything else" entry
        // below."
        if w3c_is_appropriate_end_tag(t) {
            (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::ScriptDataEscaped)
        }
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "If the current end tag token is an
        // appropriate end tag token, then switch to the data state and emit
        // the current tag token. Otherwise, treat it as per the "anything
        // else" entry below."
        if w3c_is_appropriate_end_tag(t) {
            w3c_emit_tag_to_data(t)
        } else {
            w3c_end_tag_name_anything_else(t, W3cState::ScriptDataEscaped)
        }
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter (see w3c_end_tag_name_upper).
        w3c_end_tag_name_upper(t, w3c_cp(c))
    } else if w3c_is_lower_letter(c) {
        // Lowercase ASCII letter (see w3c_end_tag_name_lower).
        w3c_end_tag_name_lower(t, w3c_cp(c))
    } else {
        // Anything else: "Emit ... Reconsume in the script data escaped
        // state."
        w3c_end_tag_name_anything_else(t, W3cState::ScriptDataEscaped)
    }
}

/// tab, LF, FF, SPACE, U+002F SOLIDUS (/) or U+003E GREATER-THAN SIGN (>):
/// the first entry of 8.2.4.26 and 8.2.4.31.
pub open spec fn w3c_is_double_escape_delimiter(c: Option<u32>) -> bool {
    w3c_is_tab_lf_ff_space(c) || c == Some(0x002Fu32) || c == Some(0x003Eu32)
}

/// 8.2.4.26 Script data double escape start state.
pub open spec fn w3c_script_data_double_escape_start(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_double_escape_delimiter(c) {
        // tab, LF, FF, SPACE, "/", ">": "If the temporary buffer is the
        // string "script", then switch to the script data double escaped
        // state. Otherwise, switch to the script data escaped state. Emit
        // the current input character as a character token."
        if w3c_same(t.temporary_buffer, w3c_word_script()) {
            (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(w3c_cp(c))])
        } else {
            (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(w3c_cp(c))])
        }
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter: "Append the lowercase version of the
        // current input character (add 0x0020 to the character's code
        // point) to the temporary buffer. Emit the current input character
        // as a character token."
        (
            w3c_switch(
                W3cTokenizer { temporary_buffer: t.temporary_buffer.push(w3c_lower(w3c_cp(c))), ..t },
                W3cState::ScriptDataDoubleEscapeStart,
            ),
            seq![Token::Character(w3c_cp(c))],
        )
    } else if w3c_is_lower_letter(c) {
        // Lowercase ASCII letter: "Append the current input character to the
        // temporary buffer. Emit the current input character as a character
        // token."
        (
            w3c_switch(
                W3cTokenizer { temporary_buffer: t.temporary_buffer.push(w3c_cp(c)), ..t },
                W3cState::ScriptDataDoubleEscapeStart,
            ),
            seq![Token::Character(w3c_cp(c))],
        )
    } else {
        // Anything else: "Reconsume in the script data escaped state."
        (w3c_reconsume(t, W3cState::ScriptDataEscaped), seq![])
    }
}

/// 8.2.4.27 Script data double escaped state.
pub open spec fn w3c_script_data_double_escaped(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the script data double escaped
        // dash state. Emit a U+002D HYPHEN-MINUS character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscapedDash), seq![Token::Character(0x002D)])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data double
        // escaped less-than sign state. Emit a U+003C LESS-THAN SIGN
        // character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscapedLessThanSign), seq![Token::Character(0x003C)])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Emit a U+FFFD REPLACEMENT CHARACTER
        // character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.28 Script data double escaped dash state.
pub open spec fn w3c_script_data_double_escaped_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the script data double escaped
        // dash dash state. Emit a U+002D HYPHEN-MINUS character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscapedDashDash), seq![Token::Character(0x002D)])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data double
        // escaped less-than sign state. Emit a U+003C LESS-THAN SIGN
        // character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscapedLessThanSign), seq![Token::Character(0x003C)])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Switch to the script data double
        // escaped state. Emit a U+FFFD REPLACEMENT CHARACTER character
        // token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Switch to the script data double escaped state.
        // Emit the current input character as a character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.29 Script data double escaped dash dash state.
pub open spec fn w3c_script_data_double_escaped_dash_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Emit a U+002D HYPHEN-MINUS character
        // token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscapedDashDash), seq![Token::Character(0x002D)])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Switch to the script data double
        // escaped less-than sign state. Emit a U+003C LESS-THAN SIGN
        // character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscapedLessThanSign), seq![Token::Character(0x003C)])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the script data state.
        // Emit a U+003E GREATER-THAN SIGN character token."
        (w3c_switch(t, W3cState::ScriptData), seq![Token::Character(0x003E)])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Switch to the script data double
        // escaped state. Emit a U+FFFD REPLACEMENT CHARACTER character
        // token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(0xFFFD)])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Switch to the script data double escaped state.
        // Emit the current input character as a character token."
        (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.30 Script data double escaped less-than sign state.
pub open spec fn w3c_script_data_double_escaped_less_than_sign(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Set the temporary buffer to the empty string.
        // Switch to the script data double escape end state. Emit a U+002F
        // SOLIDUS character token."
        (
            w3c_switch(W3cTokenizer { temporary_buffer: seq![], ..t }, W3cState::ScriptDataDoubleEscapeEnd),
            seq![Token::Character(0x002F)],
        )
    } else {
        // Anything else: "Reconsume in the script data double escaped
        // state."
        (w3c_reconsume(t, W3cState::ScriptDataDoubleEscaped), seq![])
    }
}

/// 8.2.4.31 Script data double escape end state.
pub open spec fn w3c_script_data_double_escape_end(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_double_escape_delimiter(c) {
        // tab, LF, FF, SPACE, "/", ">": "If the temporary buffer is the
        // string "script", then switch to the script data escaped state.
        // Otherwise, switch to the script data double escaped state. Emit
        // the current input character as a character token."
        if w3c_same(t.temporary_buffer, w3c_word_script()) {
            (w3c_switch(t, W3cState::ScriptDataEscaped), seq![Token::Character(w3c_cp(c))])
        } else {
            (w3c_switch(t, W3cState::ScriptDataDoubleEscaped), seq![Token::Character(w3c_cp(c))])
        }
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter: "Append the lowercase version of the
        // current input character (add 0x0020 to the character's code
        // point) to the temporary buffer. Emit the current input character
        // as a character token."
        (
            w3c_switch(
                W3cTokenizer { temporary_buffer: t.temporary_buffer.push(w3c_lower(w3c_cp(c))), ..t },
                W3cState::ScriptDataDoubleEscapeEnd,
            ),
            seq![Token::Character(w3c_cp(c))],
        )
    } else if w3c_is_lower_letter(c) {
        // Lowercase ASCII letter: "Append the current input character to the
        // temporary buffer. Emit the current input character as a character
        // token."
        (
            w3c_switch(
                W3cTokenizer { temporary_buffer: t.temporary_buffer.push(w3c_cp(c)), ..t },
                W3cState::ScriptDataDoubleEscapeEnd,
            ),
            seq![Token::Character(w3c_cp(c))],
        )
    } else {
        // Anything else: "Reconsume in the script data double escaped
        // state."
        (w3c_reconsume(t, W3cState::ScriptDataDoubleEscaped), seq![])
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.32 to 8.2.4.40: attributes.
// ---------------------------------------------------------------------------

/// 8.2.4.32 Before attribute name state.
pub open spec fn w3c_before_attribute_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
    } else if c == Some(0x002Fu32) || c == Some(0x003Eu32) || w3c_is_eof(c) {
        // U+002F SOLIDUS (/), U+003E GREATER-THAN SIGN (>), EOF: "Reconsume
        // in the after attribute name state."
        (w3c_reconsume(t, W3cState::AfterAttributeName), seq![])
    } else if c == Some(0x003Du32) {
        // U+003D EQUALS SIGN (=): "Parse error. Start a new attribute in the
        // current tag token. Set that attribute's name to the current input
        // character, and its value to the empty string. Switch to the
        // attribute name state."
        (w3c_switch(w3c_start_attribute(t, seq![0x003Du32]), W3cState::AttributeName), seq![])
    } else {
        // Anything else: "Start a new attribute in the current tag token.
        // Set that attribute's name and value to the empty string.
        // Reconsume in the attribute name state."
        (w3c_reconsume(w3c_start_attribute(t, seq![]), W3cState::AttributeName), seq![])
    }
}

/// 8.2.4.33 Attribute name state. Every transition out of the state first
/// applies the duplicate attribute rule ([`w3c_leave_attribute_name`]).
pub open spec fn w3c_attribute_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) || c == Some(0x002Fu32) || c == Some(0x003Eu32) || w3c_is_eof(c) {
        // tab, LF, FF, SPACE, "/", ">", EOF: "Reconsume in the after
        // attribute name state."
        (w3c_reconsume(w3c_leave_attribute_name(t), W3cState::AfterAttributeName), seq![])
    } else if c == Some(0x003Du32) {
        // U+003D EQUALS SIGN (=): "Switch to the before attribute value
        // state."
        (w3c_switch(w3c_leave_attribute_name(t), W3cState::BeforeAttributeValue), seq![])
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter: "Append the lowercase version of the
        // current input character (add 0x0020 to the character's code
        // point) to the current attribute's name."
        (w3c_switch(w3c_attribute_name_append(t, w3c_lower(w3c_cp(c))), W3cState::AttributeName), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current attribute's name."
        (w3c_switch(w3c_attribute_name_append(t, 0xFFFD), W3cState::AttributeName), seq![])
    } else {
        // U+0022 QUOTATION MARK ("), U+0027 APOSTROPHE ('), U+003C
        // LESS-THAN SIGN (<): "Parse error. Treat it as per the "anything
        // else" entry below." (folded into this entry)
        // Anything else: "Append the current input character to the current
        // attribute's name."
        (w3c_switch(w3c_attribute_name_append(t, w3c_cp(c)), W3cState::AttributeName), seq![])
    }
}

/// 8.2.4.34 After attribute name state.
pub open spec fn w3c_after_attribute_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::AfterAttributeName), seq![])
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Switch to the self-closing start tag state."
        (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
    } else if c == Some(0x003Du32) {
        // U+003D EQUALS SIGN (=): "Switch to the before attribute value
        // state."
        (w3c_switch(t, W3cState::BeforeAttributeValue), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current tag token."
        w3c_emit_tag_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Start a new attribute in the current tag token.
        // Set that attribute's name and value to the empty string.
        // Reconsume in the attribute name state."
        (w3c_reconsume(w3c_start_attribute(t, seq![]), W3cState::AttributeName), seq![])
    }
}

/// 8.2.4.35 Before attribute value state.
pub open spec fn w3c_before_attribute_value(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::BeforeAttributeValue), seq![])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Switch to the attribute value
        // (double-quoted) state."
        (w3c_switch(t, W3cState::AttributeValueDoubleQuoted), seq![])
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Switch to the attribute value
        // (single-quoted) state."
        (w3c_switch(t, W3cState::AttributeValueSingleQuoted), seq![])
    } else {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Treat it as per the
        // "anything else" entry below." (folded into this entry)
        // Anything else: "Reconsume in the attribute value (unquoted)
        // state."
        (w3c_reconsume(t, W3cState::AttributeValueUnquoted), seq![])
    }
}

/// 8.2.4.36 Attribute value (double-quoted) state.
pub open spec fn w3c_attribute_value_double_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Switch to the after attribute value
        // (quoted) state."
        (w3c_switch(t, W3cState::AfterAttributeValueQuoted), seq![])
    } else if c == Some(0x0026u32) {
        // U+0026 AMPERSAND (&): "Set the return state to the attribute value
        // (double-quoted) state. Switch to the character reference state."
        (
            W3cTokenizer {
                return_state: W3cReturnState::AttributeValueDoubleQuoted,
                ..w3c_switch(t, W3cState::CharacterReference)
            },
            seq![],
        )
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current attribute's value."
        (
            w3c_switch(w3c_attribute_value_append(t, seq![0xFFFDu32]), W3cState::AttributeValueDoubleQuoted),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Append the current input character to the current
        // attribute's value."
        (
            w3c_switch(w3c_attribute_value_append(t, seq![w3c_cp(c)]), W3cState::AttributeValueDoubleQuoted),
            seq![],
        )
    }
}

/// 8.2.4.37 Attribute value (single-quoted) state.
pub open spec fn w3c_attribute_value_single_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Switch to the after attribute value
        // (quoted) state."
        (w3c_switch(t, W3cState::AfterAttributeValueQuoted), seq![])
    } else if c == Some(0x0026u32) {
        // U+0026 AMPERSAND (&): "Set the return state to the attribute value
        // (single-quoted) state. Switch to the character reference state."
        (
            W3cTokenizer {
                return_state: W3cReturnState::AttributeValueSingleQuoted,
                ..w3c_switch(t, W3cState::CharacterReference)
            },
            seq![],
        )
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current attribute's value."
        (
            w3c_switch(w3c_attribute_value_append(t, seq![0xFFFDu32]), W3cState::AttributeValueSingleQuoted),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Append the current input character to the current
        // attribute's value."
        (
            w3c_switch(w3c_attribute_value_append(t, seq![w3c_cp(c)]), W3cState::AttributeValueSingleQuoted),
            seq![],
        )
    }
}

/// 8.2.4.38 Attribute value (unquoted) state.
pub open spec fn w3c_attribute_value_unquoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the before attribute name state."
        (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
    } else if c == Some(0x0026u32) {
        // U+0026 AMPERSAND (&): "Set the return state to the attribute value
        // (unquoted) state. Switch to the character reference state."
        (
            W3cTokenizer {
                return_state: W3cReturnState::AttributeValueUnquoted,
                ..w3c_switch(t, W3cState::CharacterReference)
            },
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current tag token."
        w3c_emit_tag_to_data(t)
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current attribute's value."
        (
            w3c_switch(w3c_attribute_value_append(t, seq![0xFFFDu32]), W3cState::AttributeValueUnquoted),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // U+0022 ("), U+0027 ('), U+003C (<), U+003D (=), U+0060 (`):
        // "Parse error. Treat it as per the "anything else" entry below."
        // (folded into this entry)
        // Anything else: "Append the current input character to the current
        // attribute's value."
        (
            w3c_switch(w3c_attribute_value_append(t, seq![w3c_cp(c)]), W3cState::AttributeValueUnquoted),
            seq![],
        )
    }
}

/// 8.2.4.39 After attribute value (quoted) state.
pub open spec fn w3c_after_attribute_value_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the before attribute name state."
        (w3c_switch(t, W3cState::BeforeAttributeName), seq![])
    } else if c == Some(0x002Fu32) {
        // U+002F SOLIDUS (/): "Switch to the self-closing start tag state."
        (w3c_switch(t, W3cState::SelfClosingStartTag), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current tag token."
        w3c_emit_tag_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the before attribute name
        // state."
        (w3c_reconsume(t, W3cState::BeforeAttributeName), seq![])
    }
}

/// 8.2.4.40 Self-closing start tag state.
pub open spec fn w3c_self_closing_start_tag(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Set the self-closing flag of the
        // current tag token. Switch to the data state. Emit the current tag
        // token."
        w3c_emit_tag_to_data(W3cTokenizer { current_token: w3c_tag_set_self_closing(t.current_token), ..t })
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the before attribute name
        // state."
        (w3c_reconsume(t, W3cState::BeforeAttributeName), seq![])
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.41 to 8.2.4.52: comments and markup declarations.
// ---------------------------------------------------------------------------

/// 8.2.4.41 Bogus comment state.
pub open spec fn w3c_bogus_comment(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // comment token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_eof(c) {
        // EOF: "Emit the comment. Emit an end-of-file token."
        w3c_emit_eof(t, seq![t.current_token])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Append a U+FFFD REPLACEMENT CHARACTER character to
        // the comment token's data."
        (w3c_switch(w3c_append_to_comment(t, seq![0xFFFDu32]), W3cState::BogusComment), seq![])
    } else {
        // Anything else: "Append the current input character to the comment
        // token's data."
        (w3c_switch(w3c_append_to_comment(t, seq![w3c_cp(c)]), W3cState::BogusComment), seq![])
    }
}

/// 8.2.4.42 Markup declaration open state. It does not begin by consuming
/// a character: it looks at the next characters.
pub open spec fn w3c_markup_declaration_open(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    if w3c_word_at(input, t.pos, seq![0x002Du32, 0x002Du32]) {
        // "If the next two characters are both U+002D HYPHEN-MINUS
        // characters (-), consume those two characters, create a comment
        // token whose data is the empty string, and switch to the comment
        // start state."
        (
            w3c_go(W3cTokenizer { current_token: w3c_new_comment(), ..t }, W3cState::CommentStart, t.pos + 2),
            seq![],
        )
    } else if w3c_word_at_ci(input, t.pos, w3c_word_doctype()) {
        // "Otherwise, if the next seven characters are an ASCII
        // case-insensitive match for the word "DOCTYPE", then consume those
        // characters and switch to the DOCTYPE state."
        (w3c_go(t, W3cState::Doctype, t.pos + 7), seq![])
    } else if t.adjusted_current_node_not_html && w3c_word_at(input, t.pos, w3c_word_cdata()) {
        // "Otherwise, if there is an adjusted current node and it is not an
        // element in the HTML namespace and the next seven characters are a
        // case-sensitive match for the string "[CDATA[" ..., then consume
        // those characters and switch to the CDATA section state."
        (w3c_go(t, W3cState::CdataSection, t.pos + 7), seq![])
    } else {
        // "Otherwise, this is a parse error. Create a comment token whose
        // data is the empty string. Switch to the bogus comment state
        // (don't consume anything in the current state)."
        (
            w3c_go(W3cTokenizer { current_token: w3c_new_comment(), ..t }, W3cState::BogusComment, t.pos),
            seq![],
        )
    }
}

/// 8.2.4.43 Comment start state.
pub open spec fn w3c_comment_start(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the comment start dash state."
        (w3c_switch(t, W3cState::CommentStartDash), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Switch to the data
        // state. Emit the comment token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else {
        // Anything else: "Reconsume in the comment state."
        (w3c_reconsume(t, W3cState::Comment), seq![])
    }
}

/// 8.2.4.44 Comment start dash state.
pub open spec fn w3c_comment_start_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the comment end state"
        (w3c_switch(t, W3cState::CommentEnd), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Switch to the data
        // state. Emit the comment token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit the comment token. Emit an end-of-file
        // token."
        w3c_emit_eof(t, seq![t.current_token])
    } else {
        // Anything else: "Append a U+002D HYPHEN-MINUS character (-) to the
        // comment token's data. Reconsume in the comment state."
        (w3c_reconsume(w3c_append_to_comment(t, seq![0x002Du32]), W3cState::Comment), seq![])
    }
}

/// 8.2.4.45 Comment state.
pub open spec fn w3c_comment(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Append the current input character to
        // the comment token's data. Switch to the comment less-than sign
        // state."
        (w3c_switch(w3c_append_to_comment(t, seq![0x003Cu32]), W3cState::CommentLessThanSign), seq![])
    } else if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the comment end dash state"
        (w3c_switch(t, W3cState::CommentEndDash), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the comment token's data."
        (w3c_switch(w3c_append_to_comment(t, seq![0xFFFDu32]), W3cState::Comment), seq![])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit the comment token. Emit an end-of-file
        // token."
        w3c_emit_eof(t, seq![t.current_token])
    } else {
        // Anything else: "Append the current input character to the comment
        // token's data."
        (w3c_switch(w3c_append_to_comment(t, seq![w3c_cp(c)]), W3cState::Comment), seq![])
    }
}

/// 8.2.4.46 Comment less-than sign state.
pub open spec fn w3c_comment_less_than_sign(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0021u32) {
        // U+0021 EXCLAMATION MARK (!): "Append the current input character
        // to the comment token's data. Switch to the comment less-than sign
        // bang state."
        (w3c_switch(w3c_append_to_comment(t, seq![0x0021u32]), W3cState::CommentLessThanSignBang), seq![])
    } else if c == Some(0x003Cu32) {
        // U+003C LESS-THAN SIGN (<): "Append the current input character to
        // the comment token's data."
        (w3c_switch(w3c_append_to_comment(t, seq![0x003Cu32]), W3cState::CommentLessThanSign), seq![])
    } else {
        // Anything else: "Reconsume in the comment state."
        (w3c_reconsume(t, W3cState::Comment), seq![])
    }
}

/// 8.2.4.47 Comment less-than sign bang state.
pub open spec fn w3c_comment_less_than_sign_bang(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the comment less-than sign bang
        // dash state."
        (w3c_switch(t, W3cState::CommentLessThanSignBangDash), seq![])
    } else {
        // Anything else: "Reconsume in the comment state."
        (w3c_reconsume(t, W3cState::Comment), seq![])
    }
}

/// 8.2.4.48 Comment less-than sign bang dash state.
pub open spec fn w3c_comment_less_than_sign_bang_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the comment less-than sign bang
        // dash dash state."
        (w3c_switch(t, W3cState::CommentLessThanSignBangDashDash), seq![])
    } else {
        // Anything else: "Reconsume in the comment end dash state."
        (w3c_reconsume(t, W3cState::CommentEndDash), seq![])
    }
}

/// 8.2.4.49 Comment less-than sign bang dash dash state.
pub open spec fn w3c_comment_less_than_sign_bang_dash_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Eu32) || w3c_is_eof(c) {
        // U+003E GREATER-THAN SIGN (>), EOF: "Reconsume in the comment end
        // state."
        (w3c_reconsume(t, W3cState::CommentEnd), seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the comment end state."
        (w3c_reconsume(t, W3cState::CommentEnd), seq![])
    }
}

/// 8.2.4.50 Comment end dash state.
pub open spec fn w3c_comment_end_dash(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Switch to the comment end state"
        (w3c_switch(t, W3cState::CommentEnd), seq![])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit the comment token. Emit an end-of-file
        // token."
        w3c_emit_eof(t, seq![t.current_token])
    } else {
        // Anything else: "Append a U+002D HYPHEN-MINUS character (-) to the
        // comment token's data. Reconsume in the comment state."
        (w3c_reconsume(w3c_append_to_comment(t, seq![0x002Du32]), W3cState::Comment), seq![])
    }
}

/// 8.2.4.51 Comment end state.
pub open spec fn w3c_comment_end(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // comment token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if c == Some(0x0021u32) {
        // U+0021 EXCLAMATION MARK (!): "Switch to the comment end bang
        // state."
        (w3c_switch(t, W3cState::CommentEndBang), seq![])
    } else if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Append a U+002D HYPHEN-MINUS character
        // (-) to the comment token's data."
        (w3c_switch(w3c_append_to_comment(t, seq![0x002Du32]), W3cState::CommentEnd), seq![])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit the comment token. Emit an end-of-file
        // token."
        w3c_emit_eof(t, seq![t.current_token])
    } else {
        // Anything else: "Append two U+002D HYPHEN-MINUS characters (-) to
        // the comment token's data. Reconsume in the comment state."
        (w3c_reconsume(w3c_append_to_comment(t, seq![0x002Du32, 0x002Du32]), W3cState::Comment), seq![])
    }
}

/// 8.2.4.52 Comment end bang state.
pub open spec fn w3c_comment_end_bang(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x002Du32) {
        // U+002D HYPHEN-MINUS (-): "Append two U+002D HYPHEN-MINUS characters
        // (-) and a U+0021 EXCLAMATION MARK character (!) to the comment
        // token's data. Switch to the comment end dash state."
        (
            w3c_switch(
                w3c_append_to_comment(t, seq![0x002Du32, 0x002Du32, 0x0021u32]),
                W3cState::CommentEndDash,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Switch to the data
        // state. Emit the comment token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit the comment token. Emit an end-of-file
        // token."
        w3c_emit_eof(t, seq![t.current_token])
    } else {
        // Anything else: "Append two U+002D HYPHEN-MINUS characters (-) and a
        // U+0021 EXCLAMATION MARK character (!) to the comment token's data.
        // Reconsume in the comment state."
        (
            w3c_reconsume(w3c_append_to_comment(t, seq![0x002Du32, 0x002Du32, 0x0021u32]), W3cState::Comment),
            seq![],
        )
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.53 to 8.2.4.68: DOCTYPE.
// ---------------------------------------------------------------------------

/// 8.2.4.53 DOCTYPE state.
pub open spec fn w3c_doctype(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the before DOCTYPE name state."
        (w3c_switch(t, W3cState::BeforeDoctypeName), seq![])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Create a new DOCTYPE token. Set its force-quirks
        // flag to on. Emit the token. Emit an end-of-file token."
        let tok = w3c_doctype_force_quirks(w3c_new_doctype());
        w3c_emit_eof(W3cTokenizer { current_token: tok, ..t }, seq![tok])
    } else {
        // Anything else: "Parse error. Reconsume in the before DOCTYPE name
        // state."
        (w3c_reconsume(t, W3cState::BeforeDoctypeName), seq![])
    }
}

/// 8.2.4.54 Before DOCTYPE name state.
pub open spec fn w3c_before_doctype_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::BeforeDoctypeName), seq![])
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter: "Create a new DOCTYPE token. Set the
        // token's name to the lowercase version of the current input
        // character (add 0x0020 to the character's code point). Switch to
        // the DOCTYPE name state."
        (
            w3c_switch(
                W3cTokenizer {
                    current_token: w3c_doctype_set_name(w3c_new_doctype(), seq![w3c_lower(w3c_cp(c))]),
                    ..t
                },
                W3cState::DoctypeName,
            ),
            seq![],
        )
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Create a new DOCTYPE token. Set the
        // token's name to a U+FFFD REPLACEMENT CHARACTER character. Switch
        // to the DOCTYPE name state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_set_name(w3c_new_doctype(), seq![0xFFFDu32]), ..t },
                W3cState::DoctypeName,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Create a new DOCTYPE
        // token. Set its force-quirks flag to on. Switch to the data state.
        // Emit the token."
        let tok = w3c_doctype_force_quirks(w3c_new_doctype());
        (w3c_switch(W3cTokenizer { current_token: tok, ..t }, W3cState::Data), seq![tok])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Create a new DOCTYPE token. Set its force-quirks
        // flag to on. Emit the token. Emit an end-of-file token."
        let tok = w3c_doctype_force_quirks(w3c_new_doctype());
        w3c_emit_eof(W3cTokenizer { current_token: tok, ..t }, seq![tok])
    } else {
        // Anything else: "Create a new DOCTYPE token. Set the token's name to
        // the current input character. Switch to the DOCTYPE name state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_set_name(w3c_new_doctype(), seq![w3c_cp(c)]), ..t },
                W3cState::DoctypeName,
            ),
            seq![],
        )
    }
}

/// 8.2.4.55 DOCTYPE name state.
pub open spec fn w3c_doctype_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the after DOCTYPE name state."
        (w3c_switch(t, W3cState::AfterDoctypeName), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current DOCTYPE token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_upper_letter(c) {
        // Uppercase ASCII letter: "Append the lowercase version of the
        // current input character (add 0x0020 to the character's code
        // point) to the current DOCTYPE token's name."
        (
            w3c_switch(
                W3cTokenizer {
                    current_token: w3c_doctype_append_name(t.current_token, w3c_lower(w3c_cp(c))),
                    ..t
                },
                W3cState::DoctypeName,
            ),
            seq![],
        )
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current DOCTYPE token's name."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_name(t.current_token, 0xFFFD), ..t },
                W3cState::DoctypeName,
            ),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Append the current input character to the current
        // DOCTYPE token's name."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_name(t.current_token, w3c_cp(c)), ..t },
                W3cState::DoctypeName,
            ),
            seq![],
        )
    }
}

/// 8.2.4.56 After DOCTYPE name state.
pub open spec fn w3c_after_doctype_name(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::AfterDoctypeName), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current DOCTYPE token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: the current input character is input[pos].
        if w3c_word_at_ci(input, t.pos, w3c_word_public()) {
            // "If the six characters starting from the current input
            // character are an ASCII case-insensitive match for the word
            // "PUBLIC", then consume those characters and switch to the after
            // DOCTYPE public keyword state."
            (w3c_go(t, W3cState::AfterDoctypePublicKeyword, t.pos + 6), seq![])
        } else if w3c_word_at_ci(input, t.pos, w3c_word_system()) {
            // "Otherwise, if the six characters starting from the current
            // input character are an ASCII case-insensitive match for the
            // word "SYSTEM", then consume those characters and switch to the
            // after DOCTYPE system keyword state."
            (w3c_go(t, W3cState::AfterDoctypeSystemKeyword, t.pos + 6), seq![])
        } else {
            // "Otherwise, this is a parse error. Set the DOCTYPE token's
            // force-quirks flag to on. Switch to the bogus DOCTYPE state."
            w3c_doctype_quirks_to_bogus(t)
        }
    }
}

/// 8.2.4.57 After DOCTYPE public keyword state.
pub open spec fn w3c_after_doctype_public_keyword(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the before DOCTYPE public
        // identifier state."
        (w3c_switch(t, W3cState::BeforeDoctypePublicIdentifier), seq![])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Parse error. Set the DOCTYPE token's
        // public identifier to the empty string (not missing), then switch
        // to the DOCTYPE public identifier (double-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_public(t.current_token), ..t },
                W3cState::DoctypePublicIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Parse error. Set the DOCTYPE token's
        // public identifier to the empty string (not missing), then switch
        // to the DOCTYPE public identifier (single-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_public(t.current_token), ..t },
                W3cState::DoctypePublicIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Set the DOCTYPE token's force-quirks
        // flag to on. Switch to the bogus DOCTYPE state."
        w3c_doctype_quirks_to_bogus(t)
    }
}

/// 8.2.4.58 Before DOCTYPE public identifier state.
pub open spec fn w3c_before_doctype_public_identifier(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::BeforeDoctypePublicIdentifier), seq![])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Set the DOCTYPE token's public
        // identifier to the empty string (not missing), then switch to the
        // DOCTYPE public identifier (double-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_public(t.current_token), ..t },
                W3cState::DoctypePublicIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Set the DOCTYPE token's public identifier
        // to the empty string (not missing), then switch to the DOCTYPE
        // public identifier (single-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_public(t.current_token), ..t },
                W3cState::DoctypePublicIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Set the DOCTYPE token's force-quirks
        // flag to on. Switch to the bogus DOCTYPE state."
        w3c_doctype_quirks_to_bogus(t)
    }
}

/// 8.2.4.59 DOCTYPE public identifier (double-quoted) state.
pub open spec fn w3c_doctype_public_identifier_double_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Switch to the after DOCTYPE public
        // identifier state."
        (w3c_switch(t, W3cState::AfterDoctypePublicIdentifier), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current DOCTYPE token's public identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_public(t.current_token, 0xFFFD), ..t },
                W3cState::DoctypePublicIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Append the current input character to the current
        // DOCTYPE token's public identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_public(t.current_token, w3c_cp(c)), ..t },
                W3cState::DoctypePublicIdentifierDoubleQuoted,
            ),
            seq![],
        )
    }
}

/// 8.2.4.60 DOCTYPE public identifier (single-quoted) state.
pub open spec fn w3c_doctype_public_identifier_single_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Switch to the after DOCTYPE public
        // identifier state."
        (w3c_switch(t, W3cState::AfterDoctypePublicIdentifier), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current DOCTYPE token's public identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_public(t.current_token, 0xFFFD), ..t },
                W3cState::DoctypePublicIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Append the current input character to the current
        // DOCTYPE token's public identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_public(t.current_token, w3c_cp(c)), ..t },
                W3cState::DoctypePublicIdentifierSingleQuoted,
            ),
            seq![],
        )
    }
}

/// 8.2.4.61 After DOCTYPE public identifier state.
pub open spec fn w3c_after_doctype_public_identifier(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the between DOCTYPE public and
        // system identifiers state."
        (w3c_switch(t, W3cState::BetweenDoctypePublicAndSystemIdentifiers), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current DOCTYPE token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Parse error. Set the DOCTYPE token's
        // system identifier to the empty string (not missing), then switch
        // to the DOCTYPE system identifier (double-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Parse error. Set the DOCTYPE token's
        // system identifier to the empty string (not missing), then switch
        // to the DOCTYPE system identifier (single-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Set the DOCTYPE token's force-quirks
        // flag to on. Switch to the bogus DOCTYPE state."
        w3c_doctype_quirks_to_bogus(t)
    }
}

/// 8.2.4.62 Between DOCTYPE public and system identifiers state.
pub open spec fn w3c_between_doctype_public_and_system_identifiers(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::BetweenDoctypePublicAndSystemIdentifiers), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current DOCTYPE token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Set the DOCTYPE token's system
        // identifier to the empty string (not missing), then switch to the
        // DOCTYPE system identifier (double-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Set the DOCTYPE token's system identifier
        // to the empty string (not missing), then switch to the DOCTYPE
        // system identifier (single-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Set the DOCTYPE token's force-quirks
        // flag to on. Switch to the bogus DOCTYPE state."
        w3c_doctype_quirks_to_bogus(t)
    }
}

/// 8.2.4.63 After DOCTYPE system keyword state.
pub open spec fn w3c_after_doctype_system_keyword(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Switch to the before DOCTYPE system
        // identifier state."
        (w3c_switch(t, W3cState::BeforeDoctypeSystemIdentifier), seq![])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Parse error. Set the DOCTYPE token's
        // system identifier to the empty string (not missing), then switch
        // to the DOCTYPE system identifier (double-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Parse error. Set the DOCTYPE token's
        // system identifier to the empty string (not missing), then switch
        // to the DOCTYPE system identifier (single-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Set the DOCTYPE token's force-quirks
        // flag to on. Switch to the bogus DOCTYPE state."
        w3c_doctype_quirks_to_bogus(t)
    }
}

/// 8.2.4.64 Before DOCTYPE system identifier state.
pub open spec fn w3c_before_doctype_system_identifier(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::BeforeDoctypeSystemIdentifier), seq![])
    } else if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Set the DOCTYPE token's system
        // identifier to the empty string (not missing), then switch to the
        // DOCTYPE system identifier (double-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Set the DOCTYPE token's system identifier
        // to the empty string (not missing), then switch to the DOCTYPE
        // system identifier (single-quoted) state."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_empty_system(t.current_token), ..t },
                W3cState::DoctypeSystemIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Set the DOCTYPE token's force-quirks
        // flag to on. Switch to the bogus DOCTYPE state."
        w3c_doctype_quirks_to_bogus(t)
    }
}

/// 8.2.4.65 DOCTYPE system identifier (double-quoted) state.
pub open spec fn w3c_doctype_system_identifier_double_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0022u32) {
        // U+0022 QUOTATION MARK ("): "Switch to the after DOCTYPE system
        // identifier state."
        (w3c_switch(t, W3cState::AfterDoctypeSystemIdentifier), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current DOCTYPE token's system identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_system(t.current_token, 0xFFFD), ..t },
                W3cState::DoctypeSystemIdentifierDoubleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Append the current input character to the current
        // DOCTYPE token's system identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_system(t.current_token, w3c_cp(c)), ..t },
                W3cState::DoctypeSystemIdentifierDoubleQuoted,
            ),
            seq![],
        )
    }
}

/// 8.2.4.66 DOCTYPE system identifier (single-quoted) state.
pub open spec fn w3c_doctype_system_identifier_single_quoted(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0027u32) {
        // U+0027 APOSTROPHE ('): "Switch to the after DOCTYPE system
        // identifier state."
        (w3c_switch(t, W3cState::AfterDoctypeSystemIdentifier), seq![])
    } else if c == Some(0x0000u32) {
        // U+0000 NULL: "Parse error. Append a U+FFFD REPLACEMENT CHARACTER
        // character to the current DOCTYPE token's system identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_system(t.current_token, 0xFFFD), ..t },
                W3cState::DoctypeSystemIdentifierSingleQuoted,
            ),
            seq![],
        )
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Parse error. Set the DOCTYPE
        // token's force-quirks flag to on. Switch to the data state. Emit
        // that DOCTYPE token."
        w3c_doctype_quirks_to_data(t)
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Append the current input character to the current
        // DOCTYPE token's system identifier."
        (
            w3c_switch(
                W3cTokenizer { current_token: w3c_doctype_append_system(t.current_token, w3c_cp(c)), ..t },
                W3cState::DoctypeSystemIdentifierSingleQuoted,
            ),
            seq![],
        )
    }
}

/// 8.2.4.67 After DOCTYPE system identifier state.
pub open spec fn w3c_after_doctype_system_identifier(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) {
        // tab, LF, FF, SPACE: "Ignore the character."
        (w3c_switch(t, W3cState::AfterDoctypeSystemIdentifier), seq![])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // current DOCTYPE token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Set the DOCTYPE token's force-quirks flag to on.
        // Emit that DOCTYPE token. Emit an end-of-file token."
        w3c_doctype_eof(t)
    } else {
        // Anything else: "Parse error. Switch to the bogus DOCTYPE state.
        // (This does not set the DOCTYPE token's force-quirks flag to on.)"
        (w3c_switch(t, W3cState::BogusDoctype), seq![])
    }
}

/// 8.2.4.68 Bogus DOCTYPE state.
pub open spec fn w3c_bogus_doctype(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit the
        // DOCTYPE token."
        (w3c_switch(t, W3cState::Data), seq![t.current_token])
    } else if w3c_is_eof(c) {
        // EOF: "Emit the DOCTYPE token. Emit an end-of-file token."
        w3c_emit_eof(t, seq![t.current_token])
    } else {
        // Anything else: "Ignore the character."
        (w3c_switch(t, W3cState::BogusDoctype), seq![])
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.69 to 8.2.4.71: CDATA sections.
// ---------------------------------------------------------------------------

/// 8.2.4.69 CDATA section state.
pub open spec fn w3c_cdata_section(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x005Du32) {
        // U+005D RIGHT SQUARE BRACKET (]): "Switch to the CDATA section
        // bracket state."
        (w3c_switch(t, W3cState::CdataSectionBracket), seq![])
    } else if w3c_is_eof(c) {
        // EOF: "Parse error. Emit an end-of-file token."
        w3c_emit_eof(t, seq![])
    } else {
        // Anything else: "Emit the current input character as a character
        // token." (U+0000 included: "U+0000 NULL characters are handled in
        // the tree construction stage".)
        (w3c_switch(t, W3cState::CdataSection), seq![Token::Character(w3c_cp(c))])
    }
}

/// 8.2.4.70 CDATA section bracket state.
pub open spec fn w3c_cdata_section_bracket(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x005Du32) {
        // U+005D RIGHT SQUARE BRACKET (]): "Switch to the CDATA section end
        // state."
        (w3c_switch(t, W3cState::CdataSectionEnd), seq![])
    } else {
        // Anything else: "Emit a U+005D RIGHT SQUARE BRACKET character
        // token. Reconsume in the CDATA section state"
        (w3c_reconsume(t, W3cState::CdataSection), seq![Token::Character(0x005D)])
    }
}

/// 8.2.4.71 CDATA section end state.
pub open spec fn w3c_cdata_section_end(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x005Du32) {
        // U+005D RIGHT SQUARE BRACKET (]): "Emit a U+005D RIGHT SQUARE
        // BRACKET character token."
        (w3c_switch(t, W3cState::CdataSectionEnd), seq![Token::Character(0x005D)])
    } else if c == Some(0x003Eu32) {
        // U+003E GREATER-THAN SIGN (>): "Switch to the data state."
        (w3c_switch(t, W3cState::Data), seq![])
    } else {
        // Anything else: "Emit two U+005D RIGHT SQUARE BRACKET character
        // tokens. Reconsume in the CDATA section state"
        (w3c_reconsume(t, W3cState::CdataSection), seq![Token::Character(0x005D), Token::Character(0x005D)])
    }
}

// ---------------------------------------------------------------------------
// 8.2.4.72 to 8.2.4.79: character references.
// ---------------------------------------------------------------------------

/// The row of the §8.5 named character references table, among rows `i`
/// onwards and `best` (the longest so far), whose name is the longest one
/// matching the input from `pos` case-sensitively; on equal lengths the
/// earlier row is kept (names are unique, so this never decides).
pub open spec fn w3c_longest_match_from(input: Seq<u32>, pos: nat, i: nat, best: Option<nat>) -> Option<nat>
    decreases crate::charref::spec::entity_count() - i,
{
    if i >= crate::charref::spec::entity_count() {
        best
    } else {
        let name = crate::charref::spec::entity_name(i as int);
        let longer = match best {
            Some(b) => name.len() > crate::charref::spec::entity_name(b as int).len(),
            None => true,
        };
        if w3c_word_at(input, pos, name) && longer {
            w3c_longest_match_from(input, pos, i + 1, Some(i))
        } else {
            w3c_longest_match_from(input, pos, i + 1, best)
        }
    }
}

/// "Consume the maximum number of characters possible, with the consumed
/// characters matching one of the identifiers in the first column of the
/// §8.5 Named character references table (in a case-sensitive manner)":
/// the row matched, starting at `pos`, or `None` if "no match can be made".
pub open spec fn w3c_longest_match(input: Seq<u32>, pos: nat) -> Option<nat> {
    w3c_longest_match_from(input, pos, 0, None)
}

/// 8.2.4.72's "Anything else" entry: a named character reference. The match
/// starts with the current input character, at `t.pos` (see the header).
pub open spec fn w3c_named_character_reference(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    match w3c_longest_match(input, t.pos) {
        None => {
            // "If no match can be made and the temporary buffer consists of
            // a U+0026 AMPERSAND character (&) followed by a sequence of one
            // or more alphanumeric ASCII characters and a U+003B SEMICOLON
            // character (;), then this is a parse error." (not modelled)
            // "If no match can be made, switch to the character reference
            // end state." Nothing was consumed.
            (w3c_go(t, W3cState::CharacterReferenceEnd, t.pos), seq![])
        },
        Some(i) => {
            let name = crate::charref::spec::entity_name(i as int);
            // The match consumed `name`; "Append each character to the
            // temporary buffer when it's consumed."
            let after = t.pos + name.len();
            let t1 = W3cTokenizer { temporary_buffer: t.temporary_buffer + name, ..t };
            let last_is_semicolon = name.len() > 0 && name[name.len() - 1] == 0x003Bu32;
            let next = w3c_next(input, after);
            if w3c_return_state_is_attribute(t.return_state) && !last_is_semicolon && (next == Some(
                0x003Du32,
            ) || w3c_is_alphanumeric(next)) {
                // "If the character reference was consumed as part of an
                // attribute (...), and the last character matched is not a
                // U+003B SEMICOLON character (;), and the next input
                // character is either a U+003D EQUALS SIGN character (=) or an
                // alphanumeric ASCII character, then, for historical reasons,
                // switch to the character reference end state."
                (w3c_go(t1, W3cState::CharacterReferenceEnd, after), seq![])
            } else {
                // "If the last character matched is not a U+003B SEMICOLON
                // character (;), this is a parse error." (not modelled)
                // "Set the temporary buffer to the empty string. Append one or
                // two characters corresponding to the character reference
                // name (as given by the second column of the §8.5 Named
                // character references table) to the temporary buffer."
                // "Switch to the character reference end state."
                (
                    w3c_go(
                        W3cTokenizer {
                            temporary_buffer: crate::charref::spec::entity_code_points(i as int),
                            ..t1
                        },
                        W3cState::CharacterReferenceEnd,
                        after,
                    ),
                    seq![],
                )
            }
        },
    }
}

/// 8.2.4.72 Character reference state.
pub open spec fn w3c_character_reference(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Set the temporary buffer to the empty string. Append a U+0026
    // AMPERSAND (&) character to the temporary buffer."
    let t = W3cTokenizer { temporary_buffer: seq![0x0026u32], ..t };
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_tab_lf_ff_space(c) || c == Some(0x003Cu32) || c == Some(0x0026u32) || w3c_is_eof(c) {
        // tab, LF, FF, SPACE, U+003C LESS-THAN SIGN, U+0026 AMPERSAND, EOF:
        // "Reconsume in the character reference end state."
        (w3c_reconsume(t, W3cState::CharacterReferenceEnd), seq![])
    } else if c == Some(0x0023u32) {
        // U+0023 NUMBER SIGN (#): "Append the current input character to
        // the temporary buffer. Switch to the numeric character reference
        // state."
        (
            w3c_switch(
                W3cTokenizer { temporary_buffer: t.temporary_buffer.push(0x0023), ..t },
                W3cState::NumericCharacterReference,
            ),
            seq![],
        )
    } else {
        // Anything else: see w3c_named_character_reference.
        w3c_named_character_reference(input, t)
    }
}

/// 8.2.4.73 Numeric character reference state.
pub open spec fn w3c_numeric_character_reference(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Set the character reference code to zero (0)."
    let t = W3cTokenizer { character_reference_code: 0, ..t };
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if c == Some(0x0078u32) || c == Some(0x0058u32) {
        // U+0078 LATIN SMALL LETTER X, U+0058 LATIN CAPITAL LETTER X:
        // "Append the current input character to the temporary buffer.
        // Switch to the hexadecimal character reference start state."
        (
            w3c_switch(
                W3cTokenizer { temporary_buffer: t.temporary_buffer.push(w3c_cp(c)), ..t },
                W3cState::HexadecimalCharacterReferenceStart,
            ),
            seq![],
        )
    } else {
        // Anything else: "Reconsume in the decimal character reference start
        // state."
        (w3c_reconsume(t, W3cState::DecimalCharacterReferenceStart), seq![])
    }
}

/// 8.2.4.74 Hexadecimal character reference start state.
pub open spec fn w3c_hexadecimal_character_reference_start(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_hex_digit(c) {
        // ASCII hex digit: "Reconsume in the hexadecimal character reference
        // state."
        (w3c_reconsume(t, W3cState::HexadecimalCharacterReference), seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the character reference
        // end state."
        (w3c_reconsume(t, W3cState::CharacterReferenceEnd), seq![])
    }
}

/// 8.2.4.75 Decimal character reference start state.
pub open spec fn w3c_decimal_character_reference_start(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_digit(c) {
        // ASCII digit: "Reconsume in the decimal character reference state."
        (w3c_reconsume(t, W3cState::DecimalCharacterReference), seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the character reference
        // end state."
        (w3c_reconsume(t, W3cState::CharacterReferenceEnd), seq![])
    }
}

/// Multiply the character reference code by `base` and add `digit`.
pub open spec fn w3c_code_add_digit(t: W3cTokenizer, base: nat, digit: int) -> W3cTokenizer {
    W3cTokenizer { character_reference_code: (t.character_reference_code * base + digit) as nat, ..t }
}

/// 8.2.4.76 Hexadecimal character reference state.
pub open spec fn w3c_hexadecimal_character_reference(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_digit(c) {
        // ASCII digit: "Multiply the character reference code by 16. Add a
        // numeric version of the current input character (subtract 0x0030
        // from the character's code point) to the character reference
        // code."
        (
            w3c_switch(w3c_code_add_digit(t, 16, w3c_cp(c) - 0x0030), W3cState::HexadecimalCharacterReference),
            seq![],
        )
    } else if w3c_is_upper_hex_letter(c) {
        // Uppercase ASCII hex digit: "Multiply the character reference code
        // by 16. Add a numeric version of the current input character as a
        // hexademical digit (subtract 0x0037 from the character's code
        // point) to the character reference code."
        (
            w3c_switch(w3c_code_add_digit(t, 16, w3c_cp(c) - 0x0037), W3cState::HexadecimalCharacterReference),
            seq![],
        )
    } else if w3c_is_lower_hex_letter(c) {
        // Lowercase ASCII hex digit: "Multiply the character reference code
        // by 16. Add a numeric version of the current input character as a
        // hexademical digit (subtract 0x0057 from the character's code
        // point) to the character reference code."
        (
            w3c_switch(w3c_code_add_digit(t, 16, w3c_cp(c) - 0x0057), W3cState::HexadecimalCharacterReference),
            seq![],
        )
    } else if c == Some(0x003Bu32) {
        // U+003B SEMICOLON character (;): "Switch to the numeric character
        // reference end state."
        (w3c_switch(t, W3cState::NumericCharacterReferenceEnd), seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the numeric character
        // reference end state."
        (w3c_reconsume(t, W3cState::NumericCharacterReferenceEnd), seq![])
    }
}

/// 8.2.4.77 Decimal character reference state.
pub open spec fn w3c_decimal_character_reference(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character:"
    let c = w3c_next(input, t.pos);
    if w3c_is_digit(c) {
        // ASCII digit: "Multiply the character reference code by 16. Add a
        // numeric version of the current input character (subtract 0x0030
        // from the character's code point) to the character reference
        // code."
        // W3C text, read literally: 16, not 10 (see the header).
        (
            w3c_switch(w3c_code_add_digit(t, 16, w3c_cp(c) - 0x0030), W3cState::DecimalCharacterReference),
            seq![],
        )
    } else if c == Some(0x003Bu32) {
        // U+003B SEMICOLON character (;): "Switch to the numeric character
        // reference end state."
        (w3c_switch(t, W3cState::NumericCharacterReferenceEnd), seq![])
    } else {
        // Anything else: "Parse error. Reconsume in the numeric character
        // reference end state."
        (w3c_reconsume(t, W3cState::NumericCharacterReferenceEnd), seq![])
    }
}

/// The table of 8.2.4.78: the number in the second column of the row whose
/// first column is `n`, if there is one.
pub open spec fn w3c_numeric_replacement(n: nat) -> Option<nat> {
    if n == 0x00 {
        Some(0xFFFD)  // REPLACEMENT CHARACTER
    } else if n == 0x80 {
        Some(0x20AC)  // EURO SIGN
    } else if n == 0x82 {
        Some(0x201A)  // SINGLE LOW-9 QUOTATION MARK
    } else if n == 0x83 {
        Some(0x0192)  // LATIN SMALL LETTER F WITH HOOK
    } else if n == 0x84 {
        Some(0x201E)  // DOUBLE LOW-9 QUOTATION MARK
    } else if n == 0x85 {
        Some(0x2026)  // HORIZONTAL ELLIPSIS
    } else if n == 0x86 {
        Some(0x2020)  // DAGGER
    } else if n == 0x87 {
        Some(0x2021)  // DOUBLE DAGGER
    } else if n == 0x88 {
        Some(0x02C6)  // MODIFIER LETTER CIRCUMFLEX ACCENT
    } else if n == 0x89 {
        Some(0x2030)  // PER MILLE SIGN
    } else if n == 0x8A {
        Some(0x0160)  // LATIN CAPITAL LETTER S WITH CARON
    } else if n == 0x8B {
        Some(0x2039)  // SINGLE LEFT-POINTING ANGLE QUOTATION MARK
    } else if n == 0x8C {
        Some(0x0152)  // LATIN CAPITAL LIGATURE OE
    } else if n == 0x8E {
        Some(0x017D)  // LATIN CAPITAL LETTER Z WITH CARON
    } else if n == 0x91 {
        Some(0x2018)  // LEFT SINGLE QUOTATION MARK
    } else if n == 0x92 {
        Some(0x2019)  // RIGHT SINGLE QUOTATION MARK
    } else if n == 0x93 {
        Some(0x201C)  // LEFT DOUBLE QUOTATION MARK
    } else if n == 0x94 {
        Some(0x201D)  // RIGHT DOUBLE QUOTATION MARK
    } else if n == 0x95 {
        Some(0x2022)  // BULLET
    } else if n == 0x96 {
        Some(0x2013)  // EN DASH
    } else if n == 0x97 {
        Some(0x2014)  // EM DASH
    } else if n == 0x98 {
        Some(0x02DC)  // SMALL TILDE
    } else if n == 0x99 {
        Some(0x2122)  // TRADE MARK SIGN
    } else if n == 0x9A {
        Some(0x0161)  // LATIN SMALL LETTER S WITH CARON
    } else if n == 0x9B {
        Some(0x203A)  // SINGLE RIGHT-POINTING ANGLE QUOTATION MARK
    } else if n == 0x9C {
        Some(0x0153)  // LATIN SMALL LIGATURE OE
    } else if n == 0x9E {
        Some(0x017E)  // LATIN SMALL LETTER Z WITH CARON
    } else if n == 0x9F {
        Some(0x0178)  // LATIN CAPITAL LETTER Y WITH DIAERESIS
    } else {
        None
    }
}

/// 8.2.4.78 Numeric character reference end state. It does not consume a
/// character.
pub open spec fn w3c_numeric_character_reference_end(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Check the character reference code."
    // "If that number is one of the numbers in the first column of the
    // following table, then this is a parse error. Find the row with that
    // number in the first column, and set the character reference code to
    // the number in the second column of that row."
    let code1 = match w3c_numeric_replacement(t.character_reference_code) {
        Some(r) => r,
        None => t.character_reference_code,
    };
    // "If the number is in the range 0xD800 to 0xDFFF or is greater than
    // 0x10FFFF, then this is a parse error. Set the character reference code
    // to 0xFFFD."
    let code2: nat = if (0xD800 <= code1 && code1 <= 0xDFFF) || code1 > 0x10FFFF {
        0xFFFD
    } else {
        code1
    };
    // "If the number is in the range 0x0001 to 0x0008, 0x000D to 0x001F,
    // 0x007F to 0x009F, 0xFDD0 to 0xFDEF, or is one of 0x000B, 0xFFFE, ...,
    // 0x10FFFE, or 0x10FFFF, then this is a parse error." (not modelled)
    // "Set the temporary buffer to the empty string. Append the Unicode
    // character with code point equal to the character reference code to
    // the temporary buffer. Switch to the character reference end state."
    (
        w3c_go(
            W3cTokenizer { character_reference_code: code2, temporary_buffer: seq![code2 as u32], ..t },
            W3cState::CharacterReferenceEnd,
            t.pos,
        ),
        seq![],
    )
}

/// 8.2.4.79 Character reference end state.
pub open spec fn w3c_character_reference_end(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    // "Consume the next input character." Its only use is the
    // "Reconsume in the return state" below, so `pos` ends where it is.
    // "Check the return state:"
    if w3c_return_state_is_attribute(t.return_state) {
        // attribute value (double-quoted), (single-quoted) or (unquoted)
        // state: "Append each character in the temporary buffer (in the order
        // they were added to the buffer) to the current attribute's value."
        // "Reconsume in the return state."
        (
            w3c_reconsume(w3c_attribute_value_append(t, t.temporary_buffer), w3c_return_state(t.return_state)),
            seq![],
        )
    } else {
        // Anything else: "For each of the characters in the temporary buffer
        // (in the order they were added to the buffer), emit the character as
        // a character token."
        // "Reconsume in the return state."
        (w3c_reconsume(t, w3c_return_state(t.return_state)), w3c_characters(t.temporary_buffer))
    }
}

// ---------------------------------------------------------------------------
// The machine.
// ---------------------------------------------------------------------------

/// One step of the state machine: the current state's handling of the next
/// input character.
#[verifier::opaque]
pub open spec fn w3c_step(input: Seq<u32>, t: W3cTokenizer) -> W3cStep {
    match t.state {
        W3cState::Data => w3c_data(input, t),
        W3cState::Rcdata => w3c_rcdata(input, t),
        W3cState::Rawtext => w3c_rawtext(input, t),
        W3cState::ScriptData => w3c_script_data(input, t),
        W3cState::Plaintext => w3c_plaintext(input, t),
        W3cState::TagOpen => w3c_tag_open(input, t),
        W3cState::EndTagOpen => w3c_end_tag_open(input, t),
        W3cState::TagName => w3c_tag_name(input, t),
        W3cState::RcdataLessThanSign => w3c_rcdata_less_than_sign(input, t),
        W3cState::RcdataEndTagOpen => w3c_rcdata_end_tag_open(input, t),
        W3cState::RcdataEndTagName => w3c_rcdata_end_tag_name(input, t),
        W3cState::RawtextLessThanSign => w3c_rawtext_less_than_sign(input, t),
        W3cState::RawtextEndTagOpen => w3c_rawtext_end_tag_open(input, t),
        W3cState::RawtextEndTagName => w3c_rawtext_end_tag_name(input, t),
        W3cState::ScriptDataLessThanSign => w3c_script_data_less_than_sign(input, t),
        W3cState::ScriptDataEndTagOpen => w3c_script_data_end_tag_open(input, t),
        W3cState::ScriptDataEndTagName => w3c_script_data_end_tag_name(input, t),
        W3cState::ScriptDataEscapeStart => w3c_script_data_escape_start(input, t),
        W3cState::ScriptDataEscapeStartDash => w3c_script_data_escape_start_dash(input, t),
        W3cState::ScriptDataEscaped => w3c_script_data_escaped(input, t),
        W3cState::ScriptDataEscapedDash => w3c_script_data_escaped_dash(input, t),
        W3cState::ScriptDataEscapedDashDash => w3c_script_data_escaped_dash_dash(input, t),
        W3cState::ScriptDataEscapedLessThanSign => w3c_script_data_escaped_less_than_sign(input, t),
        W3cState::ScriptDataEscapedEndTagOpen => w3c_script_data_escaped_end_tag_open(input, t),
        W3cState::ScriptDataEscapedEndTagName => w3c_script_data_escaped_end_tag_name(input, t),
        W3cState::ScriptDataDoubleEscapeStart => w3c_script_data_double_escape_start(input, t),
        W3cState::ScriptDataDoubleEscaped => w3c_script_data_double_escaped(input, t),
        W3cState::ScriptDataDoubleEscapedDash => w3c_script_data_double_escaped_dash(input, t),
        W3cState::ScriptDataDoubleEscapedDashDash => w3c_script_data_double_escaped_dash_dash(input, t),
        W3cState::ScriptDataDoubleEscapedLessThanSign => w3c_script_data_double_escaped_less_than_sign(input, t),
        W3cState::ScriptDataDoubleEscapeEnd => w3c_script_data_double_escape_end(input, t),
        W3cState::BeforeAttributeName => w3c_before_attribute_name(input, t),
        W3cState::AttributeName => w3c_attribute_name(input, t),
        W3cState::AfterAttributeName => w3c_after_attribute_name(input, t),
        W3cState::BeforeAttributeValue => w3c_before_attribute_value(input, t),
        W3cState::AttributeValueDoubleQuoted => w3c_attribute_value_double_quoted(input, t),
        W3cState::AttributeValueSingleQuoted => w3c_attribute_value_single_quoted(input, t),
        W3cState::AttributeValueUnquoted => w3c_attribute_value_unquoted(input, t),
        W3cState::AfterAttributeValueQuoted => w3c_after_attribute_value_quoted(input, t),
        W3cState::SelfClosingStartTag => w3c_self_closing_start_tag(input, t),
        W3cState::BogusComment => w3c_bogus_comment(input, t),
        W3cState::MarkupDeclarationOpen => w3c_markup_declaration_open(input, t),
        W3cState::CommentStart => w3c_comment_start(input, t),
        W3cState::CommentStartDash => w3c_comment_start_dash(input, t),
        W3cState::Comment => w3c_comment(input, t),
        W3cState::CommentLessThanSign => w3c_comment_less_than_sign(input, t),
        W3cState::CommentLessThanSignBang => w3c_comment_less_than_sign_bang(input, t),
        W3cState::CommentLessThanSignBangDash => w3c_comment_less_than_sign_bang_dash(input, t),
        W3cState::CommentLessThanSignBangDashDash => w3c_comment_less_than_sign_bang_dash_dash(input, t),
        W3cState::CommentEndDash => w3c_comment_end_dash(input, t),
        W3cState::CommentEnd => w3c_comment_end(input, t),
        W3cState::CommentEndBang => w3c_comment_end_bang(input, t),
        W3cState::Doctype => w3c_doctype(input, t),
        W3cState::BeforeDoctypeName => w3c_before_doctype_name(input, t),
        W3cState::DoctypeName => w3c_doctype_name(input, t),
        W3cState::AfterDoctypeName => w3c_after_doctype_name(input, t),
        W3cState::AfterDoctypePublicKeyword => w3c_after_doctype_public_keyword(input, t),
        W3cState::BeforeDoctypePublicIdentifier => w3c_before_doctype_public_identifier(input, t),
        W3cState::DoctypePublicIdentifierDoubleQuoted => w3c_doctype_public_identifier_double_quoted(input, t),
        W3cState::DoctypePublicIdentifierSingleQuoted => w3c_doctype_public_identifier_single_quoted(input, t),
        W3cState::AfterDoctypePublicIdentifier => w3c_after_doctype_public_identifier(input, t),
        W3cState::BetweenDoctypePublicAndSystemIdentifiers => w3c_between_doctype_public_and_system_identifiers(
            input,
            t,
        ),
        W3cState::AfterDoctypeSystemKeyword => w3c_after_doctype_system_keyword(input, t),
        W3cState::BeforeDoctypeSystemIdentifier => w3c_before_doctype_system_identifier(input, t),
        W3cState::DoctypeSystemIdentifierDoubleQuoted => w3c_doctype_system_identifier_double_quoted(input, t),
        W3cState::DoctypeSystemIdentifierSingleQuoted => w3c_doctype_system_identifier_single_quoted(input, t),
        W3cState::AfterDoctypeSystemIdentifier => w3c_after_doctype_system_identifier(input, t),
        W3cState::BogusDoctype => w3c_bogus_doctype(input, t),
        W3cState::CdataSection => w3c_cdata_section(input, t),
        W3cState::CdataSectionBracket => w3c_cdata_section_bracket(input, t),
        W3cState::CdataSectionEnd => w3c_cdata_section_end(input, t),
        W3cState::CharacterReference => w3c_character_reference(input, t),
        W3cState::NumericCharacterReference => w3c_numeric_character_reference(input, t),
        W3cState::HexadecimalCharacterReferenceStart => w3c_hexadecimal_character_reference_start(input, t),
        W3cState::DecimalCharacterReferenceStart => w3c_decimal_character_reference_start(input, t),
        W3cState::HexadecimalCharacterReference => w3c_hexadecimal_character_reference(input, t),
        W3cState::DecimalCharacterReference => w3c_decimal_character_reference(input, t),
        W3cState::NumericCharacterReferenceEnd => w3c_numeric_character_reference_end(input, t),
        W3cState::CharacterReferenceEnd => w3c_character_reference_end(input, t),
    }
}

/// The tokenizer has stopped: it emitted the end-of-file token, or its
/// position is past the EOF.
pub open spec fn w3c_stopped(input: Seq<u32>, t: W3cTokenizer) -> bool {
    t.done || t.pos > input.len()
}

/// The characters left before the EOF.
pub open spec fn w3c_remaining(input: Seq<u32>, t: W3cTokenizer) -> nat {
    if t.pos <= input.len() {
        (input.len() - t.pos) as nat
    } else {
        0
    }
}

/// A rank for each state, given the next input character, that every step
/// which does not consume a character lowers (see [`w3c_run_decreases`]):
/// 0 for the states that consume in every case, and above the rank of
/// every state that a state reconsumes in. The attribute name state
/// reconsumes in the after attribute name state, and that one in the
/// attribute name state, but on disjoint characters, so the attribute name
/// state's rank depends on the character.
pub open spec fn w3c_state_rank(s: W3cState, c: Option<u32>) -> nat {
    match s {
        W3cState::TagOpen => 1,
        W3cState::EndTagOpen => 1,
        W3cState::RcdataLessThanSign => 1,
        W3cState::RcdataEndTagOpen => 2,
        W3cState::RcdataEndTagName => 1,
        W3cState::RawtextLessThanSign => 1,
        W3cState::RawtextEndTagOpen => 2,
        W3cState::RawtextEndTagName => 1,
        W3cState::ScriptDataLessThanSign => 1,
        W3cState::ScriptDataEndTagOpen => 2,
        W3cState::ScriptDataEndTagName => 1,
        W3cState::ScriptDataEscapeStart => 1,
        W3cState::ScriptDataEscapeStartDash => 1,
        W3cState::ScriptDataEscapedLessThanSign => 2,
        W3cState::ScriptDataEscapedEndTagOpen => 2,
        W3cState::ScriptDataEscapedEndTagName => 1,
        W3cState::ScriptDataDoubleEscapeStart => 1,
        W3cState::ScriptDataDoubleEscapedLessThanSign => 1,
        W3cState::ScriptDataDoubleEscapeEnd => 1,
        W3cState::BeforeAttributeName => 2,
        W3cState::AttributeName => if w3c_is_tab_lf_ff_space(c) || c == Some(0x002Fu32) || c == Some(
            0x003Eu32,
        ) || w3c_is_eof(c) {
            2
        } else {
            0
        },
        W3cState::AfterAttributeName => 1,
        W3cState::BeforeAttributeValue => 1,
        W3cState::AfterAttributeValueQuoted => 3,
        W3cState::SelfClosingStartTag => 3,
        W3cState::MarkupDeclarationOpen => 1,
        W3cState::CommentStart => 1,
        W3cState::CommentStartDash => 1,
        W3cState::CommentLessThanSign => 1,
        W3cState::CommentLessThanSignBang => 1,
        W3cState::CommentLessThanSignBangDash => 2,
        W3cState::CommentLessThanSignBangDashDash => 2,
        W3cState::CommentEndDash => 1,
        W3cState::CommentEnd => 1,
        W3cState::CommentEndBang => 1,
        W3cState::Doctype => 1,
        W3cState::CdataSectionBracket => 1,
        W3cState::CdataSectionEnd => 1,
        W3cState::CharacterReference => 6,
        W3cState::NumericCharacterReference => 5,
        W3cState::HexadecimalCharacterReferenceStart => 4,
        W3cState::DecimalCharacterReferenceStart => 4,
        W3cState::HexadecimalCharacterReference => 3,
        W3cState::DecimalCharacterReference => 3,
        W3cState::NumericCharacterReferenceEnd => 2,
        W3cState::CharacterReferenceEnd => 1,
        _ => 0,
    }
}

/// The tokenizer's rank: its state's, at its next input character.
pub open spec fn w3c_rank(input: Seq<u32>, t: W3cTokenizer) -> nat {
    w3c_state_rank(t.state, w3c_next(input, t.pos))
}

/// Run the state machine from `t` until it stops: the tokens emitted, in
/// order.
pub open spec fn w3c_run(input: Seq<u32>, t: W3cTokenizer) -> Seq<Token>
    decreases w3c_remaining(input, t), w3c_rank(input, t) via w3c_run_decreases
{
    if w3c_stopped(input, t) {
        seq![]
    } else {
        let (t2, out) = w3c_step(input, t);
        if w3c_stopped(input, t2) {
            out
        } else {
            out + w3c_run(input, t2)
        }
    }
}

/// A tokenizer in state `start` before the first input character, with
/// `last_start_tag` the tag name of the last start tag emitted before (for
/// "appropriate end tag token"), and no adjusted current node.
pub open spec fn w3c_initial(start: W3cState, last_start_tag: Option<Seq<u32>>) -> W3cTokenizer {
    W3cTokenizer {
        state: start,
        return_state: W3cReturnState::Data,
        temporary_buffer: seq![],
        character_reference_code: 0,
        current_token: Token::EndOfFile,
        current_attribute: None,
        current_attribute_removed: false,
        last_start_tag_name: last_start_tag,
        adjusted_current_node_not_html: false,
        pos: 0,
        done: false,
    }
}

/// The tokens of `input`, starting in state `start` ("The state machine
/// must start in the data state"; other start states are what the tree
/// construction stage sets for RCDATA, RAWTEXT, script data and PLAINTEXT
/// elements).
pub open spec fn w3c_tokenize(input: Seq<u32>, start: W3cState, last_start_tag: Option<Seq<u32>>) -> Seq<Token> {
    w3c_run(input, w3c_initial(start, last_start_tag))
}

// ---------------------------------------------------------------------------
// Termination.
// ---------------------------------------------------------------------------

/// From `t` to `t2` the measure of [`w3c_run`] goes down: fewer characters
/// left, or as many and a lower rank.
pub open spec fn w3c_progress(input: Seq<u32>, t: W3cTokenizer, t2: W3cTokenizer) -> bool {
    w3c_remaining(input, t2) < w3c_remaining(input, t) || (w3c_remaining(input, t2) == w3c_remaining(
        input,
        t,
    ) && w3c_rank(input, t2) < w3c_rank(input, t))
}

/// [`w3c_data`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_data_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::Data,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_data(input, t).0),
    ensures
        w3c_progress(input, t, w3c_data(input, t).0),
{
}

/// [`w3c_rcdata`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rcdata_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::Rcdata,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rcdata(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rcdata(input, t).0),
{
}

/// [`w3c_rawtext`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rawtext_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::Rawtext,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rawtext(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rawtext(input, t).0),
{
}

/// [`w3c_script_data`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptData,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data(input, t).0),
{
}

/// [`w3c_plaintext`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_plaintext_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::Plaintext,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_plaintext(input, t).0),
    ensures
        w3c_progress(input, t, w3c_plaintext(input, t).0),
{
}

/// [`w3c_tag_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_tag_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::TagOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_tag_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_tag_open(input, t).0),
{
}

/// [`w3c_end_tag_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_end_tag_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::EndTagOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_end_tag_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_end_tag_open(input, t).0),
{
}

/// [`w3c_tag_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_tag_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::TagName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_tag_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_tag_name(input, t).0),
{
}

/// [`w3c_rcdata_less_than_sign`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rcdata_less_than_sign_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::RcdataLessThanSign,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rcdata_less_than_sign(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rcdata_less_than_sign(input, t).0),
{
}

/// [`w3c_rcdata_end_tag_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rcdata_end_tag_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::RcdataEndTagOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rcdata_end_tag_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rcdata_end_tag_open(input, t).0),
{
}

/// [`w3c_rcdata_end_tag_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rcdata_end_tag_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::RcdataEndTagName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rcdata_end_tag_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rcdata_end_tag_name(input, t).0),
{
}

/// [`w3c_rawtext_less_than_sign`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rawtext_less_than_sign_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::RawtextLessThanSign,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rawtext_less_than_sign(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rawtext_less_than_sign(input, t).0),
{
}

/// [`w3c_rawtext_end_tag_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rawtext_end_tag_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::RawtextEndTagOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rawtext_end_tag_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rawtext_end_tag_open(input, t).0),
{
}

/// [`w3c_rawtext_end_tag_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_rawtext_end_tag_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::RawtextEndTagName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_rawtext_end_tag_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_rawtext_end_tag_name(input, t).0),
{
}

/// [`w3c_script_data_less_than_sign`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_less_than_sign_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataLessThanSign,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_less_than_sign(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_less_than_sign(input, t).0),
{
}

/// [`w3c_script_data_end_tag_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_end_tag_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEndTagOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_end_tag_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_end_tag_open(input, t).0),
{
}

/// [`w3c_script_data_end_tag_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_end_tag_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEndTagName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_end_tag_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_end_tag_name(input, t).0),
{
}

/// [`w3c_script_data_escape_start`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escape_start_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapeStart,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escape_start(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escape_start(input, t).0),
{
}

/// [`w3c_script_data_escape_start_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escape_start_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapeStartDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escape_start_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escape_start_dash(input, t).0),
{
}

/// [`w3c_script_data_escaped`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escaped_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscaped,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escaped(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escaped(input, t).0),
{
}

/// [`w3c_script_data_escaped_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escaped_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapedDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escaped_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escaped_dash(input, t).0),
{
}

/// [`w3c_script_data_escaped_dash_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escaped_dash_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapedDashDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escaped_dash_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escaped_dash_dash(input, t).0),
{
}

/// [`w3c_script_data_escaped_less_than_sign`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escaped_less_than_sign_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapedLessThanSign,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escaped_less_than_sign(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escaped_less_than_sign(input, t).0),
{
}

/// [`w3c_script_data_escaped_end_tag_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escaped_end_tag_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapedEndTagOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escaped_end_tag_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escaped_end_tag_open(input, t).0),
{
}

/// [`w3c_script_data_escaped_end_tag_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_escaped_end_tag_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataEscapedEndTagName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_escaped_end_tag_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_escaped_end_tag_name(input, t).0),
{
}

/// [`w3c_script_data_double_escape_start`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_double_escape_start_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataDoubleEscapeStart,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_double_escape_start(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_double_escape_start(input, t).0),
{
}

/// [`w3c_script_data_double_escaped`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_double_escaped_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataDoubleEscaped,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_double_escaped(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_double_escaped(input, t).0),
{
}

/// [`w3c_script_data_double_escaped_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_double_escaped_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataDoubleEscapedDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_double_escaped_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_double_escaped_dash(input, t).0),
{
}

/// [`w3c_script_data_double_escaped_dash_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_double_escaped_dash_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataDoubleEscapedDashDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_double_escaped_dash_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_double_escaped_dash_dash(input, t).0),
{
}

/// [`w3c_script_data_double_escaped_less_than_sign`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_double_escaped_less_than_sign_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataDoubleEscapedLessThanSign,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_double_escaped_less_than_sign(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_double_escaped_less_than_sign(input, t).0),
{
}

/// [`w3c_script_data_double_escape_end`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_script_data_double_escape_end_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::ScriptDataDoubleEscapeEnd,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_script_data_double_escape_end(input, t).0),
    ensures
        w3c_progress(input, t, w3c_script_data_double_escape_end(input, t).0),
{
}

/// [`w3c_before_attribute_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_before_attribute_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BeforeAttributeName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_before_attribute_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_before_attribute_name(input, t).0),
{
}

/// [`w3c_attribute_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_attribute_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AttributeName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_attribute_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_attribute_name(input, t).0),
{
}

/// [`w3c_after_attribute_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_attribute_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterAttributeName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_attribute_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_attribute_name(input, t).0),
{
}

/// [`w3c_before_attribute_value`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_before_attribute_value_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BeforeAttributeValue,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_before_attribute_value(input, t).0),
    ensures
        w3c_progress(input, t, w3c_before_attribute_value(input, t).0),
{
}

/// [`w3c_attribute_value_double_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_attribute_value_double_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AttributeValueDoubleQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_attribute_value_double_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_attribute_value_double_quoted(input, t).0),
{
}

/// [`w3c_attribute_value_single_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_attribute_value_single_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AttributeValueSingleQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_attribute_value_single_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_attribute_value_single_quoted(input, t).0),
{
}

/// [`w3c_attribute_value_unquoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_attribute_value_unquoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AttributeValueUnquoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_attribute_value_unquoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_attribute_value_unquoted(input, t).0),
{
}

/// [`w3c_after_attribute_value_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_attribute_value_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterAttributeValueQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_attribute_value_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_attribute_value_quoted(input, t).0),
{
}

/// [`w3c_self_closing_start_tag`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_self_closing_start_tag_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::SelfClosingStartTag,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_self_closing_start_tag(input, t).0),
    ensures
        w3c_progress(input, t, w3c_self_closing_start_tag(input, t).0),
{
}

/// [`w3c_bogus_comment`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_bogus_comment_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BogusComment,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_bogus_comment(input, t).0),
    ensures
        w3c_progress(input, t, w3c_bogus_comment(input, t).0),
{
}

/// [`w3c_markup_declaration_open`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_markup_declaration_open_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::MarkupDeclarationOpen,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_markup_declaration_open(input, t).0),
    ensures
        w3c_progress(input, t, w3c_markup_declaration_open(input, t).0),
{
}

/// [`w3c_comment_start`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_start_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentStart,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_start(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_start(input, t).0),
{
}

/// [`w3c_comment_start_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_start_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentStartDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_start_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_start_dash(input, t).0),
{
}

/// [`w3c_comment`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::Comment,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment(input, t).0),
{
}

/// [`w3c_comment_less_than_sign`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_less_than_sign_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentLessThanSign,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_less_than_sign(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_less_than_sign(input, t).0),
{
}

/// [`w3c_comment_less_than_sign_bang`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_less_than_sign_bang_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentLessThanSignBang,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_less_than_sign_bang(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_less_than_sign_bang(input, t).0),
{
}

/// [`w3c_comment_less_than_sign_bang_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_less_than_sign_bang_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentLessThanSignBangDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_less_than_sign_bang_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_less_than_sign_bang_dash(input, t).0),
{
}

/// [`w3c_comment_less_than_sign_bang_dash_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_less_than_sign_bang_dash_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentLessThanSignBangDashDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_less_than_sign_bang_dash_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_less_than_sign_bang_dash_dash(input, t).0),
{
}

/// [`w3c_comment_end_dash`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_end_dash_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentEndDash,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_end_dash(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_end_dash(input, t).0),
{
}

/// [`w3c_comment_end`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_end_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentEnd,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_end(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_end(input, t).0),
{
}

/// [`w3c_comment_end_bang`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_comment_end_bang_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CommentEndBang,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_comment_end_bang(input, t).0),
    ensures
        w3c_progress(input, t, w3c_comment_end_bang(input, t).0),
{
}

/// [`w3c_doctype`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_doctype_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::Doctype,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_doctype(input, t).0),
    ensures
        w3c_progress(input, t, w3c_doctype(input, t).0),
{
}

/// [`w3c_before_doctype_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_before_doctype_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BeforeDoctypeName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_before_doctype_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_before_doctype_name(input, t).0),
{
}

/// [`w3c_doctype_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_doctype_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DoctypeName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_doctype_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_doctype_name(input, t).0),
{
}

/// [`w3c_after_doctype_name`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_doctype_name_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterDoctypeName,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_doctype_name(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_doctype_name(input, t).0),
{
}

/// [`w3c_after_doctype_public_keyword`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_doctype_public_keyword_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterDoctypePublicKeyword,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_doctype_public_keyword(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_doctype_public_keyword(input, t).0),
{
}

/// [`w3c_before_doctype_public_identifier`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_before_doctype_public_identifier_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BeforeDoctypePublicIdentifier,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_before_doctype_public_identifier(input, t).0),
    ensures
        w3c_progress(input, t, w3c_before_doctype_public_identifier(input, t).0),
{
}

/// [`w3c_doctype_public_identifier_double_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_doctype_public_identifier_double_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DoctypePublicIdentifierDoubleQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_doctype_public_identifier_double_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_doctype_public_identifier_double_quoted(input, t).0),
{
}

/// [`w3c_doctype_public_identifier_single_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_doctype_public_identifier_single_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DoctypePublicIdentifierSingleQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_doctype_public_identifier_single_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_doctype_public_identifier_single_quoted(input, t).0),
{
}

/// [`w3c_after_doctype_public_identifier`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_doctype_public_identifier_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterDoctypePublicIdentifier,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_doctype_public_identifier(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_doctype_public_identifier(input, t).0),
{
}

/// [`w3c_between_doctype_public_and_system_identifiers`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_between_doctype_public_and_system_identifiers_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BetweenDoctypePublicAndSystemIdentifiers,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_between_doctype_public_and_system_identifiers(input, t).0),
    ensures
        w3c_progress(input, t, w3c_between_doctype_public_and_system_identifiers(input, t).0),
{
}

/// [`w3c_after_doctype_system_keyword`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_doctype_system_keyword_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterDoctypeSystemKeyword,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_doctype_system_keyword(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_doctype_system_keyword(input, t).0),
{
}

/// [`w3c_before_doctype_system_identifier`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_before_doctype_system_identifier_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BeforeDoctypeSystemIdentifier,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_before_doctype_system_identifier(input, t).0),
    ensures
        w3c_progress(input, t, w3c_before_doctype_system_identifier(input, t).0),
{
}

/// [`w3c_doctype_system_identifier_double_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_doctype_system_identifier_double_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DoctypeSystemIdentifierDoubleQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_doctype_system_identifier_double_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_doctype_system_identifier_double_quoted(input, t).0),
{
}

/// [`w3c_doctype_system_identifier_single_quoted`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_doctype_system_identifier_single_quoted_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DoctypeSystemIdentifierSingleQuoted,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_doctype_system_identifier_single_quoted(input, t).0),
    ensures
        w3c_progress(input, t, w3c_doctype_system_identifier_single_quoted(input, t).0),
{
}

/// [`w3c_after_doctype_system_identifier`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_after_doctype_system_identifier_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::AfterDoctypeSystemIdentifier,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_after_doctype_system_identifier(input, t).0),
    ensures
        w3c_progress(input, t, w3c_after_doctype_system_identifier(input, t).0),
{
}

/// [`w3c_bogus_doctype`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_bogus_doctype_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::BogusDoctype,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_bogus_doctype(input, t).0),
    ensures
        w3c_progress(input, t, w3c_bogus_doctype(input, t).0),
{
}

/// [`w3c_cdata_section`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_cdata_section_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CdataSection,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_cdata_section(input, t).0),
    ensures
        w3c_progress(input, t, w3c_cdata_section(input, t).0),
{
}

/// [`w3c_cdata_section_bracket`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_cdata_section_bracket_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CdataSectionBracket,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_cdata_section_bracket(input, t).0),
    ensures
        w3c_progress(input, t, w3c_cdata_section_bracket(input, t).0),
{
}

/// [`w3c_cdata_section_end`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_cdata_section_end_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CdataSectionEnd,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_cdata_section_end(input, t).0),
    ensures
        w3c_progress(input, t, w3c_cdata_section_end(input, t).0),
{
}

/// [`w3c_character_reference`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_character_reference_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CharacterReference,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_character_reference(input, t).0),
    ensures
        w3c_progress(input, t, w3c_character_reference(input, t).0),
{
}

/// [`w3c_numeric_character_reference`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_numeric_character_reference_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::NumericCharacterReference,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_numeric_character_reference(input, t).0),
    ensures
        w3c_progress(input, t, w3c_numeric_character_reference(input, t).0),
{
}

/// [`w3c_hexadecimal_character_reference_start`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_hexadecimal_character_reference_start_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::HexadecimalCharacterReferenceStart,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_hexadecimal_character_reference_start(input, t).0),
    ensures
        w3c_progress(input, t, w3c_hexadecimal_character_reference_start(input, t).0),
{
}

/// [`w3c_decimal_character_reference_start`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_decimal_character_reference_start_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DecimalCharacterReferenceStart,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_decimal_character_reference_start(input, t).0),
    ensures
        w3c_progress(input, t, w3c_decimal_character_reference_start(input, t).0),
{
}

/// [`w3c_hexadecimal_character_reference`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_hexadecimal_character_reference_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::HexadecimalCharacterReference,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_hexadecimal_character_reference(input, t).0),
    ensures
        w3c_progress(input, t, w3c_hexadecimal_character_reference(input, t).0),
{
}

/// [`w3c_decimal_character_reference`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_decimal_character_reference_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::DecimalCharacterReference,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_decimal_character_reference(input, t).0),
    ensures
        w3c_progress(input, t, w3c_decimal_character_reference(input, t).0),
{
}

/// [`w3c_numeric_character_reference_end`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_numeric_character_reference_end_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::NumericCharacterReferenceEnd,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_numeric_character_reference_end(input, t).0),
    ensures
        w3c_progress(input, t, w3c_numeric_character_reference_end(input, t).0),
{
}

/// [`w3c_character_reference_end`] lowers the measure when it does not stop the tokenizer.
pub proof fn lemma_w3c_character_reference_end_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        t.state == W3cState::CharacterReferenceEnd,
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_character_reference_end(input, t).0),
    ensures
        w3c_progress(input, t, w3c_character_reference_end(input, t).0),
{
}
/// One step of [`w3c_step`] that does not stop the tokenizer lowers the
/// measure, state by state.
pub proof fn lemma_w3c_step_progress(input: Seq<u32>, t: W3cTokenizer)
    requires
        !w3c_stopped(input, t),
        !w3c_stopped(input, w3c_step(input, t).0),
    ensures
        w3c_progress(input, t, w3c_step(input, t).0),
{
    reveal(w3c_step);
    match t.state {
        W3cState::Data => lemma_w3c_data_progress(input, t),
        W3cState::Rcdata => lemma_w3c_rcdata_progress(input, t),
        W3cState::Rawtext => lemma_w3c_rawtext_progress(input, t),
        W3cState::ScriptData => lemma_w3c_script_data_progress(input, t),
        W3cState::Plaintext => lemma_w3c_plaintext_progress(input, t),
        W3cState::TagOpen => lemma_w3c_tag_open_progress(input, t),
        W3cState::EndTagOpen => lemma_w3c_end_tag_open_progress(input, t),
        W3cState::TagName => lemma_w3c_tag_name_progress(input, t),
        W3cState::RcdataLessThanSign => lemma_w3c_rcdata_less_than_sign_progress(input, t),
        W3cState::RcdataEndTagOpen => lemma_w3c_rcdata_end_tag_open_progress(input, t),
        W3cState::RcdataEndTagName => lemma_w3c_rcdata_end_tag_name_progress(input, t),
        W3cState::RawtextLessThanSign => lemma_w3c_rawtext_less_than_sign_progress(input, t),
        W3cState::RawtextEndTagOpen => lemma_w3c_rawtext_end_tag_open_progress(input, t),
        W3cState::RawtextEndTagName => lemma_w3c_rawtext_end_tag_name_progress(input, t),
        W3cState::ScriptDataLessThanSign => lemma_w3c_script_data_less_than_sign_progress(input, t),
        W3cState::ScriptDataEndTagOpen => lemma_w3c_script_data_end_tag_open_progress(input, t),
        W3cState::ScriptDataEndTagName => lemma_w3c_script_data_end_tag_name_progress(input, t),
        W3cState::ScriptDataEscapeStart => lemma_w3c_script_data_escape_start_progress(input, t),
        W3cState::ScriptDataEscapeStartDash => lemma_w3c_script_data_escape_start_dash_progress(input, t),
        W3cState::ScriptDataEscaped => lemma_w3c_script_data_escaped_progress(input, t),
        W3cState::ScriptDataEscapedDash => lemma_w3c_script_data_escaped_dash_progress(input, t),
        W3cState::ScriptDataEscapedDashDash => lemma_w3c_script_data_escaped_dash_dash_progress(input, t),
        W3cState::ScriptDataEscapedLessThanSign => lemma_w3c_script_data_escaped_less_than_sign_progress(input, t),
        W3cState::ScriptDataEscapedEndTagOpen => lemma_w3c_script_data_escaped_end_tag_open_progress(input, t),
        W3cState::ScriptDataEscapedEndTagName => lemma_w3c_script_data_escaped_end_tag_name_progress(input, t),
        W3cState::ScriptDataDoubleEscapeStart => lemma_w3c_script_data_double_escape_start_progress(input, t),
        W3cState::ScriptDataDoubleEscaped => lemma_w3c_script_data_double_escaped_progress(input, t),
        W3cState::ScriptDataDoubleEscapedDash => lemma_w3c_script_data_double_escaped_dash_progress(input, t),
        W3cState::ScriptDataDoubleEscapedDashDash => lemma_w3c_script_data_double_escaped_dash_dash_progress(input, t),
        W3cState::ScriptDataDoubleEscapedLessThanSign => lemma_w3c_script_data_double_escaped_less_than_sign_progress(input, t),
        W3cState::ScriptDataDoubleEscapeEnd => lemma_w3c_script_data_double_escape_end_progress(input, t),
        W3cState::BeforeAttributeName => lemma_w3c_before_attribute_name_progress(input, t),
        W3cState::AttributeName => lemma_w3c_attribute_name_progress(input, t),
        W3cState::AfterAttributeName => lemma_w3c_after_attribute_name_progress(input, t),
        W3cState::BeforeAttributeValue => lemma_w3c_before_attribute_value_progress(input, t),
        W3cState::AttributeValueDoubleQuoted => lemma_w3c_attribute_value_double_quoted_progress(input, t),
        W3cState::AttributeValueSingleQuoted => lemma_w3c_attribute_value_single_quoted_progress(input, t),
        W3cState::AttributeValueUnquoted => lemma_w3c_attribute_value_unquoted_progress(input, t),
        W3cState::AfterAttributeValueQuoted => lemma_w3c_after_attribute_value_quoted_progress(input, t),
        W3cState::SelfClosingStartTag => lemma_w3c_self_closing_start_tag_progress(input, t),
        W3cState::BogusComment => lemma_w3c_bogus_comment_progress(input, t),
        W3cState::MarkupDeclarationOpen => lemma_w3c_markup_declaration_open_progress(input, t),
        W3cState::CommentStart => lemma_w3c_comment_start_progress(input, t),
        W3cState::CommentStartDash => lemma_w3c_comment_start_dash_progress(input, t),
        W3cState::Comment => lemma_w3c_comment_progress(input, t),
        W3cState::CommentLessThanSign => lemma_w3c_comment_less_than_sign_progress(input, t),
        W3cState::CommentLessThanSignBang => lemma_w3c_comment_less_than_sign_bang_progress(input, t),
        W3cState::CommentLessThanSignBangDash => lemma_w3c_comment_less_than_sign_bang_dash_progress(input, t),
        W3cState::CommentLessThanSignBangDashDash => lemma_w3c_comment_less_than_sign_bang_dash_dash_progress(input, t),
        W3cState::CommentEndDash => lemma_w3c_comment_end_dash_progress(input, t),
        W3cState::CommentEnd => lemma_w3c_comment_end_progress(input, t),
        W3cState::CommentEndBang => lemma_w3c_comment_end_bang_progress(input, t),
        W3cState::Doctype => lemma_w3c_doctype_progress(input, t),
        W3cState::BeforeDoctypeName => lemma_w3c_before_doctype_name_progress(input, t),
        W3cState::DoctypeName => lemma_w3c_doctype_name_progress(input, t),
        W3cState::AfterDoctypeName => lemma_w3c_after_doctype_name_progress(input, t),
        W3cState::AfterDoctypePublicKeyword => lemma_w3c_after_doctype_public_keyword_progress(input, t),
        W3cState::BeforeDoctypePublicIdentifier => lemma_w3c_before_doctype_public_identifier_progress(input, t),
        W3cState::DoctypePublicIdentifierDoubleQuoted => lemma_w3c_doctype_public_identifier_double_quoted_progress(input, t),
        W3cState::DoctypePublicIdentifierSingleQuoted => lemma_w3c_doctype_public_identifier_single_quoted_progress(input, t),
        W3cState::AfterDoctypePublicIdentifier => lemma_w3c_after_doctype_public_identifier_progress(input, t),
        W3cState::BetweenDoctypePublicAndSystemIdentifiers => lemma_w3c_between_doctype_public_and_system_identifiers_progress(input, t),
        W3cState::AfterDoctypeSystemKeyword => lemma_w3c_after_doctype_system_keyword_progress(input, t),
        W3cState::BeforeDoctypeSystemIdentifier => lemma_w3c_before_doctype_system_identifier_progress(input, t),
        W3cState::DoctypeSystemIdentifierDoubleQuoted => lemma_w3c_doctype_system_identifier_double_quoted_progress(input, t),
        W3cState::DoctypeSystemIdentifierSingleQuoted => lemma_w3c_doctype_system_identifier_single_quoted_progress(input, t),
        W3cState::AfterDoctypeSystemIdentifier => lemma_w3c_after_doctype_system_identifier_progress(input, t),
        W3cState::BogusDoctype => lemma_w3c_bogus_doctype_progress(input, t),
        W3cState::CdataSection => lemma_w3c_cdata_section_progress(input, t),
        W3cState::CdataSectionBracket => lemma_w3c_cdata_section_bracket_progress(input, t),
        W3cState::CdataSectionEnd => lemma_w3c_cdata_section_end_progress(input, t),
        W3cState::CharacterReference => lemma_w3c_character_reference_progress(input, t),
        W3cState::NumericCharacterReference => lemma_w3c_numeric_character_reference_progress(input, t),
        W3cState::HexadecimalCharacterReferenceStart => lemma_w3c_hexadecimal_character_reference_start_progress(input, t),
        W3cState::DecimalCharacterReferenceStart => lemma_w3c_decimal_character_reference_start_progress(input, t),
        W3cState::HexadecimalCharacterReference => lemma_w3c_hexadecimal_character_reference_progress(input, t),
        W3cState::DecimalCharacterReference => lemma_w3c_decimal_character_reference_progress(input, t),
        W3cState::NumericCharacterReferenceEnd => lemma_w3c_numeric_character_reference_end_progress(input, t),
        W3cState::CharacterReferenceEnd => lemma_w3c_character_reference_end_progress(input, t),
    }
}

/// Termination of [`w3c_run`]: a step that does not stop the tokenizer
/// lowers the measure.
#[via_fn]
pub proof fn w3c_run_decreases(input: Seq<u32>, t: W3cTokenizer) {
    if !w3c_stopped(input, t) {
        let t2 = w3c_step(input, t).0;
        if !w3c_stopped(input, t2) {
            lemma_w3c_step_progress(input, t);
        }
    }
}

} // verus!
