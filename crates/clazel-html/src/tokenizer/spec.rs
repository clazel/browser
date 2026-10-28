//! Executable-style specification of HTML tokenization, transcribed from
//! the WHATWG HTML Standard (Living Standard, whatwg/html commit
//! `939677714df7379fee3667040113b41c91c851e7`, 26 October 2026):
//! §13.2.3.5 "Preprocessing the input stream", the tokenizer's part of
//! §13.2.4 "Parse state", and §13.2.5 "Tokenization" with all 84 of its
//! states (<https://html.spec.whatwg.org/multipage/parsing.html#tokenization>).
//! Nothing here runs; it defines what "correct" means. Each state is one
//! spec function named after it, and each case of its "Consume the next
//! input character" switch is commented with the character it matches.
//! The character reference table and the numeric checks are in
//! `crate::charref::spec`.
//!
//! The standard at this commit has 84 states: the 80 that Phase 4's plan
//! counted, less the "decimal character reference start state" (removed
//! from the standard), plus five processing instruction states (§13.2.5.72
//! to §13.2.5.76), reached from the tag open state on `?`, and their
//! processing instruction token.
//!
//! Modelling choices (each one a deliberate, reviewable deviation in form,
//! never in meaning):
//! - The input stream is `input: Seq<u32>` of code points *after*
//!   preprocessing ([`preprocess`]), with the next input character at
//!   `pos` and EOF at `input.len()`. Consuming a character advances `pos`;
//!   "reconsume in the X state" switches to X without advancing it, which
//!   is exactly "provide it with the current input character instead";
//!   consuming EOF leaves `pos` at the end.
//! - Parse errors are not modelled: the standard says a user agent
//!   proceeds the same way whether or not it reports them. Each "This is a
//!   … parse error." sentence is kept as a comment where it stands.
//! - A state's work until it next consumes a character or switches state
//!   is one call of its spec function, which returns the new tokenizer and
//!   the tokens it emitted ([`Step`]). [`run`] calls them until an
//!   end-of-file token is emitted ([`Tokenizer::done`]): the standard's
//!   tokenizer stops there, since nothing follows EOF.
//! - The tokenizer has two faces, proven equal ([`run`] and
//!   [`next_token`], `theorem_step_equals_whole` in `lemmas.rs`):
//!   [`tokenize`]`(input, start_state, last_start_tag)` over the whole
//!   input, whose start state and last start tag are the parameters the
//!   html5lib tests set (`initialStates`, `lastStartTag`), as the URL
//!   parser's state override is a parameter; and [`next_token`], which runs
//!   steps until at least one token is emitted and returns the tokenizer,
//!   for the tree builder, which switches the state between tokens
//!   (§13.2.6.2) and sets [`Tokenizer::in_foreign_content`].
//! - The markup declaration open state's CDATA rule asks whether "there is
//!   an adjusted current node and it is not an element in the HTML
//!   namespace". The tokenizer never sees the tree, so this is the flag
//!   [`Tokenizer::in_foreign_content`], set by the tree builder before each
//!   token.
//! - "The tag name of the last start tag to have been emitted from this
//!   tokenizer" is [`Tokenizer::last_start_tag`]: set when a start tag
//!   token is emitted, and a parameter of [`tokenize`] for tests and the
//!   fragment parsing algorithm.
//! - The return state is only ever set to the data state, the RCDATA
//!   state or one of the three attribute value states, so it is a
//!   [`ReturnState`] of those five, and "switch to the return state" is
//!   [`ReturnState::state`].
//! - The current tag token's attributes: "start a new attribute in the
//!   current tag token" adds it to the token, and on leaving the attribute
//!   name state a duplicate is "removed from the token" but stays the
//!   current attribute. Here the current attribute is kept apart
//!   ([`Tokenizer::current_attribute`]) with whether it is still on the
//!   token ([`AttributeStatus`]); the token's `attributes` are the earlier
//!   ones. It joins them when the next attribute starts or the token is
//!   emitted, unless it was removed. Nothing reads the token's list in
//!   between except the duplicate check, which compares with the earlier
//!   attributes, so this is the same list.
//! - The current token is one field ([`Tokenizer::current`]) of type
//!   [`Token`], holding the current tag, comment, DOCTYPE or processing
//!   instruction token; a state that changes a field of "the current tag
//!   token" changes it when the current token is a tag and does nothing
//!   otherwise (which no reachable state does).
//! - Where the standard words several states identically except for the
//!   states they name (the RCDATA, RAWTEXT, script data and script data
//!   escaped "less-than sign", "end tag open" and "end tag name" states;
//!   the two quoted attribute value states; the script data double escape
//!   start and end states; the public and system DOCTYPE keyword,
//!   identifier and quoted identifier states), each state still has its
//!   own spec function, which calls one shared function with those states
//!   (or the quote character) as parameters. The shared function's
//!   comments quote the text with the varying words in brackets.
//! - The character reference code is a `nat` (unbounded, as the
//!   standard's number is).
//! - Character tokens carry one code point each, as the standard emits
//!   them; html5lib's coalescing is the test's.
//! - The "parser pause flag" check before each step is omitted: the flag
//!   is never set without scripting, and a pause would only end a run
//!   early. The insertion point and `document.write` are not modelled.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §13.2.3.5 Preprocessing the input stream
// ---------------------------------------------------------------------

/// §13.2.3.5: "the input stream must be preprocessed by normalizing
/// newlines" (Infra §4.6, "normalize newlines": "replace every U+000D CR
/// U+000A LF code point pair with a single U+000A LF code point, and then
/// replace every remaining U+000D CR code point with a U+000A LF code
/// point"). The other sentences of the section name parse errors only.
pub open spec fn preprocess(input: Seq<u32>) -> Seq<u32>
    decreases input.len(),
{
    if input.len() == 0 {
        seq![]
    } else if input[0] == 0x0D && input.len() >= 2 && input[1] == 0x0A {
        // A CR LF pair: one LF.
        seq![0x0Au32] + preprocess(input.subrange(2, input.len() as int))
    } else if input[0] == 0x0D {
        // A remaining CR: LF.
        seq![0x0Au32] + preprocess(input.subrange(1, input.len() as int))
    } else {
        seq![input[0]] + preprocess(input.subrange(1, input.len() as int))
    }
}

// ---------------------------------------------------------------------
// §13.2.5 Tokens
// ---------------------------------------------------------------------

/// An attribute of a tag token: "a name and a value".
pub struct Attribute {
    /// name
    pub name: Seq<u32>,
    /// value
    pub value: Seq<u32>,
}

/// A token (§13.2.5: "DOCTYPE, start tag, end tag, comment, character,
/// end-of-file", and §13.2.5.73's processing instruction token).
pub enum Token {
    /// "DOCTYPE tokens have a name, a public identifier, a system
    /// identifier, and a force-quirks flag." `None` is "missing".
    Doctype {
        /// name
        name: Option<Seq<u32>>,
        /// public identifier
        public_identifier: Option<Seq<u32>>,
        /// system identifier
        system_identifier: Option<Seq<u32>>,
        /// force-quirks flag (`true` is "on")
        force_quirks: bool,
    },
    /// A start tag: "a tag name, a self-closing flag, and a list of
    /// attributes".
    StartTag {
        /// tag name
        tag_name: Seq<u32>,
        /// self-closing flag (`true` is "set")
        self_closing: bool,
        /// list of attributes
        attributes: Seq<Attribute>,
    },
    /// An end tag, with the same fields.
    EndTag {
        /// tag name
        tag_name: Seq<u32>,
        /// self-closing flag
        self_closing: bool,
        /// list of attributes
        attributes: Seq<Attribute>,
    },
    /// "Comment and character tokens have data."
    Comment {
        /// data
        data: Seq<u32>,
    },
    /// A processing instruction token: a target and data (§13.2.5.73).
    ProcessingInstruction {
        /// target
        target: Seq<u32>,
        /// data
        data: Seq<u32>,
    },
    /// A character token, one code point (its data).
    Character(u32),
    /// The end-of-file token.
    EndOfFile,
}

// ---------------------------------------------------------------------
// §13.2.5 The states
// ---------------------------------------------------------------------

/// The 84 states of §13.2.5, in the standard's order.
pub enum State {
    /// §13.2.5.1
    Data,
    /// §13.2.5.2
    Rcdata,
    /// §13.2.5.3
    Rawtext,
    /// §13.2.5.4
    ScriptData,
    /// §13.2.5.5
    Plaintext,
    /// §13.2.5.6
    TagOpen,
    /// §13.2.5.7
    EndTagOpen,
    /// §13.2.5.8
    TagName,
    /// §13.2.5.9
    RcdataLessThanSign,
    /// §13.2.5.10
    RcdataEndTagOpen,
    /// §13.2.5.11
    RcdataEndTagName,
    /// §13.2.5.12
    RawtextLessThanSign,
    /// §13.2.5.13
    RawtextEndTagOpen,
    /// §13.2.5.14
    RawtextEndTagName,
    /// §13.2.5.15
    ScriptDataLessThanSign,
    /// §13.2.5.16
    ScriptDataEndTagOpen,
    /// §13.2.5.17
    ScriptDataEndTagName,
    /// §13.2.5.18
    ScriptDataEscapeStart,
    /// §13.2.5.19
    ScriptDataEscapeStartDash,
    /// §13.2.5.20
    ScriptDataEscaped,
    /// §13.2.5.21
    ScriptDataEscapedDash,
    /// §13.2.5.22
    ScriptDataEscapedDashDash,
    /// §13.2.5.23
    ScriptDataEscapedLessThanSign,
    /// §13.2.5.24
    ScriptDataEscapedEndTagOpen,
    /// §13.2.5.25
    ScriptDataEscapedEndTagName,
    /// §13.2.5.26
    ScriptDataDoubleEscapeStart,
    /// §13.2.5.27
    ScriptDataDoubleEscaped,
    /// §13.2.5.28
    ScriptDataDoubleEscapedDash,
    /// §13.2.5.29
    ScriptDataDoubleEscapedDashDash,
    /// §13.2.5.30
    ScriptDataDoubleEscapedLessThanSign,
    /// §13.2.5.31
    ScriptDataDoubleEscapeEnd,
    /// §13.2.5.32
    BeforeAttributeName,
    /// §13.2.5.33
    AttributeName,
    /// §13.2.5.34
    AfterAttributeName,
    /// §13.2.5.35
    BeforeAttributeValue,
    /// §13.2.5.36
    AttributeValueDoubleQuoted,
    /// §13.2.5.37
    AttributeValueSingleQuoted,
    /// §13.2.5.38
    AttributeValueUnquoted,
    /// §13.2.5.39
    AfterAttributeValueQuoted,
    /// §13.2.5.40
    SelfClosingStartTag,
    /// §13.2.5.41
    BogusComment,
    /// §13.2.5.42
    MarkupDeclarationOpen,
    /// §13.2.5.43
    CommentStart,
    /// §13.2.5.44
    CommentStartDash,
    /// §13.2.5.45
    Comment,
    /// §13.2.5.46
    CommentLessThanSign,
    /// §13.2.5.47
    CommentLessThanSignBang,
    /// §13.2.5.48
    CommentLessThanSignBangDash,
    /// §13.2.5.49
    CommentLessThanSignBangDashDash,
    /// §13.2.5.50
    CommentEndDash,
    /// §13.2.5.51
    CommentEnd,
    /// §13.2.5.52
    CommentEndBang,
    /// §13.2.5.53
    Doctype,
    /// §13.2.5.54
    BeforeDoctypeName,
    /// §13.2.5.55
    DoctypeName,
    /// §13.2.5.56
    AfterDoctypeName,
    /// §13.2.5.57
    AfterDoctypePublicKeyword,
    /// §13.2.5.58
    BeforeDoctypePublicIdentifier,
    /// §13.2.5.59
    DoctypePublicIdentifierDoubleQuoted,
    /// §13.2.5.60
    DoctypePublicIdentifierSingleQuoted,
    /// §13.2.5.61
    AfterDoctypePublicIdentifier,
    /// §13.2.5.62
    BetweenDoctypePublicAndSystemIdentifiers,
    /// §13.2.5.63
    AfterDoctypeSystemKeyword,
    /// §13.2.5.64
    BeforeDoctypeSystemIdentifier,
    /// §13.2.5.65
    DoctypeSystemIdentifierDoubleQuoted,
    /// §13.2.5.66
    DoctypeSystemIdentifierSingleQuoted,
    /// §13.2.5.67
    AfterDoctypeSystemIdentifier,
    /// §13.2.5.68
    BogusDoctype,
    /// §13.2.5.69
    CdataSection,
    /// §13.2.5.70
    CdataSectionBracket,
    /// §13.2.5.71
    CdataSectionEnd,
    /// §13.2.5.72
    ProcessingInstructionOpen,
    /// §13.2.5.73
    ProcessingInstructionTarget,
    /// §13.2.5.74
    AfterProcessingInstructionTarget,
    /// §13.2.5.75
    ProcessingInstructionData,
    /// §13.2.5.76
    ProcessingInstructionQuestionable,
    /// §13.2.5.77
    CharacterReference,
    /// §13.2.5.78
    NamedCharacterReference,
    /// §13.2.5.79
    AmbiguousAmpersand,
    /// §13.2.5.80
    NumericCharacterReference,
    /// §13.2.5.81
    HexadecimalCharacterReferenceStart,
    /// §13.2.5.82
    HexadecimalCharacterReference,
    /// §13.2.5.83
    DecimalCharacterReference,
    /// §13.2.5.84
    NumericCharacterReferenceEnd,
}

/// The states the return state is ever set to (see the header).
pub enum ReturnState {
    /// the data state
    Data,
    /// the RCDATA state
    Rcdata,
    /// the attribute value (double-quoted) state
    AttributeValueDoubleQuoted,
    /// the attribute value (single-quoted) state
    AttributeValueSingleQuoted,
    /// the attribute value (unquoted) state
    AttributeValueUnquoted,
}

impl ReturnState {
    /// The state "switch to the return state" switches to.
    pub open spec fn state(self) -> State {
        match self {
            ReturnState::Data => State::Data,
            ReturnState::Rcdata => State::Rcdata,
            ReturnState::AttributeValueDoubleQuoted => State::AttributeValueDoubleQuoted,
            ReturnState::AttributeValueSingleQuoted => State::AttributeValueSingleQuoted,
            ReturnState::AttributeValueUnquoted => State::AttributeValueUnquoted,
        }
    }
}

/// Whether the current attribute is on the current tag token (see the
/// header).
pub enum AttributeStatus {
    /// No attribute has been started on the current tag token.
    NoAttribute,
    /// The current attribute is on the token.
    Kept,
    /// The current attribute was removed as a duplicate.
    Removed,
}

/// The tokenizer's state (§13.2.4 and §13.2.5), with the input position.
pub struct Tokenizer {
    /// The state machine's state.
    pub state: State,
    /// "the return state"
    pub return_state: ReturnState,
    /// "the temporary buffer"
    pub temporary_buffer: Seq<u32>,
    /// "the character reference code"
    pub character_reference_code: nat,
    /// The current tag, comment, DOCTYPE or processing instruction token.
    pub current: Token,
    /// "the current attribute" of the current tag token.
    pub current_attribute: Attribute,
    /// Whether the current attribute is on the token.
    pub attribute_status: AttributeStatus,
    /// "the tag name of the last start tag to have been emitted from this
    /// tokenizer", if any.
    pub last_start_tag: Option<Seq<u32>>,
    /// "there is an adjusted current node and it is not an element in the
    /// HTML namespace" (set by the tree builder).
    pub in_foreign_content: bool,
    /// The next input character's position.
    pub pos: nat,
    /// An end-of-file token has been emitted.
    pub done: bool,
}

/// What one call of a state's spec function returns: the tokenizer after
/// it, and the tokens it emitted, in order.
pub type Step = (Tokenizer, Seq<Token>);

/// A comment token with empty data (the "current token" before any token
/// is created; never emitted as such).
pub open spec fn empty_comment() -> Token {
    Token::Comment { data: seq![] }
}

/// An attribute with empty name and value.
pub open spec fn empty_attribute() -> Attribute {
    Attribute { name: seq![], value: seq![] }
}

/// The tokenizer before the first step: in `start_state` (§13.2.5: "The
/// state machine must start in the data state"; tests and the tree builder
/// start it elsewhere), at the start of the input.
pub open spec fn initial(start_state: State, last_start_tag: Option<Seq<u32>>) -> Tokenizer {
    Tokenizer {
        state: start_state,
        return_state: ReturnState::Data,
        temporary_buffer: seq![],
        character_reference_code: 0,
        current: empty_comment(),
        current_attribute: empty_attribute(),
        attribute_status: AttributeStatus::NoAttribute,
        last_start_tag: last_start_tag,
        in_foreign_content: false,
        pos: 0,
        done: false,
    }
}

// ---------------------------------------------------------------------
// Characters and the input
// ---------------------------------------------------------------------

/// The next input character: `None` is EOF.
pub open spec fn next_char(input: Seq<u32>, pos: nat) -> Option<u32> {
    if pos < input.len() {
        Some(input[pos as int])
    } else {
        None
    }
}

/// U+0009 CHARACTER TABULATION, U+000A LINE FEED, U+000C FORM FEED or
/// U+0020 SPACE: the four characters the states list together.
pub open spec fn is_tab_lf_ff_space(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x20
}

/// ASCII upper hex digit: an ASCII digit or U+0041 (A) to U+0046 (F).
pub open spec fn is_ascii_upper_hex_digit(c: u32) -> bool {
    0x41 <= c <= 0x46
}

/// ASCII lower hex digit: U+0061 (a) to U+0066 (f).
pub open spec fn is_ascii_lower_hex_digit(c: u32) -> bool {
    0x61 <= c <= 0x66
}

/// ASCII hex digit: an ASCII digit, upper hex digit or lower hex digit.
pub open spec fn is_ascii_hex_digit(c: u32) -> bool {
    crate::charref::spec::is_ascii_digit(c) || is_ascii_upper_hex_digit(c) || is_ascii_lower_hex_digit(c)
}

/// "the lowercase version of the current input character (add 0x0020 to
/// the character's code point)", for an ASCII upper alpha.
pub open spec fn to_lower(c: u32) -> u32 {
    (c + 0x20) as u32
}

/// ASCII lowercase of one code point (Infra: ASCII upper alpha to lower,
/// others unchanged).
pub open spec fn ascii_lower(c: u32) -> u32 {
    if crate::charref::spec::is_ascii_upper_alpha(c) {
        to_lower(c)
    } else {
        c
    }
}

/// The input from `pos` on starts with `s`, compared ASCII
/// case-insensitively (`s` is lowercase).
pub open spec fn starts_with_ci(input: Seq<u32>, pos: nat, s: Seq<u32>) -> bool {
    pos + s.len() <= input.len() && input.subrange(pos as int, (pos + s.len()) as int).map_values(
        |c: u32| ascii_lower(c),
    ) == s
}

/// The input from `pos` on starts with `s`, exactly.
pub open spec fn starts_with(input: Seq<u32>, pos: nat, s: Seq<u32>) -> bool {
    pos + s.len() <= input.len() && input.subrange(pos as int, (pos + s.len()) as int) == s
}

/// "doctype"
pub open spec fn doctype_lower() -> Seq<u32> {
    seq![0x64u32, 0x6F, 0x63, 0x74, 0x79, 0x70, 0x65]
}

/// "[CDATA["
pub open spec fn cdata_open() -> Seq<u32> {
    seq![0x5Bu32, 0x43, 0x44, 0x41, 0x54, 0x41, 0x5B]
}

/// "public"
pub open spec fn public_lower() -> Seq<u32> {
    seq![0x70u32, 0x75, 0x62, 0x6C, 0x69, 0x63]
}

/// "system"
pub open spec fn system_lower() -> Seq<u32> {
    seq![0x73u32, 0x79, 0x73, 0x74, 0x65, 0x6D]
}

/// "script"
pub open spec fn script() -> Seq<u32> {
    seq![0x73u32, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "xml"
pub open spec fn xml() -> Seq<u32> {
    seq![0x78u32, 0x6D, 0x6C]
}

/// "xml-stylesheet"
pub open spec fn xml_stylesheet() -> Seq<u32> {
    seq![0x78u32, 0x6D, 0x6C, 0x2D, 0x73, 0x74, 0x79, 0x6C, 0x65, 0x73, 0x68, 0x65, 0x65, 0x74]
}

/// `a` and `b` are ASCII case-insensitive matches (`b` is lowercase).
pub open spec fn eq_ci(a: Seq<u32>, b: Seq<u32>) -> bool {
    a.map_values(|c: u32| ascii_lower(c)) == b
}

// ---------------------------------------------------------------------
// Actions the states share
// ---------------------------------------------------------------------

/// A character token.
pub open spec fn ch(c: u32) -> Token {
    Token::Character(c)
}

/// One character token for each code point of `s`, in order.
pub open spec fn chars(s: Seq<u32>) -> Seq<Token> {
    s.map_values(|c: u32| ch(c))
}

/// The current input character has been consumed: the next one is the
/// one after it.
pub open spec fn consumed(t: Tokenizer) -> Tokenizer {
    Tokenizer { pos: t.pos + 1, ..t }
}

/// "Switch to" (or "reconsume in") the state `s`.
pub open spec fn switch_to(t: Tokenizer, s: State) -> Tokenizer {
    Tokenizer { state: s, ..t }
}

/// "Emit an end-of-file token": the last token.
pub open spec fn emit_eof(t: Tokenizer, before: Seq<Token>) -> Step {
    (Tokenizer { done: true, ..t }, before.push(Token::EndOfFile))
}

/// "Create a new start tag token, set its tag name to the empty string."
pub open spec fn new_start_tag(t: Tokenizer) -> Tokenizer {
    Tokenizer {
        current: Token::StartTag { tag_name: seq![], self_closing: false, attributes: seq![] },
        attribute_status: AttributeStatus::NoAttribute,
        ..t
    }
}

/// "Create a new end tag token, set its tag name to the empty string."
pub open spec fn new_end_tag(t: Tokenizer) -> Tokenizer {
    Tokenizer {
        current: Token::EndTag { tag_name: seq![], self_closing: false, attributes: seq![] },
        attribute_status: AttributeStatus::NoAttribute,
        ..t
    }
}

/// "Append" `c` "to the current tag token's tag name."
pub open spec fn append_to_tag_name(t: Tokenizer, c: u32) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::StartTag { tag_name: name, self_closing, attributes } => Token::StartTag {
                tag_name: name.push(c),
                self_closing,
                attributes,
            },
            Token::EndTag { tag_name: name, self_closing, attributes } => Token::EndTag {
                tag_name: name.push(c),
                self_closing,
                attributes,
            },
            other => other,
        },
        ..t
    }
}

/// "Set the self-closing flag of the current tag token."
pub open spec fn set_self_closing(t: Tokenizer) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::StartTag { tag_name: name, self_closing, attributes } => Token::StartTag {
                tag_name: name,
                self_closing: true,
                attributes,
            },
            Token::EndTag { tag_name: name, self_closing, attributes } => Token::EndTag {
                tag_name: name,
                self_closing: true,
                attributes,
            },
            other => other,
        },
        ..t
    }
}

/// The current tag token's attributes, with the current attribute if it
/// is on the token (see the header).
pub open spec fn attributes_with_current(attributes: Seq<Attribute>, t: Tokenizer) -> Seq<Attribute> {
    if t.attribute_status is Kept {
        attributes.push(t.current_attribute)
    } else {
        attributes
    }
}

/// "Start a new attribute in the current tag token", with name `name` and
/// an empty value: the previous current attribute joins the token's list
/// unless it was removed.
pub open spec fn start_attribute(t: Tokenizer, name: Seq<u32>) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::StartTag { tag_name: n, self_closing, attributes } => Token::StartTag {
                tag_name: n,
                self_closing,
                attributes: attributes_with_current(attributes, t),
            },
            Token::EndTag { tag_name: n, self_closing, attributes } => Token::EndTag {
                tag_name: n,
                self_closing,
                attributes: attributes_with_current(attributes, t),
            },
            other => other,
        },
        current_attribute: Attribute { name: name, value: seq![] },
        attribute_status: AttributeStatus::Kept,
        ..t
    }
}

/// Append `c` to the current attribute's name.
pub open spec fn append_to_attribute_name(t: Tokenizer, c: u32) -> Tokenizer {
    Tokenizer {
        current_attribute: Attribute { name: t.current_attribute.name.push(c), ..t.current_attribute },
        ..t
    }
}

/// Append `s` to the current attribute's value.
pub open spec fn append_to_attribute_value(t: Tokenizer, s: Seq<u32>) -> Tokenizer {
    Tokenizer {
        current_attribute: Attribute { value: t.current_attribute.value + s, ..t.current_attribute },
        ..t
    }
}

/// The current tag token's attributes (without the current attribute).
pub open spec fn tag_attributes(token: Token) -> Seq<Attribute> {
    match token {
        Token::StartTag { attributes, .. } => attributes,
        Token::EndTag { attributes, .. } => attributes,
        _ => seq![],
    }
}

/// §13.2.5.33, after the switch: "When the user agent leaves the attribute
/// name state (and before emitting the tag token, if appropriate), the
/// complete attribute's name must be compared to the other attributes on
/// the same token; if there is already an attribute on the token with the
/// exact same name, then this is a duplicate-attribute parse error and the
/// new attribute must be removed from the token."
pub open spec fn leave_attribute_name(t: Tokenizer) -> Tokenizer {
    if t.attribute_status is Kept && has_attribute_named(tag_attributes(t.current), t.current_attribute.name) {
        Tokenizer { attribute_status: AttributeStatus::Removed, ..t }
    } else {
        t
    }
}

/// One of `attributes` has the name `name`.
pub open spec fn has_attribute_named(attributes: Seq<Attribute>, name: Seq<u32>) -> bool
    decreases attributes.len(),
{
    if attributes.len() == 0 {
        false
    } else {
        attributes.last().name == name || has_attribute_named(attributes.drop_last(), name)
    }
}

/// "Emit the current tag token": with the current attribute if it is on
/// the token; a start tag becomes the last start tag emitted.
pub open spec fn emit_current_tag(t: Tokenizer, before: Seq<Token>) -> Step {
    match t.current {
        Token::StartTag { tag_name: name, self_closing, attributes } => (
            Tokenizer { last_start_tag: Some(name), attribute_status: AttributeStatus::NoAttribute, ..t },
            before.push(
                Token::StartTag { tag_name: name, self_closing, attributes: attributes_with_current(attributes, t) },
            ),
        ),
        Token::EndTag { tag_name: name, self_closing, attributes } => (
            Tokenizer { attribute_status: AttributeStatus::NoAttribute, ..t },
            before.push(
                Token::EndTag { tag_name: name, self_closing, attributes: attributes_with_current(attributes, t) },
            ),
        ),
        other => (t, before.push(other)),
    }
}

/// "Emit the current token" (a comment, DOCTYPE or processing instruction
/// token).
pub open spec fn emit_current(t: Tokenizer, before: Seq<Token>) -> Seq<Token> {
    before.push(t.current)
}

/// §13.2.5: "An appropriate end tag token is an end tag token whose tag
/// name matches the tag name of the last start tag to have been emitted
/// from this tokenizer, if any. If no start tag has been emitted from this
/// tokenizer, then no end tag token is appropriate."
pub open spec fn is_appropriate_end_tag(t: Tokenizer) -> bool {
    match (t.current, t.last_start_tag) {
        (Token::EndTag { tag_name: name, .. }, Some(last)) => name == last,
        _ => false,
    }
}

/// "Create a comment token whose data is" `data`.
pub open spec fn new_comment(t: Tokenizer, data: Seq<u32>) -> Tokenizer {
    Tokenizer { current: Token::Comment { data }, ..t }
}

/// Append `s` to the comment token's data.
pub open spec fn append_to_comment(t: Tokenizer, s: Seq<u32>) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Comment { data } => Token::Comment { data: data + s },
            other => other,
        },
        ..t
    }
}

/// §13.2.5: "To convert the temporary buffer to a comment, create a
/// comment token whose data is the concatenation of "?" and the code
/// points in the temporary buffer, in the order they were added to the
/// buffer."
pub open spec fn convert_temporary_buffer_to_comment(t: Tokenizer) -> Tokenizer {
    new_comment(t, seq![0x3Fu32] + t.temporary_buffer)
}

/// "Create a new DOCTYPE token" (§13.2.5: name, public identifier and
/// system identifier missing, force-quirks off), with name `name`.
pub open spec fn new_doctype(t: Tokenizer, name: Option<Seq<u32>>) -> Tokenizer {
    Tokenizer {
        current: Token::Doctype {
            name: name,
            public_identifier: None,
            system_identifier: None,
            force_quirks: false,
        },
        ..t
    }
}

/// "Set the current DOCTYPE token's force-quirks flag to on."
pub open spec fn set_force_quirks(t: Tokenizer) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name,
                public_identifier,
                system_identifier,
                force_quirks: true,
            },
            other => other,
        },
        ..t
    }
}

/// Append `c` to the current DOCTYPE token's name.
pub open spec fn append_to_doctype_name(t: Tokenizer, c: u32) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name: Some(
                    match name {
                        Some(n) => n.push(c),
                        None => seq![c],
                    },
                ),
                public_identifier,
                system_identifier,
                force_quirks,
            },
            other => other,
        },
        ..t
    }
}

/// "Set the current DOCTYPE token's public identifier to the empty string
/// (not missing)."
pub open spec fn set_public_identifier_empty(t: Tokenizer) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name,
                public_identifier: Some(seq![]),
                system_identifier,
                force_quirks,
            },
            other => other,
        },
        ..t
    }
}

/// Append `c` to the current DOCTYPE token's public identifier.
pub open spec fn append_to_public_identifier(t: Tokenizer, c: u32) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name,
                public_identifier: Some(
                    match public_identifier {
                        Some(p) => p.push(c),
                        None => seq![c],
                    },
                ),
                system_identifier,
                force_quirks,
            },
            other => other,
        },
        ..t
    }
}

/// "Set the current DOCTYPE token's system identifier to the empty string
/// (not missing)."
pub open spec fn set_system_identifier_empty(t: Tokenizer) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name,
                public_identifier,
                system_identifier: Some(seq![]),
                force_quirks,
            },
            other => other,
        },
        ..t
    }
}

/// Append `c` to the current DOCTYPE token's system identifier.
pub open spec fn append_to_system_identifier(t: Tokenizer, c: u32) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::Doctype { name, public_identifier, system_identifier, force_quirks } => Token::Doctype {
                name,
                public_identifier,
                system_identifier: Some(
                    match system_identifier {
                        Some(s) => s.push(c),
                        None => seq![c],
                    },
                ),
                force_quirks,
            },
            other => other,
        },
        ..t
    }
}

/// Append `s` to the current processing instruction token's data.
pub open spec fn append_to_pi_data(t: Tokenizer, s: Seq<u32>) -> Tokenizer {
    Tokenizer {
        current: match t.current {
            Token::ProcessingInstruction { target, data } => Token::ProcessingInstruction {
                target,
                data: data + s,
            },
            other => other,
        },
        ..t
    }
}

/// §13.2.5: "A character reference is said to be consumed as part of an
/// attribute if the return state is either attribute value (double-quoted)
/// state, attribute value (single-quoted) state, or attribute value
/// (unquoted) state."
pub open spec fn consumed_as_part_of_attribute(t: Tokenizer) -> bool {
    !(t.return_state is Data || t.return_state is Rcdata)
}

/// §13.2.5: "When a state says to flush code points consumed as a
/// character reference, it means that for each code point in the temporary
/// buffer (in the order they were added to the buffer), the user agent
/// must append the code point from the buffer to the current attribute's
/// value if the character reference was consumed as part of an attribute,
/// or emit the code point as a character token otherwise."
pub open spec fn flush(t: Tokenizer) -> Step {
    if consumed_as_part_of_attribute(t) {
        (append_to_attribute_value(t, t.temporary_buffer), seq![])
    } else {
        (t, chars(t.temporary_buffer))
    }
}

/// A step that emits nothing.
pub open spec fn none(t: Tokenizer) -> Step {
    (t, seq![])
}

/// A step that emits one token.
pub open spec fn one(t: Tokenizer, token: Token) -> Step {
    (t, seq![token])
}

/// A step that emits two tokens.
pub open spec fn two(t: Tokenizer, a: Token, b: Token) -> Step {
    (t, seq![a, b])
}

// ---------------------------------------------------------------------
// §13.2.5.1 to §13.2.5.31: data, RCDATA, RAWTEXT, script data, PLAINTEXT
// and tags
// ---------------------------------------------------------------------

/// §13.2.5.1 Data state.
pub open spec fn data_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // "Consume the next input character:"
    match next_char(input, t.pos) {
        // EOF: "Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x26 {
                // U+0026 AMPERSAND (&): "Set the return state to the data
                // state. Switch to the character reference state."
                none(switch_to(Tokenizer { return_state: ReturnState::Data, ..n }, State::CharacterReference))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the tag open state."
                none(switch_to(n, State::TagOpen))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit the current input character as a character
                // token."
                one(n, ch(c))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.2 RCDATA state.
pub open spec fn rcdata_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x26 {
                // U+0026 AMPERSAND (&): "Set the return state to the RCDATA
                // state. Switch to the character reference state."
                none(switch_to(Tokenizer { return_state: ReturnState::Rcdata, ..n }, State::CharacterReference))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the RCDATA less-than
                // sign state."
                none(switch_to(n, State::RcdataLessThanSign))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit a U+FFFD REPLACEMENT CHARACTER character
                // token."
                one(n, ch(0xFFFD))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.3 RAWTEXT state.
pub open spec fn rawtext_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the RAWTEXT less-than
                // sign state."
                none(switch_to(n, State::RawtextLessThanSign))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit a U+FFFD REPLACEMENT CHARACTER character
                // token."
                one(n, ch(0xFFFD))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.4 Script data state.
pub open spec fn script_data_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // less-than sign state."
                none(switch_to(n, State::ScriptDataLessThanSign))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit a U+FFFD REPLACEMENT CHARACTER character
                // token."
                one(n, ch(0xFFFD))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.5 PLAINTEXT state.
pub open spec fn plaintext_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit a U+FFFD REPLACEMENT CHARACTER character
                // token."
                one(n, ch(0xFFFD))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.6 Tag open state.
pub open spec fn tag_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-before-tag-name parse error. Emit a U+003C
        // LESS-THAN SIGN character token and an end-of-file token."
        None => emit_eof(t, seq![ch(0x3C)]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x21 {
                // U+0021 EXCLAMATION MARK (!): "Switch to the markup
                // declaration open state."
                none(switch_to(n, State::MarkupDeclarationOpen))
            } else if c == 0x2F {
                // U+002F SOLIDUS (/): "Switch to the end tag open state."
                none(switch_to(n, State::EndTagOpen))
            } else if crate::charref::spec::is_ascii_alpha(c) {
                // ASCII alpha: "Create a new start tag token, set its tag
                // name to the empty string. Reconsume in the tag name state."
                none(switch_to(new_start_tag(t), State::TagName))
            } else if c == 0x3F {
                // U+003F QUESTION MARK (?): "Set the temporary buffer to the
                // empty string. Switch to the processing instruction open
                // state."
                none(switch_to(Tokenizer { temporary_buffer: seq![], ..n }, State::ProcessingInstructionOpen))
            } else {
                // Anything else: "This is an
                // invalid-first-character-of-tag-name parse error. Emit a
                // U+003C LESS-THAN SIGN character token. Reconsume in the
                // data state."
                one(switch_to(t, State::Data), ch(0x3C))
            }
        },
    }
}

/// §13.2.5.7 End tag open state.
pub open spec fn end_tag_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-before-tag-name parse error. Emit a U+003C
        // LESS-THAN SIGN character token, a U+002F SOLIDUS character token
        // and an end-of-file token."
        None => emit_eof(t, seq![ch(0x3C), ch(0x2F)]),
        Some(c) => {
            let n = consumed(t);
            if crate::charref::spec::is_ascii_alpha(c) {
                // ASCII alpha: "Create a new end tag token, set its tag name
                // to the empty string. Reconsume in the tag name state."
                none(switch_to(new_end_tag(t), State::TagName))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is a
                // missing-end-tag-name parse error. Switch to the data
                // state."
                none(switch_to(n, State::Data))
            } else {
                // Anything else: "This is an
                // invalid-first-character-of-tag-name parse error. Create a
                // comment token whose data is the empty string. Reconsume in
                // the bogus comment state."
                none(switch_to(new_comment(t, seq![]), State::BogusComment))
            }
        },
    }
}

/// §13.2.5.8 Tag name state.
pub open spec fn tag_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-tag parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the before attribute name
                // state."
                none(switch_to(n, State::BeforeAttributeName))
            } else if c == 0x2F {
                // U+002F SOLIDUS (/): "Switch to the self-closing start tag
                // state."
                none(switch_to(n, State::SelfClosingStartTag))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state.
                // Emit the current tag token."
                emit_current_tag(switch_to(n, State::Data), seq![])
            } else if crate::charref::spec::is_ascii_upper_alpha(c) {
                // ASCII upper alpha: "Append the lowercase version of the
                // current input character (add 0x0020 to the character's
                // code point) to the current tag token's tag name."
                none(append_to_tag_name(n, to_lower(c)))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to
                // the current tag token's tag name."
                none(append_to_tag_name(n, 0xFFFD))
            } else {
                // Anything else: "Append the current input character to the
                // current tag token's tag name."
                none(append_to_tag_name(n, c))
            }
        },
    }
}

/// The "less-than sign" states of RCDATA and RAWTEXT (§13.2.5.9 and
/// §13.2.5.12), which differ only in their states.
pub open spec fn text_less_than_sign_state(input: Seq<u32>, t: Tokenizer, text: State, end_tag_open: State) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2F => {
            // U+002F SOLIDUS (/): "Set the temporary buffer to the empty
            // string. Switch to the [RCDATA|RAWTEXT] end tag open state."
            none(switch_to(Tokenizer { temporary_buffer: seq![], ..consumed(t) }, end_tag_open))
        },
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the [RCDATA|RAWTEXT] state."
        _ => one(switch_to(t, text), ch(0x3C)),
    }
}

/// The "end tag open" states of RCDATA, RAWTEXT, script data and script
/// data escaped (§13.2.5.10, §13.2.5.13, §13.2.5.16, §13.2.5.24), which
/// differ only in their states.
pub open spec fn text_end_tag_open_state(input: Seq<u32>, t: Tokenizer, text: State, end_tag_name: State) -> Step {
    match next_char(input, t.pos) {
        Some(c) if crate::charref::spec::is_ascii_alpha(c) => {
            // ASCII alpha: "Create a new end tag token, set its tag name to
            // the empty string. Reconsume in the [...] end tag name state."
            none(switch_to(new_end_tag(t), end_tag_name))
        },
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token and a
        // U+002F SOLIDUS character token. Reconsume in the [...] state."
        _ => two(switch_to(t, text), ch(0x3C), ch(0x2F)),
    }
}

/// The "end tag name" states of RCDATA, RAWTEXT, script data and script
/// data escaped (§13.2.5.11, §13.2.5.14, §13.2.5.17, §13.2.5.25), which
/// differ only in the state "anything else" reconsumes in.
pub open spec fn text_end_tag_name_state(input: Seq<u32>, t: Tokenizer, text: State) -> Step {
    // Anything else: "Emit a U+003C LESS-THAN SIGN character token, a
    // U+002F SOLIDUS character token, and a character token for each of the
    // characters in the temporary buffer (in the order they were added to
    // the buffer). Reconsume in the [...] state."
    let anything_else = (switch_to(t, text), seq![ch(0x3C), ch(0x2F)] + chars(t.temporary_buffer));
    match next_char(input, t.pos) {
        None => anything_else,
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "If the current end tag token is an
                // appropriate end tag token, then switch to the before
                // attribute name state. Otherwise, treat it as per the
                // "anything else" entry below."
                if is_appropriate_end_tag(t) {
                    none(switch_to(n, State::BeforeAttributeName))
                } else {
                    anything_else
                }
            } else if c == 0x2F {
                // U+002F SOLIDUS (/): "If the current end tag token is an
                // appropriate end tag token, then switch to the self-closing
                // start tag state. Otherwise, treat it as per the "anything
                // else" entry below."
                if is_appropriate_end_tag(t) {
                    none(switch_to(n, State::SelfClosingStartTag))
                } else {
                    anything_else
                }
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "If the current end tag token
                // is an appropriate end tag token, then switch to the data
                // state and emit the current tag token. Otherwise, treat it
                // as per the "anything else" entry below."
                if is_appropriate_end_tag(t) {
                    emit_current_tag(switch_to(n, State::Data), seq![])
                } else {
                    anything_else
                }
            } else if crate::charref::spec::is_ascii_upper_alpha(c) {
                // ASCII upper alpha: "Append the lowercase version of the
                // current input character (add 0x0020 to the character's
                // code point) to the current tag token's tag name. Append
                // the current input character to the temporary buffer."
                none(
                    Tokenizer {
                        temporary_buffer: t.temporary_buffer.push(c),
                        ..append_to_tag_name(n, to_lower(c))
                    },
                )
            } else if crate::charref::spec::is_ascii_lower_alpha(c) {
                // ASCII lower alpha: "Append the current input character to
                // the current tag token's tag name. Append the current input
                // character to the temporary buffer."
                none(Tokenizer { temporary_buffer: t.temporary_buffer.push(c), ..append_to_tag_name(n, c) })
            } else {
                anything_else
            }
        },
    }
}

/// §13.2.5.9 RCDATA less-than sign state.
pub open spec fn rcdata_less_than_sign_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_less_than_sign_state(input, t, State::Rcdata, State::RcdataEndTagOpen)
}

/// §13.2.5.10 RCDATA end tag open state.
pub open spec fn rcdata_end_tag_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_open_state(input, t, State::Rcdata, State::RcdataEndTagName)
}

/// §13.2.5.11 RCDATA end tag name state.
pub open spec fn rcdata_end_tag_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_name_state(input, t, State::Rcdata)
}

/// §13.2.5.12 RAWTEXT less-than sign state.
pub open spec fn rawtext_less_than_sign_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_less_than_sign_state(input, t, State::Rawtext, State::RawtextEndTagOpen)
}

/// §13.2.5.13 RAWTEXT end tag open state.
pub open spec fn rawtext_end_tag_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_open_state(input, t, State::Rawtext, State::RawtextEndTagName)
}

/// §13.2.5.14 RAWTEXT end tag name state.
pub open spec fn rawtext_end_tag_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_name_state(input, t, State::Rawtext)
}

/// §13.2.5.15 Script data less-than sign state.
pub open spec fn script_data_less_than_sign_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2F => {
            // U+002F SOLIDUS (/): "Set the temporary buffer to the empty
            // string. Switch to the script data end tag open state."
            none(switch_to(Tokenizer { temporary_buffer: seq![], ..consumed(t) }, State::ScriptDataEndTagOpen))
        },
        Some(c) if c == 0x21 => {
            // U+0021 EXCLAMATION MARK (!): "Switch to the script data escape
            // start state. Emit a U+003C LESS-THAN SIGN character token and a
            // U+0021 EXCLAMATION MARK character token."
            two(switch_to(consumed(t), State::ScriptDataEscapeStart), ch(0x3C), ch(0x21))
        },
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the script data state."
        _ => one(switch_to(t, State::ScriptData), ch(0x3C)),
    }
}

/// §13.2.5.16 Script data end tag open state.
pub open spec fn script_data_end_tag_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_open_state(input, t, State::ScriptData, State::ScriptDataEndTagName)
}

/// §13.2.5.17 Script data end tag name state.
pub open spec fn script_data_end_tag_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_name_state(input, t, State::ScriptData)
}

/// §13.2.5.18 Script data escape start state.
pub open spec fn script_data_escape_start_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2D => {
            // U+002D HYPHEN-MINUS (-): "Switch to the script data escape
            // start dash state. Emit a U+002D HYPHEN-MINUS character token."
            one(switch_to(consumed(t), State::ScriptDataEscapeStartDash), ch(0x2D))
        },
        // Anything else: "Reconsume in the script data state."
        _ => none(switch_to(t, State::ScriptData)),
    }
}

/// §13.2.5.19 Script data escape start dash state.
pub open spec fn script_data_escape_start_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2D => {
            // U+002D HYPHEN-MINUS (-): "Switch to the script data escaped
            // dash dash state. Emit a U+002D HYPHEN-MINUS character token."
            one(switch_to(consumed(t), State::ScriptDataEscapedDashDash), ch(0x2D))
        },
        // Anything else: "Reconsume in the script data state."
        _ => none(switch_to(t, State::ScriptData)),
    }
}

/// §13.2.5.20 Script data escaped state.
pub open spec fn script_data_escaped_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-script-html-comment-like-text parse error.
        // Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the script data escaped
                // dash state. Emit a U+002D HYPHEN-MINUS character token."
                one(switch_to(n, State::ScriptDataEscapedDash), ch(0x2D))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // escaped less-than sign state."
                none(switch_to(n, State::ScriptDataEscapedLessThanSign))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit a U+FFFD REPLACEMENT CHARACTER character token."
                one(n, ch(0xFFFD))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.21 Script data escaped dash state.
pub open spec fn script_data_escaped_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-script-html-comment-like-text parse error.
        // Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the script data escaped
                // dash dash state. Emit a U+002D HYPHEN-MINUS character
                // token."
                one(switch_to(n, State::ScriptDataEscapedDashDash), ch(0x2D))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // escaped less-than sign state."
                none(switch_to(n, State::ScriptDataEscapedLessThanSign))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Switch to the script data escaped state. Emit a
                // U+FFFD REPLACEMENT CHARACTER character token."
                one(switch_to(n, State::ScriptDataEscaped), ch(0xFFFD))
            } else {
                // Anything else: "Switch to the script data escaped state.
                // Emit the current input character as a character token."
                one(switch_to(n, State::ScriptDataEscaped), ch(c))
            }
        },
    }
}

/// §13.2.5.22 Script data escaped dash dash state.
pub open spec fn script_data_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-script-html-comment-like-text parse error.
        // Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Emit a U+002D HYPHEN-MINUS
                // character token."
                one(n, ch(0x2D))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // escaped less-than sign state."
                none(switch_to(n, State::ScriptDataEscapedLessThanSign))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the script data
                // state. Emit a U+003E GREATER-THAN SIGN character token."
                one(switch_to(n, State::ScriptData), ch(0x3E))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Switch to the script data escaped state. Emit a
                // U+FFFD REPLACEMENT CHARACTER character token."
                one(switch_to(n, State::ScriptDataEscaped), ch(0xFFFD))
            } else {
                // Anything else: "Switch to the script data escaped state.
                // Emit the current input character as a character token."
                one(switch_to(n, State::ScriptDataEscaped), ch(c))
            }
        },
    }
}

/// §13.2.5.23 Script data escaped less-than sign state.
pub open spec fn script_data_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2F => {
            // U+002F SOLIDUS (/): "Set the temporary buffer to the empty
            // string. Switch to the script data escaped end tag open state."
            none(
                switch_to(Tokenizer { temporary_buffer: seq![], ..consumed(t) }, State::ScriptDataEscapedEndTagOpen),
            )
        },
        Some(c) if crate::charref::spec::is_ascii_alpha(c) => {
            // ASCII alpha: "Set the temporary buffer to the empty string.
            // Emit a U+003C LESS-THAN SIGN character token. Reconsume in the
            // script data double escape start state."
            one(switch_to(Tokenizer { temporary_buffer: seq![], ..t }, State::ScriptDataDoubleEscapeStart), ch(0x3C))
        },
        // Anything else: "Emit a U+003C LESS-THAN SIGN character token.
        // Reconsume in the script data escaped state."
        _ => one(switch_to(t, State::ScriptDataEscaped), ch(0x3C)),
    }
}

/// §13.2.5.24 Script data escaped end tag open state.
pub open spec fn script_data_escaped_end_tag_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_open_state(input, t, State::ScriptDataEscaped, State::ScriptDataEscapedEndTagName)
}

/// §13.2.5.25 Script data escaped end tag name state.
pub open spec fn script_data_escaped_end_tag_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    text_end_tag_name_state(input, t, State::ScriptDataEscaped)
}

/// The script data double escape start and end states (§13.2.5.26 and
/// §13.2.5.31), which differ only in the states they switch to: `if_script`
/// when the temporary buffer is "script", `otherwise` when not, and
/// `anything_else` for other characters.
pub open spec fn double_escape_boundary_state(
    input: Seq<u32>,
    t: Tokenizer,
    if_script: State,
    otherwise: State,
    anything_else: State,
) -> Step {
    match next_char(input, t.pos) {
        Some(c) if is_tab_lf_ff_space(c) || c == 0x2F || c == 0x3E => {
            // tab, LF, FF, space, U+002F SOLIDUS (/), U+003E GREATER-THAN
            // SIGN (>): "If the temporary buffer is "script", then switch to
            // the [...] state. Otherwise, switch to the [...] state. Emit the
            // current input character as a character token."
            one(
                switch_to(consumed(t), if t.temporary_buffer == script() { if_script } else { otherwise }),
                ch(c),
            )
        },
        Some(c) if crate::charref::spec::is_ascii_upper_alpha(c) => {
            // ASCII upper alpha: "Append the lowercase version of the
            // current input character (add 0x0020 to the character's code
            // point) to the temporary buffer. Emit the current input
            // character as a character token."
            one(Tokenizer { temporary_buffer: t.temporary_buffer.push(to_lower(c)), ..consumed(t) }, ch(c))
        },
        Some(c) if crate::charref::spec::is_ascii_lower_alpha(c) => {
            // ASCII lower alpha: "Append the current input character to the
            // temporary buffer. Emit the current input character as a
            // character token."
            one(Tokenizer { temporary_buffer: t.temporary_buffer.push(c), ..consumed(t) }, ch(c))
        },
        // Anything else: "Reconsume in the [...] state."
        _ => none(switch_to(t, anything_else)),
    }
}

/// §13.2.5.26 Script data double escape start state.
pub open spec fn script_data_double_escape_start_state(input: Seq<u32>, t: Tokenizer) -> Step {
    double_escape_boundary_state(
        input,
        t,
        State::ScriptDataDoubleEscaped,
        State::ScriptDataEscaped,
        State::ScriptDataEscaped,
    )
}

/// §13.2.5.27 Script data double escaped state.
pub open spec fn script_data_double_escaped_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-script-html-comment-like-text parse error.
        // Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the script data double
                // escaped dash state. Emit a U+002D HYPHEN-MINUS character
                // token."
                one(switch_to(n, State::ScriptDataDoubleEscapedDash), ch(0x2D))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // double escaped less-than sign state. Emit a U+003C
                // LESS-THAN SIGN character token."
                one(switch_to(n, State::ScriptDataDoubleEscapedLessThanSign), ch(0x3C))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Emit a U+FFFD REPLACEMENT CHARACTER character token."
                one(n, ch(0xFFFD))
            } else {
                // Anything else: "Emit the current input character as a
                // character token."
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.28 Script data double escaped dash state.
pub open spec fn script_data_double_escaped_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-script-html-comment-like-text parse error.
        // Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the script data double
                // escaped dash dash state. Emit a U+002D HYPHEN-MINUS
                // character token."
                one(switch_to(n, State::ScriptDataDoubleEscapedDashDash), ch(0x2D))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // double escaped less-than sign state. Emit a U+003C
                // LESS-THAN SIGN character token."
                one(switch_to(n, State::ScriptDataDoubleEscapedLessThanSign), ch(0x3C))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Switch to the script data double escaped state. Emit
                // a U+FFFD REPLACEMENT CHARACTER character token."
                one(switch_to(n, State::ScriptDataDoubleEscaped), ch(0xFFFD))
            } else {
                // Anything else: "Switch to the script data double escaped
                // state. Emit the current input character as a character
                // token."
                one(switch_to(n, State::ScriptDataDoubleEscaped), ch(c))
            }
        },
    }
}

/// §13.2.5.29 Script data double escaped dash dash state.
pub open spec fn script_data_double_escaped_dash_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-script-html-comment-like-text parse error.
        // Emit an end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Emit a U+002D HYPHEN-MINUS
                // character token."
                one(n, ch(0x2D))
            } else if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Switch to the script data
                // double escaped less-than sign state. Emit a U+003C
                // LESS-THAN SIGN character token."
                one(switch_to(n, State::ScriptDataDoubleEscapedLessThanSign), ch(0x3C))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the script data
                // state. Emit a U+003E GREATER-THAN SIGN character token."
                one(switch_to(n, State::ScriptData), ch(0x3E))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Switch to the script data double escaped state. Emit
                // a U+FFFD REPLACEMENT CHARACTER character token."
                one(switch_to(n, State::ScriptDataDoubleEscaped), ch(0xFFFD))
            } else {
                // Anything else: "Switch to the script data double escaped
                // state. Emit the current input character as a character
                // token."
                one(switch_to(n, State::ScriptDataDoubleEscaped), ch(c))
            }
        },
    }
}

/// §13.2.5.30 Script data double escaped less-than sign state.
pub open spec fn script_data_double_escaped_less_than_sign_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2F => {
            // U+002F SOLIDUS (/): "Set the temporary buffer to the empty
            // string. Switch to the script data double escape end state.
            // Emit a U+002F SOLIDUS character token."
            one(
                switch_to(Tokenizer { temporary_buffer: seq![], ..consumed(t) }, State::ScriptDataDoubleEscapeEnd),
                ch(0x2F),
            )
        },
        // Anything else: "Reconsume in the script data double escaped
        // state."
        _ => none(switch_to(t, State::ScriptDataDoubleEscaped)),
    }
}

/// §13.2.5.31 Script data double escape end state.
pub open spec fn script_data_double_escape_end_state(input: Seq<u32>, t: Tokenizer) -> Step {
    double_escape_boundary_state(
        input,
        t,
        State::ScriptDataEscaped,
        State::ScriptDataDoubleEscaped,
        State::ScriptDataDoubleEscaped,
    )
}

// ---------------------------------------------------------------------
// §13.2.5.32 to §13.2.5.40: attributes
// ---------------------------------------------------------------------

/// §13.2.5.32 Before attribute name state.
pub open spec fn before_attribute_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Reconsume in the after attribute name state."
        None => none(switch_to(t, State::AfterAttributeName)),
        Some(c) => {
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(consumed(t))
            } else if c == 0x2F || c == 0x3E {
                // U+002F SOLIDUS (/), U+003E GREATER-THAN SIGN (>): "Reconsume
                // in the after attribute name state."
                none(switch_to(t, State::AfterAttributeName))
            } else if c == 0x3D {
                // U+003D EQUALS SIGN (=): "This is an
                // unexpected-equals-sign-before-attribute-name parse error.
                // Start a new attribute in the current tag token. Set that
                // attribute's name to the current input character, and its
                // value to the empty string. Switch to the attribute name
                // state."
                none(switch_to(start_attribute(consumed(t), seq![c]), State::AttributeName))
            } else {
                // Anything else: "Start a new attribute in the current tag
                // token. Set that attribute name and value to the empty
                // string. Reconsume in the attribute name state."
                none(switch_to(start_attribute(t, seq![]), State::AttributeName))
            }
        },
    }
}

/// §13.2.5.33 Attribute name state. Leaving it runs
/// [`leave_attribute_name`] (the paragraph after the switch).
pub open spec fn attribute_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Reconsume in the after attribute name state."
        None => none(switch_to(leave_attribute_name(t), State::AfterAttributeName)),
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) || c == 0x2F || c == 0x3E {
                // tab, LF, FF, space, U+002F SOLIDUS (/), U+003E GREATER-THAN
                // SIGN (>): "Reconsume in the after attribute name state."
                none(switch_to(leave_attribute_name(t), State::AfterAttributeName))
            } else if c == 0x3D {
                // U+003D EQUALS SIGN (=): "Switch to the before attribute
                // value state."
                none(switch_to(leave_attribute_name(n), State::BeforeAttributeValue))
            } else if crate::charref::spec::is_ascii_upper_alpha(c) {
                // ASCII upper alpha: "Append the lowercase version of the
                // current input character (add 0x0020 to the character's
                // code point) to the current attribute's name."
                none(append_to_attribute_name(n, to_lower(c)))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to
                // the current attribute's name."
                none(append_to_attribute_name(n, 0xFFFD))
            } else {
                // U+0022 QUOTATION MARK ("), U+0027 APOSTROPHE ('), U+003C
                // LESS-THAN SIGN (<): "This is an
                // unexpected-character-in-attribute-name parse error. Treat it
                // as per the "anything else" entry below."
                // Anything else: "Append the current input character to the
                // current attribute's name."
                none(append_to_attribute_name(n, c))
            }
        },
    }
}

/// §13.2.5.34 After attribute name state.
pub open spec fn after_attribute_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-tag parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(n)
            } else if c == 0x2F {
                // U+002F SOLIDUS (/): "Switch to the self-closing start tag
                // state."
                none(switch_to(n, State::SelfClosingStartTag))
            } else if c == 0x3D {
                // U+003D EQUALS SIGN (=): "Switch to the before attribute
                // value state."
                none(switch_to(n, State::BeforeAttributeValue))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state.
                // Emit the current tag token."
                emit_current_tag(switch_to(n, State::Data), seq![])
            } else {
                // Anything else: "Start a new attribute in the current tag
                // token. Set that attribute name and value to the empty
                // string. Reconsume in the attribute name state."
                none(switch_to(start_attribute(t, seq![]), State::AttributeName))
            }
        },
    }
}

/// §13.2.5.35 Before attribute value state.
pub open spec fn before_attribute_value_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if is_tab_lf_ff_space(c) => {
            // tab, LF, FF, space: "Ignore the character."
            none(consumed(t))
        },
        Some(c) if c == 0x22 => {
            // U+0022 QUOTATION MARK ("): "Switch to the attribute value
            // (double-quoted) state."
            none(switch_to(consumed(t), State::AttributeValueDoubleQuoted))
        },
        Some(c) if c == 0x27 => {
            // U+0027 APOSTROPHE ('): "Switch to the attribute value
            // (single-quoted) state."
            none(switch_to(consumed(t), State::AttributeValueSingleQuoted))
        },
        Some(c) if c == 0x3E => {
            // U+003E GREATER-THAN SIGN (>): "This is a missing-attribute-value
            // parse error. Switch to the data state. Emit the current tag
            // token."
            emit_current_tag(switch_to(consumed(t), State::Data), seq![])
        },
        // Anything else (EOF too): "Reconsume in the attribute value
        // (unquoted) state."
        _ => none(switch_to(t, State::AttributeValueUnquoted)),
    }
}

/// The quoted attribute value states (§13.2.5.36 and §13.2.5.37), which
/// differ only in the quote that ends them and the return state they set.
pub open spec fn attribute_value_quoted_state(input: Seq<u32>, t: Tokenizer, quote: u32, ret: ReturnState) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-tag parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == quote {
                // U+0022 QUOTATION MARK (") [U+0027 APOSTROPHE (')]: "Switch
                // to the after attribute value (quoted) state."
                none(switch_to(n, State::AfterAttributeValueQuoted))
            } else if c == 0x26 {
                // U+0026 AMPERSAND (&): "Set the return state to the attribute
                // value ([double|single]-quoted) state. Switch to the
                // character reference state."
                none(switch_to(Tokenizer { return_state: ret, ..n }, State::CharacterReference))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to
                // the current attribute's value."
                none(append_to_attribute_value(n, seq![0xFFFDu32]))
            } else {
                // Anything else: "Append the current input character to the
                // current attribute's value."
                none(append_to_attribute_value(n, seq![c]))
            }
        },
    }
}

/// §13.2.5.36 Attribute value (double-quoted) state.
pub open spec fn attribute_value_double_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    attribute_value_quoted_state(input, t, 0x22, ReturnState::AttributeValueDoubleQuoted)
}

/// §13.2.5.37 Attribute value (single-quoted) state.
pub open spec fn attribute_value_single_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    attribute_value_quoted_state(input, t, 0x27, ReturnState::AttributeValueSingleQuoted)
}

/// §13.2.5.38 Attribute value (unquoted) state.
pub open spec fn attribute_value_unquoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-tag parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the before attribute name
                // state."
                none(switch_to(n, State::BeforeAttributeName))
            } else if c == 0x26 {
                // U+0026 AMPERSAND (&): "Set the return state to the attribute
                // value (unquoted) state. Switch to the character reference
                // state."
                none(
                    switch_to(
                        Tokenizer { return_state: ReturnState::AttributeValueUnquoted, ..n },
                        State::CharacterReference,
                    ),
                )
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state.
                // Emit the current tag token."
                emit_current_tag(switch_to(n, State::Data), seq![])
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to
                // the current attribute's value."
                none(append_to_attribute_value(n, seq![0xFFFDu32]))
            } else {
                // U+0022 ("), U+0027 ('), U+003C (<), U+003D (=), U+0060 (`):
                // "This is an unexpected-character-in-unquoted-attribute-value
                // parse error. Treat it as per the "anything else" entry
                // below."
                // Anything else: "Append the current input character to the
                // current attribute's value."
                none(append_to_attribute_value(n, seq![c]))
            }
        },
    }
}

/// §13.2.5.39 After attribute value (quoted) state.
pub open spec fn after_attribute_value_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-tag parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the before attribute name
                // state."
                none(switch_to(n, State::BeforeAttributeName))
            } else if c == 0x2F {
                // U+002F SOLIDUS (/): "Switch to the self-closing start tag
                // state."
                none(switch_to(n, State::SelfClosingStartTag))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state.
                // Emit the current tag token."
                emit_current_tag(switch_to(n, State::Data), seq![])
            } else {
                // Anything else: "This is a
                // missing-whitespace-between-attributes parse error. Reconsume
                // in the before attribute name state."
                none(switch_to(t, State::BeforeAttributeName))
            }
        },
    }
}

/// §13.2.5.40 Self-closing start tag state.
pub open spec fn self_closing_start_tag_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-tag parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Set the self-closing flag of
                // the current tag token. Switch to the data state. Emit the
                // current tag token."
                emit_current_tag(switch_to(set_self_closing(consumed(t)), State::Data), seq![])
            } else {
                // Anything else: "This is an unexpected-solidus-in-tag parse
                // error. Reconsume in the before attribute name state."
                none(switch_to(t, State::BeforeAttributeName))
            }
        },
    }
}

// ---------------------------------------------------------------------
// §13.2.5.41 to §13.2.5.52: comments
// ---------------------------------------------------------------------

/// §13.2.5.41 Bogus comment state.
pub open spec fn bogus_comment_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Emit the current comment token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current comment token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to the
                // comment token's data."
                none(append_to_comment(n, seq![0xFFFDu32]))
            } else {
                // Anything else: "Append the current input character to the
                // comment token's data."
                none(append_to_comment(n, seq![c]))
            }
        },
    }
}

/// §13.2.5.42 Markup declaration open state.
pub open spec fn markup_declaration_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // "If the next few characters are:"
    if starts_with(input, t.pos, seq![0x2Du32, 0x2D]) {
        // "Two U+002D HYPHEN-MINUS characters (-)": "Consume those two
        // characters, create a comment token whose data is the empty string,
        // and switch to the comment start state."
        none(switch_to(new_comment(Tokenizer { pos: t.pos + 2, ..t }, seq![]), State::CommentStart))
    } else if starts_with_ci(input, t.pos, doctype_lower()) {
        // "ASCII case-insensitive match for the word "DOCTYPE"": "Consume
        // those characters and switch to the DOCTYPE state."
        none(switch_to(Tokenizer { pos: t.pos + 7, ..t }, State::Doctype))
    } else if starts_with(input, t.pos, cdata_open()) {
        // "The string "[CDATA[" (the five uppercase letters "CDATA" with a
        // U+005B LEFT SQUARE BRACKET character before and after)": "Consume
        // those characters. If there is an adjusted current node and it is
        // not an element in the HTML namespace, then switch to the CDATA
        // section state. Otherwise, this is a cdata-in-html-content parse
        // error. Create a comment token whose data is the "[CDATA[" string.
        // Switch to the bogus comment state."
        let n = Tokenizer { pos: t.pos + 7, ..t };
        if t.in_foreign_content {
            none(switch_to(n, State::CdataSection))
        } else {
            none(switch_to(new_comment(n, cdata_open()), State::BogusComment))
        }
    } else {
        // "Anything else": "This is an incorrectly-opened-comment parse
        // error. Create a comment token whose data is the empty string.
        // Switch to the bogus comment state (don't consume anything in the
        // current state)."
        none(switch_to(new_comment(t, seq![]), State::BogusComment))
    }
}

/// §13.2.5.43 Comment start state.
pub open spec fn comment_start_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2D => {
            // U+002D HYPHEN-MINUS (-): "Switch to the comment start dash
            // state."
            none(switch_to(consumed(t), State::CommentStartDash))
        },
        Some(c) if c == 0x3E => {
            // U+003E GREATER-THAN SIGN (>): "This is an
            // abrupt-closing-of-empty-comment parse error. Switch to the data
            // state. Emit the current comment token."
            let n = switch_to(consumed(t), State::Data);
            (n, emit_current(n, seq![]))
        },
        // Anything else (EOF too): "Reconsume in the comment state."
        _ => none(switch_to(t, State::Comment)),
    }
}

/// §13.2.5.44 Comment start dash state.
pub open spec fn comment_start_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-comment parse error. Emit the current
        // comment token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the comment end state."
                none(switch_to(consumed(t), State::CommentEnd))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is an
                // abrupt-closing-of-empty-comment parse error. Switch to the
                // data state. Emit the current comment token."
                let n = switch_to(consumed(t), State::Data);
                (n, emit_current(n, seq![]))
            } else {
                // Anything else: "Append a U+002D HYPHEN-MINUS character (-)
                // to the comment token's data. Reconsume in the comment
                // state."
                none(switch_to(append_to_comment(t, seq![0x2Du32]), State::Comment))
            }
        },
    }
}

/// §13.2.5.45 Comment state.
pub open spec fn comment_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-comment parse error. Emit the current
        // comment token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3C {
                // U+003C LESS-THAN SIGN (<): "Append the current input
                // character to the comment token's data. Switch to the comment
                // less-than sign state."
                none(switch_to(append_to_comment(n, seq![c]), State::CommentLessThanSign))
            } else if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the comment end dash
                // state."
                none(switch_to(n, State::CommentEndDash))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to the
                // comment token's data."
                none(append_to_comment(n, seq![0xFFFDu32]))
            } else {
                // Anything else: "Append the current input character to the
                // comment token's data."
                none(append_to_comment(n, seq![c]))
            }
        },
    }
}

/// §13.2.5.46 Comment less-than sign state.
pub open spec fn comment_less_than_sign_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x21 => {
            // U+0021 EXCLAMATION MARK (!): "Append the current input character
            // to the comment token's data. Switch to the comment less-than
            // sign bang state."
            none(switch_to(append_to_comment(consumed(t), seq![c]), State::CommentLessThanSignBang))
        },
        Some(c) if c == 0x3C => {
            // U+003C LESS-THAN SIGN (<): "Append the current input character
            // to the comment token's data."
            none(append_to_comment(consumed(t), seq![c]))
        },
        // Anything else: "Reconsume in the comment state."
        _ => none(switch_to(t, State::Comment)),
    }
}

/// §13.2.5.47 Comment less-than sign bang state.
pub open spec fn comment_less_than_sign_bang_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2D => {
            // U+002D HYPHEN-MINUS (-): "Switch to the comment less-than sign
            // bang dash state."
            none(switch_to(consumed(t), State::CommentLessThanSignBangDash))
        },
        // Anything else: "Reconsume in the comment state."
        _ => none(switch_to(t, State::Comment)),
    }
}

/// §13.2.5.48 Comment less-than sign bang dash state.
pub open spec fn comment_less_than_sign_bang_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x2D => {
            // U+002D HYPHEN-MINUS (-): "Switch to the comment less-than sign
            // bang dash dash state."
            none(switch_to(consumed(t), State::CommentLessThanSignBangDashDash))
        },
        // Anything else: "Reconsume in the comment end dash state."
        _ => none(switch_to(t, State::CommentEndDash)),
    }
}

/// §13.2.5.49 Comment less-than sign bang dash dash state.
pub open spec fn comment_less_than_sign_bang_dash_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // U+003E GREATER-THAN SIGN (>), EOF: "Reconsume in the comment end state."
    // Anything else: "This is a nested-comment parse error. Reconsume in the
    // comment end state."
    none(switch_to(t, State::CommentEnd))
}

/// §13.2.5.50 Comment end dash state.
pub open spec fn comment_end_dash_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-comment parse error. Emit the current
        // comment token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Switch to the comment end state."
                none(switch_to(consumed(t), State::CommentEnd))
            } else {
                // Anything else: "Append a U+002D HYPHEN-MINUS character (-)
                // to the comment token's data. Reconsume in the comment
                // state."
                none(switch_to(append_to_comment(t, seq![0x2Du32]), State::Comment))
            }
        },
    }
}

/// §13.2.5.51 Comment end state.
pub open spec fn comment_end_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-comment parse error. Emit the current
        // comment token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current comment token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else if c == 0x21 {
                // U+0021 EXCLAMATION MARK (!): "Switch to the comment end bang
                // state."
                none(switch_to(n, State::CommentEndBang))
            } else if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Append a U+002D HYPHEN-MINUS
                // character (-) to the comment token's data."
                none(append_to_comment(n, seq![0x2Du32]))
            } else {
                // Anything else: "Append two U+002D HYPHEN-MINUS characters (-)
                // to the comment token's data. Reconsume in the comment
                // state."
                none(switch_to(append_to_comment(t, seq![0x2Du32, 0x2D]), State::Comment))
            }
        },
    }
}

/// §13.2.5.52 Comment end bang state.
pub open spec fn comment_end_bang_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-comment parse error. Emit the current
        // comment token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            let n = consumed(t);
            if c == 0x2D {
                // U+002D HYPHEN-MINUS (-): "Append two U+002D HYPHEN-MINUS
                // characters (-) and a U+0021 EXCLAMATION MARK character (!)
                // to the comment token's data. Switch to the comment end dash
                // state."
                none(switch_to(append_to_comment(n, seq![0x2Du32, 0x2D, 0x21]), State::CommentEndDash))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is an
                // incorrectly-closed-comment parse error. Switch to the data
                // state. Emit the current comment token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else {
                // Anything else: "Append two U+002D HYPHEN-MINUS characters (-)
                // and a U+0021 EXCLAMATION MARK character (!) to the comment
                // token's data. Reconsume in the comment state."
                none(switch_to(append_to_comment(t, seq![0x2Du32, 0x2D, 0x21]), State::Comment))
            }
        },
    }
}

// ---------------------------------------------------------------------
// §13.2.5.53 to §13.2.5.68: DOCTYPE
// ---------------------------------------------------------------------

/// §13.2.5.53 DOCTYPE state.
pub open spec fn doctype_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Create a new DOCTYPE
        // token. Set its force-quirks flag to on. Emit the current token.
        // Emit an end-of-file token."
        None => {
            let n = set_force_quirks(new_doctype(t, None));
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the before DOCTYPE name
                // state."
                none(switch_to(consumed(t), State::BeforeDoctypeName))
            } else {
                // U+003E GREATER-THAN SIGN (>): "Reconsume in the before
                // DOCTYPE name state."
                // Anything else: "This is a
                // missing-whitespace-before-doctype-name parse error.
                // Reconsume in the before DOCTYPE name state."
                none(switch_to(t, State::BeforeDoctypeName))
            }
        },
    }
}

/// §13.2.5.54 Before DOCTYPE name state.
pub open spec fn before_doctype_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Create a new DOCTYPE
        // token. Set its force-quirks flag to on. Emit the current token.
        // Emit an end-of-file token."
        None => {
            let n = set_force_quirks(new_doctype(t, None));
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(n)
            } else if crate::charref::spec::is_ascii_upper_alpha(c) {
                // ASCII upper alpha: "Create a new DOCTYPE token. Set the
                // token's name to the lowercase version of the current input
                // character (add 0x0020 to the character's code point). Switch
                // to the DOCTYPE name state."
                none(switch_to(new_doctype(n, Some(seq![to_lower(c)])), State::DoctypeName))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Create a new DOCTYPE token. Set the token's name to a
                // U+FFFD REPLACEMENT CHARACTER character. Switch to the DOCTYPE
                // name state."
                none(switch_to(new_doctype(n, Some(seq![0xFFFDu32])), State::DoctypeName))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is a missing-doctype-name
                // parse error. Create a new DOCTYPE token. Set its force-quirks
                // flag to on. Switch to the data state. Emit the current
                // token."
                let m = switch_to(set_force_quirks(new_doctype(n, None)), State::Data);
                (m, emit_current(m, seq![]))
            } else {
                // Anything else: "Create a new DOCTYPE token. Set the token's
                // name to the current input character. Switch to the DOCTYPE
                // name state."
                none(switch_to(new_doctype(n, Some(seq![c])), State::DoctypeName))
            }
        },
    }
}

/// §13.2.5.55 DOCTYPE name state.
pub open spec fn doctype_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the after DOCTYPE name
                // state."
                none(switch_to(n, State::AfterDoctypeName))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current DOCTYPE token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else if crate::charref::spec::is_ascii_upper_alpha(c) {
                // ASCII upper alpha: "Append the lowercase version of the
                // current input character (add 0x0020 to the character's code
                // point) to the current DOCTYPE token's name."
                none(append_to_doctype_name(n, to_lower(c)))
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to the
                // current DOCTYPE token's name."
                none(append_to_doctype_name(n, 0xFFFD))
            } else {
                // Anything else: "Append the current input character to the
                // current DOCTYPE token's name."
                none(append_to_doctype_name(n, c))
            }
        },
    }
}

/// §13.2.5.56 After DOCTYPE name state.
pub open spec fn after_doctype_name_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(consumed(t))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current DOCTYPE token."
                let n = consumed(t);
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else if starts_with_ci(input, t.pos, public_lower()) {
                // Anything else: "If the six characters starting from the
                // current input character are an ASCII case-insensitive match
                // for the word "PUBLIC", then consume those characters and
                // switch to the after DOCTYPE public keyword state."
                none(switch_to(Tokenizer { pos: t.pos + 6, ..t }, State::AfterDoctypePublicKeyword))
            } else if starts_with_ci(input, t.pos, system_lower()) {
                // "Otherwise, if the six characters starting from the current
                // input character are an ASCII case-insensitive match for the
                // word "SYSTEM", then consume those characters and switch to
                // the after DOCTYPE system keyword state."
                none(switch_to(Tokenizer { pos: t.pos + 6, ..t }, State::AfterDoctypeSystemKeyword))
            } else {
                // "Otherwise, this is an
                // invalid-character-sequence-after-doctype-name parse error.
                // Set the current DOCTYPE token's force-quirks flag to on.
                // Reconsume in the bogus DOCTYPE state."
                none(switch_to(set_force_quirks(t), State::BogusDoctype))
            }
        },
    }
}

/// The after DOCTYPE public and system keyword states (§13.2.5.57 and
/// §13.2.5.63), which differ only in the identifier they set and the
/// states they switch to.
pub open spec fn after_doctype_keyword_state(input: Seq<u32>, t: Tokenizer, public: bool) -> Step {
    let set_empty = |t: Tokenizer|
        if public {
            set_public_identifier_empty(t)
        } else {
            set_system_identifier_empty(t)
        };
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the before DOCTYPE
                // [public|system] identifier state."
                none(
                    switch_to(
                        n,
                        if public {
                            State::BeforeDoctypePublicIdentifier
                        } else {
                            State::BeforeDoctypeSystemIdentifier
                        },
                    ),
                )
            } else if c == 0x22 {
                // U+0022 QUOTATION MARK ("): "This is a
                // missing-whitespace-after-doctype-[public|system]-keyword
                // parse error. Set the current DOCTYPE token's [public|system]
                // identifier to the empty string (not missing), then switch to
                // the DOCTYPE [public|system] identifier (double-quoted) state."
                none(
                    switch_to(
                        set_empty(n),
                        if public {
                            State::DoctypePublicIdentifierDoubleQuoted
                        } else {
                            State::DoctypeSystemIdentifierDoubleQuoted
                        },
                    ),
                )
            } else if c == 0x27 {
                // U+0027 APOSTROPHE ('): the same, single-quoted.
                none(
                    switch_to(
                        set_empty(n),
                        if public {
                            State::DoctypePublicIdentifierSingleQuoted
                        } else {
                            State::DoctypeSystemIdentifierSingleQuoted
                        },
                    ),
                )
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is a
                // missing-doctype-[public|system]-identifier parse error. Set
                // the current DOCTYPE token's force-quirks flag to on. Switch
                // to the data state. Emit the current DOCTYPE token."
                let m = switch_to(set_force_quirks(n), State::Data);
                (m, emit_current(m, seq![]))
            } else {
                // Anything else: "This is a
                // missing-quote-before-doctype-[public|system]-identifier
                // parse error. Set the current DOCTYPE token's force-quirks
                // flag to on. Reconsume in the bogus DOCTYPE state."
                none(switch_to(set_force_quirks(t), State::BogusDoctype))
            }
        },
    }
}

/// §13.2.5.57 After DOCTYPE public keyword state.
pub open spec fn after_doctype_public_keyword_state(input: Seq<u32>, t: Tokenizer) -> Step {
    after_doctype_keyword_state(input, t, true)
}

/// The before DOCTYPE public and system identifier states (§13.2.5.58 and
/// §13.2.5.64).
pub open spec fn before_doctype_identifier_state(input: Seq<u32>, t: Tokenizer, public: bool) -> Step {
    let set_empty = |t: Tokenizer|
        if public {
            set_public_identifier_empty(t)
        } else {
            set_system_identifier_empty(t)
        };
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(n)
            } else if c == 0x22 {
                // U+0022 QUOTATION MARK ("): "Set the current DOCTYPE token's
                // [public|system] identifier to the empty string (not
                // missing), then switch to the DOCTYPE [public|system]
                // identifier (double-quoted) state."
                none(
                    switch_to(
                        set_empty(n),
                        if public {
                            State::DoctypePublicIdentifierDoubleQuoted
                        } else {
                            State::DoctypeSystemIdentifierDoubleQuoted
                        },
                    ),
                )
            } else if c == 0x27 {
                // U+0027 APOSTROPHE ('): the same, single-quoted.
                none(
                    switch_to(
                        set_empty(n),
                        if public {
                            State::DoctypePublicIdentifierSingleQuoted
                        } else {
                            State::DoctypeSystemIdentifierSingleQuoted
                        },
                    ),
                )
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is a
                // missing-doctype-[public|system]-identifier parse error. Set
                // the current DOCTYPE token's force-quirks flag to on. Switch
                // to the data state. Emit the current DOCTYPE token."
                let m = switch_to(set_force_quirks(n), State::Data);
                (m, emit_current(m, seq![]))
            } else {
                // Anything else: "This is a
                // missing-quote-before-doctype-[public|system]-identifier
                // parse error. Set the current DOCTYPE token's force-quirks
                // flag to on. Reconsume in the bogus DOCTYPE state."
                none(switch_to(set_force_quirks(t), State::BogusDoctype))
            }
        },
    }
}

/// §13.2.5.58 Before DOCTYPE public identifier state.
pub open spec fn before_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer) -> Step {
    before_doctype_identifier_state(input, t, true)
}

/// The four quoted DOCTYPE identifier states (§13.2.5.59, §13.2.5.60,
/// §13.2.5.65, §13.2.5.66), which differ in the identifier, the quote, and
/// the state after it.
pub open spec fn doctype_identifier_quoted_state(input: Seq<u32>, t: Tokenizer, public: bool, quote: u32) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if c == quote {
                // U+0022 QUOTATION MARK (") [U+0027 APOSTROPHE (')]: "Switch to
                // the after DOCTYPE [public|system] identifier state."
                none(
                    switch_to(
                        n,
                        if public {
                            State::AfterDoctypePublicIdentifier
                        } else {
                            State::AfterDoctypeSystemIdentifier
                        },
                    ),
                )
            } else if c == 0x00 {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Append a U+FFFD REPLACEMENT CHARACTER character to the
                // current DOCTYPE token's [public|system] identifier."
                none(
                    if public {
                        append_to_public_identifier(n, 0xFFFD)
                    } else {
                        append_to_system_identifier(n, 0xFFFD)
                    },
                )
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "This is an
                // abrupt-doctype-[public|system]-identifier parse error. Set
                // the current DOCTYPE token's force-quirks flag to on. Switch
                // to the data state. Emit the current DOCTYPE token."
                let m = switch_to(set_force_quirks(n), State::Data);
                (m, emit_current(m, seq![]))
            } else {
                // Anything else: "Append the current input character to the
                // current DOCTYPE token's [public|system] identifier."
                none(
                    if public {
                        append_to_public_identifier(n, c)
                    } else {
                        append_to_system_identifier(n, c)
                    },
                )
            }
        },
    }
}

/// §13.2.5.59 DOCTYPE public identifier (double-quoted) state.
pub open spec fn doctype_public_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    doctype_identifier_quoted_state(input, t, true, 0x22)
}

/// §13.2.5.60 DOCTYPE public identifier (single-quoted) state.
pub open spec fn doctype_public_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    doctype_identifier_quoted_state(input, t, true, 0x27)
}

/// §13.2.5.61 After DOCTYPE public identifier state.
pub open spec fn after_doctype_public_identifier_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Switch to the between DOCTYPE public and
                // system identifiers state."
                none(switch_to(n, State::BetweenDoctypePublicAndSystemIdentifiers))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current DOCTYPE token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else if c == 0x22 {
                // U+0022 QUOTATION MARK ("): "This is a
                // missing-whitespace-between-doctype-public-and-system-identifiers
                // parse error. Set the current DOCTYPE token's system
                // identifier to the empty string (not missing), then switch to
                // the DOCTYPE system identifier (double-quoted) state."
                none(switch_to(set_system_identifier_empty(n), State::DoctypeSystemIdentifierDoubleQuoted))
            } else if c == 0x27 {
                // U+0027 APOSTROPHE ('): the same, single-quoted.
                none(switch_to(set_system_identifier_empty(n), State::DoctypeSystemIdentifierSingleQuoted))
            } else {
                // Anything else: "This is a
                // missing-quote-before-doctype-system-identifier parse error.
                // Set the current DOCTYPE token's force-quirks flag to on.
                // Reconsume in the bogus DOCTYPE state."
                none(switch_to(set_force_quirks(t), State::BogusDoctype))
            }
        },
    }
}

/// §13.2.5.62 Between DOCTYPE public and system identifiers state.
pub open spec fn between_doctype_public_and_system_identifiers_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(n)
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current DOCTYPE token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else if c == 0x22 {
                // U+0022 QUOTATION MARK ("): "Set the current DOCTYPE token's
                // system identifier to the empty string (not missing), then
                // switch to the DOCTYPE system identifier (double-quoted)
                // state."
                none(switch_to(set_system_identifier_empty(n), State::DoctypeSystemIdentifierDoubleQuoted))
            } else if c == 0x27 {
                // U+0027 APOSTROPHE ('): the same, single-quoted.
                none(switch_to(set_system_identifier_empty(n), State::DoctypeSystemIdentifierSingleQuoted))
            } else {
                // Anything else: "This is a
                // missing-quote-before-doctype-system-identifier parse error.
                // Set the current DOCTYPE token's force-quirks flag to on.
                // Reconsume in the bogus DOCTYPE state."
                none(switch_to(set_force_quirks(t), State::BogusDoctype))
            }
        },
    }
}

/// §13.2.5.63 After DOCTYPE system keyword state.
pub open spec fn after_doctype_system_keyword_state(input: Seq<u32>, t: Tokenizer) -> Step {
    after_doctype_keyword_state(input, t, false)
}

/// §13.2.5.64 Before DOCTYPE system identifier state.
pub open spec fn before_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer) -> Step {
    before_doctype_identifier_state(input, t, false)
}

/// §13.2.5.65 DOCTYPE system identifier (double-quoted) state.
pub open spec fn doctype_system_identifier_double_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    doctype_identifier_quoted_state(input, t, false, 0x22)
}

/// §13.2.5.66 DOCTYPE system identifier (single-quoted) state.
pub open spec fn doctype_system_identifier_single_quoted_state(input: Seq<u32>, t: Tokenizer) -> Step {
    doctype_identifier_quoted_state(input, t, false, 0x27)
}

/// §13.2.5.67 After DOCTYPE system identifier state.
pub open spec fn after_doctype_system_identifier_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-doctype parse error. Set the current
        // DOCTYPE token's force-quirks flag to on. Emit the current DOCTYPE
        // token. Emit an end-of-file token."
        None => {
            let n = set_force_quirks(t);
            emit_eof(n, emit_current(n, seq![]))
        },
        Some(c) => {
            let n = consumed(t);
            if is_tab_lf_ff_space(c) {
                // tab, LF, FF, space: "Ignore the character."
                none(n)
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current DOCTYPE token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else {
                // Anything else: "This is an
                // unexpected-character-after-doctype-system-identifier parse
                // error. Reconsume in the bogus DOCTYPE state. (This does not
                // set the current DOCTYPE token's force-quirks flag to on.)"
                none(switch_to(t, State::BogusDoctype))
            }
        },
    }
}

/// §13.2.5.68 Bogus DOCTYPE state.
pub open spec fn bogus_doctype_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "Emit the current DOCTYPE token. Emit an end-of-file token."
        None => emit_eof(t, emit_current(t, seq![])),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current DOCTYPE token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else {
                // U+0000 NULL: "This is an unexpected-null-character parse
                // error. Ignore the character."
                // Anything else: "Ignore the character."
                none(n)
            }
        },
    }
}

// ---------------------------------------------------------------------
// §13.2.5.69 to §13.2.5.76: CDATA sections and processing instructions
// ---------------------------------------------------------------------

/// §13.2.5.69 CDATA section state.
pub open spec fn cdata_section_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-cdata parse error. Emit an end-of-file
        // token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x5D {
                // U+005D RIGHT SQUARE BRACKET (]): "Switch to the CDATA
                // section bracket state."
                none(switch_to(n, State::CdataSectionBracket))
            } else {
                // Anything else: "Emit the current input character as a
                // character token." (U+0000 NULL is handled by the tree
                // builder, as the standard notes.)
                one(n, ch(c))
            }
        },
    }
}

/// §13.2.5.70 CDATA section bracket state.
pub open spec fn cdata_section_bracket_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x5D => {
            // U+005D RIGHT SQUARE BRACKET (]): "Switch to the CDATA section
            // end state."
            none(switch_to(consumed(t), State::CdataSectionEnd))
        },
        // Anything else: "Emit a U+005D RIGHT SQUARE BRACKET character
        // token. Reconsume in the CDATA section state."
        _ => one(switch_to(t, State::CdataSection), ch(0x5D)),
    }
}

/// §13.2.5.71 CDATA section end state.
pub open spec fn cdata_section_end_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if c == 0x5D => {
            // U+005D RIGHT SQUARE BRACKET (]): "Emit a U+005D RIGHT SQUARE
            // BRACKET character token."
            one(consumed(t), ch(0x5D))
        },
        Some(c) if c == 0x3E => {
            // U+003E GREATER-THAN SIGN character: "Switch to the data state."
            none(switch_to(consumed(t), State::Data))
        },
        // Anything else: "Emit two U+005D RIGHT SQUARE BRACKET character
        // tokens. Reconsume in the CDATA section state."
        _ => two(switch_to(t, State::CdataSection), ch(0x5D), ch(0x5D)),
    }
}

/// §13.2.5.72 Processing instruction open state.
pub open spec fn processing_instruction_open_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-processing-instruction parse error. Emit an
        // end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            if crate::charref::spec::is_ascii_alpha(c) || c == 0x5F {
                // ASCII alpha, U+005F LOW LINE (_): "Reconsume in the
                // processing instruction target state."
                none(switch_to(t, State::ProcessingInstructionTarget))
            } else {
                // Anything else: "This is an
                // invalid-first-character-of-processing-instruction-target
                // parse error. Convert the temporary buffer to a comment.
                // Reconsume in the bogus comment state."
                none(switch_to(convert_temporary_buffer_to_comment(t), State::BogusComment))
            }
        },
    }
}

/// §13.2.5.73 Processing instruction target state.
pub open spec fn processing_instruction_target_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-processing-instruction parse error. Emit an
        // end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            if is_tab_lf_ff_space(c) || c == 0x3F || c == 0x3E {
                // tab, LF, FF, space, U+003F QUESTION MARK (?), U+003E
                // GREATER-THAN SIGN (>): "Let target be the concatenation of
                // the code points in the temporary buffer, in the order they
                // were added to the buffer."
                let target = t.temporary_buffer;
                if eq_ci(target, xml()) || eq_ci(target, xml_stylesheet()) {
                    // "If target is an ASCII case-insensitive match for "xml"
                    // or "xml-stylesheet": This is a
                    // disallowed-processing-instruction-target parse error.
                    // Convert the temporary buffer to a comment. Reconsume in
                    // the bogus comment state."
                    none(switch_to(convert_temporary_buffer_to_comment(t), State::BogusComment))
                } else {
                    // "Otherwise: Create a processing instruction token whose
                    // target is target and data is the empty string. Reconsume
                    // in the after processing instruction target state."
                    none(
                        switch_to(
                            Tokenizer { current: Token::ProcessingInstruction { target, data: seq![] }, ..t },
                            State::AfterProcessingInstructionTarget,
                        ),
                    )
                }
            } else if crate::charref::spec::is_ascii_alphanumeric(c) || c == 0x2D || c == 0x5F {
                // ASCII alphanumeric, U+002D HYPHEN-MINUS (-), U+005F LOW LINE
                // (_): "Append the current input character to the temporary
                // buffer."
                none(Tokenizer { temporary_buffer: t.temporary_buffer.push(c), ..consumed(t) })
            } else {
                // Anything else: "This is an
                // invalid-processing-instruction-target parse error. Convert
                // the temporary buffer to a comment. Reconsume in the bogus
                // comment state."
                none(switch_to(convert_temporary_buffer_to_comment(t), State::BogusComment))
            }
        },
    }
}

/// §13.2.5.74 After processing instruction target state.
pub open spec fn after_processing_instruction_target_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if is_tab_lf_ff_space(c) => {
            // tab, LF, FF, space: "Ignore the character."
            none(consumed(t))
        },
        // Anything else (EOF too): "Reconsume in the processing instruction
        // data state."
        _ => none(switch_to(t, State::ProcessingInstructionData)),
    }
}

/// §13.2.5.75 Processing instruction data state.
pub open spec fn processing_instruction_data_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-processing-instruction parse error. Emit an
        // end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            let n = consumed(t);
            if c == 0x3F {
                // U+003F QUESTION MARK (?): "Switch to the processing
                // instruction questionable state."
                none(switch_to(n, State::ProcessingInstructionQuestionable))
            } else if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current processing instruction token."
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else {
                // Anything else: "Append the current input character to the
                // current processing instruction token's data."
                none(append_to_pi_data(n, seq![c]))
            }
        },
    }
}

/// §13.2.5.76 Processing instruction questionable state.
pub open spec fn processing_instruction_questionable_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        // EOF: "This is an eof-in-processing-instruction parse error. Emit an
        // end-of-file token."
        None => emit_eof(t, seq![]),
        Some(c) => {
            if c == 0x3E {
                // U+003E GREATER-THAN SIGN (>): "Switch to the data state. Emit
                // the current processing instruction token."
                let n = consumed(t);
                (switch_to(n, State::Data), emit_current(n, seq![]))
            } else {
                // Anything else: "Append U+003F (?) to the current processing
                // instruction token's data. Reconsume in the processing
                // instruction data state."
                none(switch_to(append_to_pi_data(t, seq![0x3Fu32]), State::ProcessingInstructionData))
            }
        },
    }
}

// ---------------------------------------------------------------------
// §13.2.5.77 to §13.2.5.84: character references
// ---------------------------------------------------------------------

/// "Flush code points consumed as a character reference" and switch (or
/// reconsume) in the return state.
pub open spec fn flush_and_return(t: Tokenizer) -> Step {
    let (f, toks) = flush(t);
    (switch_to(f, t.return_state.state()), toks)
}

/// §13.2.5.77 Character reference state.
pub open spec fn character_reference_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // "Set the temporary buffer to the empty string. Append a U+0026
    // AMPERSAND (&) character to the temporary buffer."
    let t = Tokenizer { temporary_buffer: seq![0x26u32], ..t };
    // "Consume the next input character:"
    match next_char(input, t.pos) {
        Some(c) if crate::charref::spec::is_ascii_alphanumeric(c) => {
            // ASCII alphanumeric: "Reconsume in the named character reference
            // state."
            none(switch_to(t, State::NamedCharacterReference))
        },
        Some(c) if c == 0x23 => {
            // U+0023 NUMBER SIGN (#): "Append the current input character to
            // the temporary buffer. Switch to the numeric character reference
            // state."
            none(
                switch_to(
                    Tokenizer { temporary_buffer: t.temporary_buffer.push(c), ..consumed(t) },
                    State::NumericCharacterReference,
                ),
            )
        },
        // Anything else: "Flush code points consumed as a character
        // reference. Reconsume in the return state."
        _ => flush_and_return(t),
    }
}

/// §13.2.5.78 Named character reference state.
pub open spec fn named_character_reference_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // "Consume the maximum number of characters possible, where the
    // consumed characters are one of the identifiers in the first column of
    // the named character references table. Append each character to the
    // temporary buffer when it's consumed."
    match crate::charref::spec::longest_match(input, t.pos as int) {
        Some(i) => {
            // "If there is a match":
            let name = crate::charref::spec::entity_name(i as int);
            let n = Tokenizer {
                pos: t.pos + name.len(),
                temporary_buffer: t.temporary_buffer + name,
                ..t
            };
            if crate::charref::spec::historical_reasons(consumed_as_part_of_attribute(t), name, next_char(input, n.pos)) {
                // "If the character reference was consumed as part of an
                // attribute, and the last character matched is not a U+003B
                // SEMICOLON character (;), and the next input character is
                // either a U+003D EQUALS SIGN character (=) or an ASCII
                // alphanumeric, then, for historical reasons, flush code
                // points consumed as a character reference and switch to the
                // return state."
                flush_and_return(n)
            } else {
                // "Otherwise:"
                // 1. "If the last character matched is not a U+003B SEMICOLON
                //    character (;), then this is a
                //    missing-semicolon-after-character-reference parse error."
                // 2. "Set the temporary buffer to the empty string. Append one
                //    or two characters corresponding to the character
                //    reference name (as given by the second column of the
                //    named character references table) to the temporary
                //    buffer."
                // 3. "Flush code points consumed as a character reference.
                //    Switch to the return state."
                flush_and_return(Tokenizer { temporary_buffer: crate::charref::spec::entity_code_points(i as int), ..n })
            }
        },
        None => {
            // "Otherwise": "Flush code points consumed as a character
            // reference. Switch to the ambiguous ampersand state."
            let (f, toks) = flush(t);
            (switch_to(f, State::AmbiguousAmpersand), toks)
        },
    }
}

/// §13.2.5.79 Ambiguous ampersand state.
pub open spec fn ambiguous_ampersand_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if crate::charref::spec::is_ascii_alphanumeric(c) => {
            // ASCII alphanumeric: "If the character reference was consumed as
            // part of an attribute, then append the current input character
            // to the current attribute's value. Otherwise, emit the current
            // input character as a character token."
            if consumed_as_part_of_attribute(t) {
                none(append_to_attribute_value(consumed(t), seq![c]))
            } else {
                one(consumed(t), ch(c))
            }
        },
        // U+003B SEMICOLON (;): "This is an unknown-named-character-reference
        // parse error. Reconsume in the return state."
        // Anything else: "Reconsume in the return state."
        _ => none(switch_to(t, t.return_state.state())),
    }
}

/// §13.2.5.80 Numeric character reference state.
pub open spec fn numeric_character_reference_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // "Set the character reference code to zero (0)."
    let t = Tokenizer { character_reference_code: 0, ..t };
    // "Consume the next input character:"
    match next_char(input, t.pos) {
        Some(c) if c == 0x78 || c == 0x58 => {
            // U+0078 LATIN SMALL LETTER X, U+0058 LATIN CAPITAL LETTER X:
            // "Append the current input character to the temporary buffer.
            // Switch to the hexadecimal character reference start state."
            none(
                switch_to(
                    Tokenizer { temporary_buffer: t.temporary_buffer.push(c), ..consumed(t) },
                    State::HexadecimalCharacterReferenceStart,
                ),
            )
        },
        Some(c) if crate::charref::spec::is_ascii_digit(c) => {
            // ASCII digit: "Reconsume in the decimal character reference
            // state."
            none(switch_to(t, State::DecimalCharacterReference))
        },
        // Anything else: "This is an
        // absence-of-digits-in-numeric-character-reference parse error. Flush
        // code points consumed as a character reference. Reconsume in the
        // return state."
        _ => flush_and_return(t),
    }
}

/// §13.2.5.81 Hexadecimal character reference start state.
pub open spec fn hexadecimal_character_reference_start_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if is_ascii_hex_digit(c) => {
            // ASCII hex digit: "Reconsume in the hexadecimal character
            // reference state."
            none(switch_to(t, State::HexadecimalCharacterReference))
        },
        // Anything else: "This is an
        // absence-of-digits-in-numeric-character-reference parse error. Flush
        // code points consumed as a character reference. Reconsume in the
        // return state."
        _ => flush_and_return(t),
    }
}

/// "Multiply the character reference code by" `base`, and "add" `digit`.
pub open spec fn add_digit(t: Tokenizer, base: nat, digit: nat) -> Tokenizer {
    Tokenizer { character_reference_code: t.character_reference_code * base + digit, ..t }
}

/// §13.2.5.82 Hexadecimal character reference state.
pub open spec fn hexadecimal_character_reference_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if crate::charref::spec::is_ascii_digit(c) => {
            // ASCII digit: "Multiply the character reference code by 16. Add a
            // numeric version of the current input character (subtract 0x0030
            // from the character's code point) to the character reference
            // code."
            none(add_digit(consumed(t), 16, (c - 0x30) as nat))
        },
        Some(c) if is_ascii_upper_hex_digit(c) => {
            // ASCII upper hex digit: "Multiply the character reference code by
            // 16. Add a numeric version of the current input character as a
            // hexadecimal digit (subtract 0x0037 from the character's code
            // point) to the character reference code."
            none(add_digit(consumed(t), 16, (c - 0x37) as nat))
        },
        Some(c) if is_ascii_lower_hex_digit(c) => {
            // ASCII lower hex digit: "Multiply the character reference code by
            // 16. Add a numeric version of the current input character as a
            // hexadecimal digit (subtract 0x0057 from the character's code
            // point) to the character reference code."
            none(add_digit(consumed(t), 16, (c - 0x57) as nat))
        },
        Some(c) if c == 0x3B => {
            // U+003B SEMICOLON: "Switch to the numeric character reference end
            // state."
            none(switch_to(consumed(t), State::NumericCharacterReferenceEnd))
        },
        // Anything else: "This is a missing-semicolon-after-character-reference
        // parse error. Reconsume in the numeric character reference end
        // state."
        _ => none(switch_to(t, State::NumericCharacterReferenceEnd)),
    }
}

/// §13.2.5.83 Decimal character reference state.
pub open spec fn decimal_character_reference_state(input: Seq<u32>, t: Tokenizer) -> Step {
    match next_char(input, t.pos) {
        Some(c) if crate::charref::spec::is_ascii_digit(c) => {
            // ASCII digit: "Multiply the character reference code by 10. Add a
            // numeric version of the current input character (subtract 0x0030
            // from the character's code point) to the character reference
            // code."
            none(add_digit(consumed(t), 10, (c - 0x30) as nat))
        },
        Some(c) if c == 0x3B => {
            // U+003B SEMICOLON: "Switch to the numeric character reference end
            // state."
            none(switch_to(consumed(t), State::NumericCharacterReferenceEnd))
        },
        // Anything else: "This is a missing-semicolon-after-character-reference
        // parse error. Reconsume in the numeric character reference end
        // state."
        _ => none(switch_to(t, State::NumericCharacterReferenceEnd)),
    }
}

/// §13.2.5.84 Numeric character reference end state.
pub open spec fn numeric_character_reference_end_state(input: Seq<u32>, t: Tokenizer) -> Step {
    // "Check the character reference code:" (the five checks are
    // `numeric_reference_end_code`, with the table)
    let code = crate::charref::spec::numeric_reference_end_code(t.character_reference_code);
    // "Set the temporary buffer to the empty string. Append a code point
    // equal to the character reference code to the temporary buffer. Flush
    // code points consumed as a character reference. Switch to the return
    // state."
    flush_and_return(Tokenizer { temporary_buffer: seq![code], ..t })
}

// ---------------------------------------------------------------------
// The state machine
// ---------------------------------------------------------------------

/// One call of the current state's function (§13.2.5: "the following state
/// machine").
#[verifier::opaque]
pub open spec fn step(input: Seq<u32>, t: Tokenizer) -> Step {
    match t.state {
        State::Data => data_state(input, t),
        State::Rcdata => rcdata_state(input, t),
        State::Rawtext => rawtext_state(input, t),
        State::ScriptData => script_data_state(input, t),
        State::Plaintext => plaintext_state(input, t),
        State::TagOpen => tag_open_state(input, t),
        State::EndTagOpen => end_tag_open_state(input, t),
        State::TagName => tag_name_state(input, t),
        State::RcdataLessThanSign => rcdata_less_than_sign_state(input, t),
        State::RcdataEndTagOpen => rcdata_end_tag_open_state(input, t),
        State::RcdataEndTagName => rcdata_end_tag_name_state(input, t),
        State::RawtextLessThanSign => rawtext_less_than_sign_state(input, t),
        State::RawtextEndTagOpen => rawtext_end_tag_open_state(input, t),
        State::RawtextEndTagName => rawtext_end_tag_name_state(input, t),
        State::ScriptDataLessThanSign => script_data_less_than_sign_state(input, t),
        State::ScriptDataEndTagOpen => script_data_end_tag_open_state(input, t),
        State::ScriptDataEndTagName => script_data_end_tag_name_state(input, t),
        State::ScriptDataEscapeStart => script_data_escape_start_state(input, t),
        State::ScriptDataEscapeStartDash => script_data_escape_start_dash_state(input, t),
        State::ScriptDataEscaped => script_data_escaped_state(input, t),
        State::ScriptDataEscapedDash => script_data_escaped_dash_state(input, t),
        State::ScriptDataEscapedDashDash => script_data_escaped_dash_dash_state(input, t),
        State::ScriptDataEscapedLessThanSign => script_data_escaped_less_than_sign_state(input, t),
        State::ScriptDataEscapedEndTagOpen => script_data_escaped_end_tag_open_state(input, t),
        State::ScriptDataEscapedEndTagName => script_data_escaped_end_tag_name_state(input, t),
        State::ScriptDataDoubleEscapeStart => script_data_double_escape_start_state(input, t),
        State::ScriptDataDoubleEscaped => script_data_double_escaped_state(input, t),
        State::ScriptDataDoubleEscapedDash => script_data_double_escaped_dash_state(input, t),
        State::ScriptDataDoubleEscapedDashDash => script_data_double_escaped_dash_dash_state(input, t),
        State::ScriptDataDoubleEscapedLessThanSign => script_data_double_escaped_less_than_sign_state(input, t),
        State::ScriptDataDoubleEscapeEnd => script_data_double_escape_end_state(input, t),
        State::BeforeAttributeName => before_attribute_name_state(input, t),
        State::AttributeName => attribute_name_state(input, t),
        State::AfterAttributeName => after_attribute_name_state(input, t),
        State::BeforeAttributeValue => before_attribute_value_state(input, t),
        State::AttributeValueDoubleQuoted => attribute_value_double_quoted_state(input, t),
        State::AttributeValueSingleQuoted => attribute_value_single_quoted_state(input, t),
        State::AttributeValueUnquoted => attribute_value_unquoted_state(input, t),
        State::AfterAttributeValueQuoted => after_attribute_value_quoted_state(input, t),
        State::SelfClosingStartTag => self_closing_start_tag_state(input, t),
        State::BogusComment => bogus_comment_state(input, t),
        State::MarkupDeclarationOpen => markup_declaration_open_state(input, t),
        State::CommentStart => comment_start_state(input, t),
        State::CommentStartDash => comment_start_dash_state(input, t),
        State::Comment => comment_state(input, t),
        State::CommentLessThanSign => comment_less_than_sign_state(input, t),
        State::CommentLessThanSignBang => comment_less_than_sign_bang_state(input, t),
        State::CommentLessThanSignBangDash => comment_less_than_sign_bang_dash_state(input, t),
        State::CommentLessThanSignBangDashDash => comment_less_than_sign_bang_dash_dash_state(input, t),
        State::CommentEndDash => comment_end_dash_state(input, t),
        State::CommentEnd => comment_end_state(input, t),
        State::CommentEndBang => comment_end_bang_state(input, t),
        State::Doctype => doctype_state(input, t),
        State::BeforeDoctypeName => before_doctype_name_state(input, t),
        State::DoctypeName => doctype_name_state(input, t),
        State::AfterDoctypeName => after_doctype_name_state(input, t),
        State::AfterDoctypePublicKeyword => after_doctype_public_keyword_state(input, t),
        State::BeforeDoctypePublicIdentifier => before_doctype_public_identifier_state(input, t),
        State::DoctypePublicIdentifierDoubleQuoted => doctype_public_identifier_double_quoted_state(input, t),
        State::DoctypePublicIdentifierSingleQuoted => doctype_public_identifier_single_quoted_state(input, t),
        State::AfterDoctypePublicIdentifier => after_doctype_public_identifier_state(input, t),
        State::BetweenDoctypePublicAndSystemIdentifiers => between_doctype_public_and_system_identifiers_state(
            input,
            t,
        ),
        State::AfterDoctypeSystemKeyword => after_doctype_system_keyword_state(input, t),
        State::BeforeDoctypeSystemIdentifier => before_doctype_system_identifier_state(input, t),
        State::DoctypeSystemIdentifierDoubleQuoted => doctype_system_identifier_double_quoted_state(input, t),
        State::DoctypeSystemIdentifierSingleQuoted => doctype_system_identifier_single_quoted_state(input, t),
        State::AfterDoctypeSystemIdentifier => after_doctype_system_identifier_state(input, t),
        State::BogusDoctype => bogus_doctype_state(input, t),
        State::CdataSection => cdata_section_state(input, t),
        State::CdataSectionBracket => cdata_section_bracket_state(input, t),
        State::CdataSectionEnd => cdata_section_end_state(input, t),
        State::ProcessingInstructionOpen => processing_instruction_open_state(input, t),
        State::ProcessingInstructionTarget => processing_instruction_target_state(input, t),
        State::AfterProcessingInstructionTarget => after_processing_instruction_target_state(input, t),
        State::ProcessingInstructionData => processing_instruction_data_state(input, t),
        State::ProcessingInstructionQuestionable => processing_instruction_questionable_state(input, t),
        State::CharacterReference => character_reference_state(input, t),
        State::NamedCharacterReference => named_character_reference_state(input, t),
        State::AmbiguousAmpersand => ambiguous_ampersand_state(input, t),
        State::NumericCharacterReference => numeric_character_reference_state(input, t),
        State::HexadecimalCharacterReferenceStart => hexadecimal_character_reference_start_state(input, t),
        State::HexadecimalCharacterReference => hexadecimal_character_reference_state(input, t),
        State::DecimalCharacterReference => decimal_character_reference_state(input, t),
        State::NumericCharacterReferenceEnd => numeric_character_reference_end_state(input, t),
    }
}

/// The tokenizer has stopped: an end-of-file token was emitted (or the
/// position is past the input, which no step reaches).
pub open spec fn stopped(input: Seq<u32>, t: Tokenizer) -> bool {
    t.done || t.pos > input.len()
}

/// The tokens the tokenizer emits from `t` on, until the end-of-file token
/// (§13.2.5's state machine, run to the end of the input).
pub open spec fn run(input: Seq<u32>, t: Tokenizer) -> Seq<Token>
    decreases super::termination::remaining(input, t), super::termination::rank(input, t) via run_decreases
{
    if stopped(input, t) {
        seq![]
    } else {
        let (n, toks) = step(input, t);
        if stopped(input, n) {
            toks
        } else {
            toks + run(input, n)
        }
    }
}

/// Termination of [`run`] (`termination.rs`).
#[via_fn]
pub proof fn run_decreases(input: Seq<u32>, t: Tokenizer) {
    super::termination::lemma_step_decreases(input, t);
}

/// The whole-input face: the tokens of `input` (preprocessed), starting in
/// `start_state` with `last_start_tag` as the last start tag emitted.
pub open spec fn tokenize(input: Seq<u32>, start_state: State, last_start_tag: Option<Seq<u32>>) -> Seq<Token> {
    run(input, initial(start_state, last_start_tag))
}

/// The one-token face: steps from `t` until one emits a token (or the
/// tokenizer stops), with the tokenizer after it and the tokens that step
/// emitted (one or more; a step emits more than one only where the
/// standard emits several in a row).
pub open spec fn next_token(input: Seq<u32>, t: Tokenizer) -> Step
    decreases super::termination::remaining(input, t), super::termination::rank(input, t) via next_token_decreases
{
    if stopped(input, t) {
        (t, seq![])
    } else {
        let (n, toks) = step(input, t);
        if toks.len() > 0 || stopped(input, n) {
            (n, toks)
        } else {
            next_token(input, n)
        }
    }
}

/// Termination of [`next_token`] (`termination.rs`).
#[via_fn]
pub proof fn next_token_decreases(input: Seq<u32>, t: Tokenizer) {
    super::termination::lemma_step_decreases(input, t);
}

} // verus!
