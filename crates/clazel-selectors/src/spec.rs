//! Executable-style specification of CSS selectors: parsing, matching against an element
//! of a `clazel-dom` arena, specificity and serialization. Nothing here runs; it defines
//! what "correct" means.
//!
//! Sources, each pinned to the text transcribed:
//! - Selectors Level 4, Editor's Draft, `selectors-4/Overview.bs` of `w3c/csswg-drafts` at
//!   commit `5b65dd3a82c1019dca6158823e995a52d1d4204a` (2026-11-07),
//!   <https://drafts.csswg.org/selectors-4/>. Its sections are cited as `§N`.
//! - HTML Living Standard, §4.16.2 "Case-sensitivity of selectors" and §4.16.3
//!   "Pseudo-classes" (`:link`), as published on 2026-11-09,
//!   <https://html.spec.whatwg.org/multipage/semantics-other.html#case-sensitivity-of-selectors>.
//! - CSSOM, Editor's Draft, `cssom-1/Overview.bs` of `w3c/csswg-drafts` at commit
//!   `5823c7a7c3401c6b434dbf3ef88077ea45e30303`, §6.7.2 "Serializing Selectors" and §2.1
//!   "Common Serializing Idioms", <https://drafts.csswg.org/cssom-1/#serializing-selectors>.
//! - CSS Syntax Level 3 through [`clazel_css::parser::spec`], which pins its own commit:
//!   "parse something according to a CSS grammar" (§5.4.1), "parse a list" (§5.4.2) and
//!   `<an+b>` (§6).
//!
//! The text's prose has few numbered steps, so a `// "…"` comment quotes the sentence or
//! grammar production a branch stands for, and `// N.` is used where the text numbers.
//!
//! Modelling choices. Each is a difference in form, never in meaning, except those marked
//! **meaning**, which say what they change and why.
//! - **meaning** The subset (phase-5.md item 5.5). Supported: the grammar of §18; type,
//!   universal and namespace selectors (§5); attribute selectors with all seven forms and
//!   the `i` and `s` flags (§6); class and ID selectors (§6.6, §7); `:link`, `:visited`,
//!   `:any-link` (§9); `:root`, `:empty`, `:first-child`, `:last-child`, `:only-child`,
//!   `:nth-child()`, `:nth-last-child()` and the `-of-type` forms (§15); `:is()`, `:not()`,
//!   `:where()` (§4); the user action pseudo-classes `:hover`, `:active`, `:focus`,
//!   `:focus-visible`, `:focus-within` (§11); the four combinators (§16); and the
//!   pseudo-elements `::before`, `::after`, `::first-line`, `::first-letter`, in both
//!   spellings. Everything else is a selector this UA has "no usable level of support"
//!   for, which §3.10's note says UAs "must treat as invalid": `:has()` (deferred to Phase
//!   8, because its matching is not linear), the `of S` argument of `:nth-child()` and
//!   `:nth-last-child()`, the other pseudo-classes and pseudo-elements, and every
//!   functional pseudo-element.
//! - **meaning** `:visited` never matches. No history reaches a renderer, which also closes
//!   the history-sniffing channel §9.2's note describes. So `:link` matches every element
//!   HTML says matches "one of `:link` and `:visited`".
//! - **meaning** The user action pseudo-classes parse and never match: this phase has no
//!   pointer or focus.
//! - **meaning** A pseudo-element is only valid at the end of a complex selector, followed by
//!   nothing but user action pseudo-classes (§18's note: "a pseudo-element-selector is only
//!   valid if placed at the end of the last compound-selector", and "the user action
//!   pseudo-classes are allowed after any pseudo-element"). No sub-pseudo-element of the
//!   supported four exists, so a second one is invalid. A pseudo-element is folded into the
//!   last compound selector's list of simple selectors, followed by its pseudo-classes, and
//!   matches no element (§3.6: it is not an element), which is what "match a selector
//!   against an element" needs.
//! - **meaning** No namespace prefix is declared (§3.9: CSS declares them with `@namespace`,
//!   which item 5.5 does not parse), so there is no default namespace, and a named prefix
//!   is "an undeclared namespace prefix", which makes the selector invalid. Step 2 of
//!   "parse a selector" is folded into the grammar: a named prefix is rejected where it is
//!   read.
//! - **meaning** Every document is an HTML document: the arenas are built by the HTML
//!   parser. So HTML's case rules (§4.16.2) apply to every HTML element.
//! - **meaning** `A` and `B` of `<an+b>` are clamped to the 32-bit signed range, as CSS Values
//!   4 §5.1 allows for integers out of an implementation's range ("must be clamped").
//! - The grammar is matched by recursive descent, one production per function. §18's
//!   grammar is unambiguous once its whitespace rules are applied: each alternative starts
//!   with a different token, except `<wq-name>` and `<ns-prefix>`, which the next one or
//!   two tokens decide, so the one way the descent can match is the grammar's match.
//! - `#` ("one or more, comma-separated") on a list of component values from the parser is
//!   a split at its `<comma-token>`s: every block in such a list is already a simple block
//!   or a function, so a comma at the top of the list is the only kind there is. "Parse a
//!   list" (CSS Syntax §5.4.2) on such a list splits the same way, except that a comma at
//!   the end starts no further item, as its step 3's "while input is not empty" says. Both
//!   work on index ranges of one list, so that every function here recurses into a part of
//!   its argument.
//! - "Match a complex selector" considers "all possible elements that could be related to
//!   this element by the rightmost combinator". Those are found by walking: ancestors by
//!   following parents at most as many times as the arena has nodes (in a well-formed arena
//!   every chain of parents ends sooner, `clazel_dom::lemmas::lemma_ancestor_iff_path`), and
//!   earlier siblings by index in the parent's children.
//! - "Inclusive siblings" of an element without a parent are the element alone (§15's
//!   note: these pseudo-classes match "elements without parents").
//! - "Document white space characters" (`:empty`) are CSS Text 3's tabs, spaces and segment
//!   breaks, which in an HTML document are U+0009, U+000A, U+000C, U+000D and U+0020, the
//!   characters HTML's inter-element whitespace is made of.
//! - **meaning** Specificity components saturate at `u32::MAX` at every addition. §17:
//!   "implementations may have limitations on the size of A, B, or C. If so, values higher
//!   than the limit must be clamped to that limit, and not overflow." No selector reaches
//!   the limit: each component counts simple selectors of a selector read from at most
//!   `MAX_PARSER_INPUT` (2^29) code points.
//! - "Represents any index i = An + B for any non-negative integer n" is evaluated
//!   arithmetically ([`nth_index_matches`]); `lemmas::lemma_nth_index_matches` proves it equal
//!   to the existential.
//! - CSSOM's "serialize a selector" names neither `:is()` and `:where()` (serialized as
//!   `:not()` is, "a group of selectors"), nor the `s` flag (serialized as `i` is), nor a
//!   `*|` prefix when no default namespace exists (left out on type and universal selectors,
//!   where it changes nothing, and kept on attribute selectors, where it does); these follow
//!   what engines print, which is what WPT's `css/selectors/parsing` expects. Pseudo-class
//!   and pseudo-element names are printed in lowercase, as engines do.

pub use clazel_css::parser::spec::*;
pub use clazel_dom::spec::{Attr, Document, DocumentMode, Namespace, NodeId, NodeKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// The parsed form
// ------------------------------------------------------------------------------------

/// §5.3 the namespace component of a type, universal or attribute selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NsPrefix {
    /// No `|` at all.
    Absent,
    /// `*|`: "in any namespace, including those without a namespace".
    Any,
    /// `|`: "without a namespace".
    NoNamespace,
}

/// §6 `<attr-matcher>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttrMatcher {
    /// `=`
    Equals,
    /// `~=`
    Includes,
    /// `|=`
    DashMatch,
    /// `^=`
    Prefix,
    /// `$=`
    Suffix,
    /// `*=`
    Substring,
}

/// §6.3 `<attr-modifier>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseFlag {
    /// `i`: "match the attribute's value ASCII case-insensitively".
    I,
    /// `s`: "match the value case-sensitively".
    S,
}

/// The pseudo-classes of the subset that take no argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PseudoClass {
    /// §9.2 `:link`
    Link,
    /// §9.2 `:visited`
    Visited,
    /// §9.1 `:any-link`
    AnyLink,
    /// §15.1 `:root`
    Root,
    /// §15.2 `:empty`
    Empty,
    /// §15.3.3 `:first-child`
    FirstChild,
    /// §15.3.4 `:last-child`
    LastChild,
    /// §15.3.5 `:only-child`
    OnlyChild,
    /// §15.4.3 `:first-of-type`
    FirstOfType,
    /// §15.4.4 `:last-of-type`
    LastOfType,
    /// §15.4.5 `:only-of-type`
    OnlyOfType,
    /// §11.2 `:hover`
    Hover,
    /// §11.3 `:active`
    Active,
    /// §11.4 `:focus`
    Focus,
    /// §11.5 `:focus-visible`
    FocusVisible,
    /// §11.6 `:focus-within`
    FocusWithin,
}

/// The four child-indexed pseudo-classes that take `<an+b>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NthKind {
    /// §15.3.1 `:nth-child()`
    Child,
    /// §15.3.2 `:nth-last-child()`
    LastChild,
    /// §15.4.1 `:nth-of-type()`
    OfType,
    /// §15.4.2 `:nth-last-of-type()`
    LastOfType,
}

/// The pseudo-elements of the subset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PseudoElement {
    /// `::before`
    Before,
    /// `::after`
    After,
    /// `::first-line`
    FirstLine,
    /// `::first-letter`
    FirstLetter,
}

/// §16 `<combinator>`, and the descendant combinator, which is whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Combinator {
    /// §16.1 " "
    Descendant,
    /// §16.2 `>`
    Child,
    /// §16.3 `+`
    NextSibling,
    /// §16.4 `~`
    SubsequentSibling,
}

/// The value part of an attribute selector: `<attr-matcher>`, the value, `<attr-modifier>?`.
pub ghost struct AttrTest {
    /// The matcher.
    pub matcher: AttrMatcher,
    /// The value of the `<string-token>` or `<ident-token>`.
    pub value: Seq<u32>,
    /// The flag, if any.
    pub flag: Option<CaseFlag>,
}

/// §3.1 simple selector, and a pseudo-element (modelling choices).
pub ghost enum Simple {
    /// §5.1 type selector: a namespace component and the name as written.
    Type {
        /// The namespace component.
        ns: NsPrefix,
        /// The name, as written.
        name: Seq<u32>,
    },
    /// §5.2 universal selector.
    Universal {
        /// The namespace component.
        ns: NsPrefix,
    },
    /// §7 ID selector.
    Id {
        /// The identifier.
        name: Seq<u32>,
    },
    /// §6.6 class selector.
    Class {
        /// The identifier.
        name: Seq<u32>,
    },
    /// §6 attribute selector.
    Attribute {
        /// The namespace component.
        ns: NsPrefix,
        /// The attribute name, as written.
        name: Seq<u32>,
        /// The matcher, value and flag; none for `[att]`.
        test: Option<AttrTest>,
    },
    /// A pseudo-class without an argument.
    PseudoClass {
        /// Which.
        class: PseudoClass,
    },
    /// `:nth-child(An+B)` and the other three.
    Nth {
        /// Which.
        kind: NthKind,
        /// A, clamped.
        a: int,
        /// B, clamped.
        b: int,
    },
    /// §4.2 `:is()`, with its forgiving argument after parsing.
    Is {
        /// The selector list.
        arg: Seq<Complex>,
    },
    /// §4.4 `:where()`.
    Where {
        /// The selector list.
        arg: Seq<Complex>,
    },
    /// §4.3 `:not()`.
    Not {
        /// The selector list.
        arg: Seq<Complex>,
    },
    /// A pseudo-element.
    PseudoElement {
        /// Which.
        element: PseudoElement,
    },
}

/// §3.1 complex selector: compound selectors, each a sequence of simple selectors, and the
/// combinator between each two. `combinators[k]` stands between `compounds[k]` and
/// `compounds[k + 1]`, so a well-formed one has one combinator fewer than compounds.
pub ghost struct Complex {
    /// The compound selectors, left to right.
    pub compounds: Seq<Seq<Simple>>,
    /// The combinators, left to right.
    pub combinators: Seq<Combinator>,
}

/// What a step of the descent finds at a position.
pub ghost enum Step<T> {
    /// Nothing of this production starts here.
    Absent,
    /// The production, and the index after it.
    Found {
        /// What was read.
        value: T,
        /// The index after it.
        next: int,
    },
    /// The production starts here and is malformed: the selector is invalid.
    Invalid,
}

// ------------------------------------------------------------------------------------
// Names
// ------------------------------------------------------------------------------------

/// "is"
pub open spec fn str_is() -> Seq<u32> {
    seq![0x69u32, 0x73]
}

/// "where"
pub open spec fn str_where() -> Seq<u32> {
    seq![0x77u32, 0x68, 0x65, 0x72, 0x65]
}

/// "not"
pub open spec fn str_not() -> Seq<u32> {
    seq![0x6Eu32, 0x6F, 0x74]
}

/// "nth-child"
pub open spec fn str_nth_child() -> Seq<u32> {
    seq![0x6Eu32, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]
}

/// "nth-last-child"
pub open spec fn str_nth_last_child() -> Seq<u32> {
    seq![0x6Eu32, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]
}

/// "nth-of-type"
pub open spec fn str_nth_of_type() -> Seq<u32> {
    seq![0x6Eu32, 0x74, 0x68, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65]
}

/// "nth-last-of-type"
pub open spec fn str_nth_last_of_type() -> Seq<u32> {
    seq![
        0x6Eu32, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79,
        0x70, 0x65,
    ]
}

/// The lowercase name of a pseudo-class without an argument.
pub open spec fn pseudo_class_name(class: PseudoClass) -> Seq<u32> {
    match class {
        PseudoClass::Link => seq![0x6Cu32, 0x69, 0x6E, 0x6B],
        PseudoClass::Visited => seq![0x76u32, 0x69, 0x73, 0x69, 0x74, 0x65, 0x64],
        PseudoClass::AnyLink => seq![0x61u32, 0x6E, 0x79, 0x2D, 0x6C, 0x69, 0x6E, 0x6B],
        PseudoClass::Root => seq![0x72u32, 0x6F, 0x6F, 0x74],
        PseudoClass::Empty => seq![0x65u32, 0x6D, 0x70, 0x74, 0x79],
        PseudoClass::FirstChild => seq![
            0x66u32, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64,
        ],
        PseudoClass::LastChild => seq![0x6Cu32, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        PseudoClass::OnlyChild => seq![0x6Fu32, 0x6E, 0x6C, 0x79, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
        PseudoClass::FirstOfType => seq![
            0x66u32, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65,
        ],
        PseudoClass::LastOfType => seq![
            0x6Cu32, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65,
        ],
        PseudoClass::OnlyOfType => seq![
            0x6Fu32, 0x6E, 0x6C, 0x79, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65,
        ],
        PseudoClass::Hover => seq![0x68u32, 0x6F, 0x76, 0x65, 0x72],
        PseudoClass::Active => seq![0x61u32, 0x63, 0x74, 0x69, 0x76, 0x65],
        PseudoClass::Focus => seq![0x66u32, 0x6F, 0x63, 0x75, 0x73],
        PseudoClass::FocusVisible => seq![
            0x66u32, 0x6F, 0x63, 0x75, 0x73, 0x2D, 0x76, 0x69, 0x73, 0x69, 0x62, 0x6C, 0x65,
        ],
        PseudoClass::FocusWithin => seq![
            0x66u32, 0x6F, 0x63, 0x75, 0x73, 0x2D, 0x77, 0x69, 0x74, 0x68, 0x69, 0x6E,
        ],
    }
}

/// The lowercase name of a pseudo-element.
pub open spec fn pseudo_element_name(element: PseudoElement) -> Seq<u32> {
    match element {
        PseudoElement::Before => seq![0x62u32, 0x65, 0x66, 0x6F, 0x72, 0x65],
        PseudoElement::After => seq![0x61u32, 0x66, 0x74, 0x65, 0x72],
        PseudoElement::FirstLine => seq![0x66u32, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x69, 0x6E, 0x65],
        PseudoElement::FirstLetter => seq![
            0x66u32, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6C, 0x65, 0x74, 0x74, 0x65, 0x72,
        ],
    }
}

/// The lowercase name of an `<an+b>` pseudo-class.
pub open spec fn nth_name(kind: NthKind) -> Seq<u32> {
    match kind {
        NthKind::Child => str_nth_child(),
        NthKind::LastChild => str_nth_last_child(),
        NthKind::OfType => str_nth_of_type(),
        NthKind::LastOfType => str_nth_last_of_type(),
    }
}

/// §3.7 "All syntax defined by the Selectors spec is ASCII case-insensitive": the
/// pseudo-class without an argument that `name` names, if the subset has it.
pub open spec fn pseudo_class_named(name: Seq<u32>) -> Option<PseudoClass> {
    if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Link)) {
        Some(PseudoClass::Link)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Visited)) {
        Some(PseudoClass::Visited)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::AnyLink)) {
        Some(PseudoClass::AnyLink)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Root)) {
        Some(PseudoClass::Root)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Empty)) {
        Some(PseudoClass::Empty)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FirstChild)) {
        Some(PseudoClass::FirstChild)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::LastChild)) {
        Some(PseudoClass::LastChild)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::OnlyChild)) {
        Some(PseudoClass::OnlyChild)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FirstOfType)) {
        Some(PseudoClass::FirstOfType)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::LastOfType)) {
        Some(PseudoClass::LastOfType)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::OnlyOfType)) {
        Some(PseudoClass::OnlyOfType)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Hover)) {
        Some(PseudoClass::Hover)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Active)) {
        Some(PseudoClass::Active)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::Focus)) {
        Some(PseudoClass::Focus)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FocusVisible)) {
        Some(PseudoClass::FocusVisible)
    } else if ascii_case_insensitive_match(name, pseudo_class_name(PseudoClass::FocusWithin)) {
        Some(PseudoClass::FocusWithin)
    } else {
        None
    }
}

/// The pseudo-element that `name` names, if the subset has it.
pub open spec fn pseudo_element_named(name: Seq<u32>) -> Option<PseudoElement> {
    if ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::Before)) {
        Some(PseudoElement::Before)
    } else if ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::After)) {
        Some(PseudoElement::After)
    } else if ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::FirstLine)) {
        Some(PseudoElement::FirstLine)
    } else if ascii_case_insensitive_match(name, pseudo_element_name(PseudoElement::FirstLetter)) {
        Some(PseudoElement::FirstLetter)
    } else {
        None
    }
}

/// The `<an+b>` pseudo-class that `name` names.
pub open spec fn nth_named(name: Seq<u32>) -> Option<NthKind> {
    if ascii_case_insensitive_match(name, str_nth_child()) {
        Some(NthKind::Child)
    } else if ascii_case_insensitive_match(name, str_nth_last_child()) {
        Some(NthKind::LastChild)
    } else if ascii_case_insensitive_match(name, str_nth_of_type()) {
        Some(NthKind::OfType)
    } else if ascii_case_insensitive_match(name, str_nth_last_of_type()) {
        Some(NthKind::LastOfType)
    } else {
        None
    }
}

/// §11 "user action pseudo-classes", the ones "allowed after any pseudo-element".
pub open spec fn is_user_action(class: PseudoClass) -> bool {
    class == PseudoClass::Hover || class == PseudoClass::Active || class == PseudoClass::Focus
        || class == PseudoClass::FocusVisible || class == PseudoClass::FocusWithin
}

/// The lowest `A` or `B` kept (modelling choices).
pub open spec fn int_min() -> int {
    -0x8000_0000
}

/// The highest `A` or `B` kept (modelling choices).
pub open spec fn int_max() -> int {
    0x7FFF_FFFF
}

/// `n` clamped to the 32-bit signed range.
pub open spec fn clamp(n: int) -> int {
    if n < int_min() {
        int_min()
    } else if n > int_max() {
        int_max()
    } else {
        n
    }
}

// ------------------------------------------------------------------------------------
// §18 Grammar: reading the items of a list of component values
// ------------------------------------------------------------------------------------

/// The item at `i`, if it is a token, below `hi`.
pub open spec fn token_at(items: Seq<ComponentValue>, i: int, hi: int) -> Option<Token> {
    if 0 <= i < hi && hi <= items.len() {
        match items[i] {
            ComponentValue::Token { token } => Some(token),
            _ => None,
        }
    } else {
        None
    }
}

/// True if the item at `i` is the `<delim-token>` `c`.
pub open spec fn is_delim_at(items: Seq<ComponentValue>, i: int, hi: int, c: u32) -> bool {
    token_at(items, i, hi) == Some(Token::Delim { value: c })
}

/// True if the item at `i` is `token`.
pub open spec fn is_token_at(items: Seq<ComponentValue>, i: int, hi: int, token: Token) -> bool {
    token_at(items, i, hi) == Some(token)
}

/// The value of the `<ident-token>` at `i`, if there is one.
pub open spec fn ident_at(items: Seq<ComponentValue>, i: int, hi: int) -> Option<Seq<u32>> {
    match token_at(items, i, hi) {
        Some(Token::Ident { value }) => Some(value),
        _ => None,
    }
}

/// How many `<whitespace-token>`s follow each other from `i` on, below `hi`.
pub open spec fn whitespace_run(items: Seq<ComponentValue>, i: int, hi: int) -> nat
    decreases hi - i,
{
    if i < 0 || i >= hi || hi > items.len() || !is_whitespace_token(items[i]) {
        0
    } else {
        1 + whitespace_run(items, i + 1, hi)
    }
}

/// The index of the first item at or after `i` that is not a `<whitespace-token>`, or `hi`.
pub open spec fn skip_whitespace(items: Seq<ComponentValue>, i: int, hi: int) -> int {
    i + whitespace_run(items, i, hi)
}

/// The index of the first `<comma-token>` at or after `i`, or `hi`.
pub open spec fn next_comma(items: Seq<ComponentValue>, i: int, hi: int) -> int
    decreases hi - i,
{
    if i >= hi || i < 0 || hi > items.len() {
        if i < hi {
            hi
        } else {
            i
        }
    } else if is(items[i], Token::Comma) {
        i
    } else {
        next_comma(items, i + 1, hi)
    }
}

/// True if the items from `i` up to `hi` are all `<whitespace-token>`s.
pub open spec fn only_whitespace(items: Seq<ComponentValue>, i: int, hi: int) -> bool {
    skip_whitespace(items, i, hi) >= hi
}

// ------------------------------------------------------------------------------------
// §18 Grammar: the productions without selectors inside
// ------------------------------------------------------------------------------------

/// §18 `<type-selector> = <wq-name> | <ns-prefix>? '*'`, with `<wq-name> = <ns-prefix>?
/// <ident-token>` and `<ns-prefix> = [ <ident-token> | '*' ]? '|'`. "White space is
/// forbidden … between any of the components of a <type-selector>", so they are adjacent
/// items.
pub open spec fn type_selector(items: Seq<ComponentValue>, i: int, hi: int) -> Step<Simple> {
    match ident_at(items, i, hi) {
        Some(name) => if is_delim_at(items, i + 1, hi, 0x7C) {
            // "ident |": a named <ns-prefix>, which is undeclared, so "a simple selector
            // containing an undeclared namespace prefix is invalid" (§3.10). The other
            // reading, "ident" and then '|', has nothing the grammar lets follow: '|' starts
            // no <subclass-selector> and no <combinator>.
            Step::Invalid
        } else {
            Step::Found { value: Simple::Type { ns: NsPrefix::Absent, name }, next: i + 1 }
        },
        None => if is_delim_at(items, i, hi, 0x2A) {
            if is_delim_at(items, i + 1, hi, 0x7C) {
                // '*' '|': "*|E" or "*|*".
                match ident_at(items, i + 2, hi) {
                    Some(name) => Step::Found {
                        value: Simple::Type { ns: NsPrefix::Any, name },
                        next: i + 3,
                    },
                    None => if is_delim_at(items, i + 2, hi, 0x2A) {
                        Step::Found { value: Simple::Universal { ns: NsPrefix::Any }, next: i + 3 }
                    } else {
                        Step::Invalid
                    },
                }
            } else {
                // '*'
                Step::Found { value: Simple::Universal { ns: NsPrefix::Absent }, next: i + 1 }
            }
        } else if is_delim_at(items, i, hi, 0x7C) {
            // '|': "|E" or "|*".
            match ident_at(items, i + 1, hi) {
                Some(name) => Step::Found {
                    value: Simple::Type { ns: NsPrefix::NoNamespace, name },
                    next: i + 2,
                },
                None => if is_delim_at(items, i + 1, hi, 0x2A) {
                    Step::Found {
                        value: Simple::Universal { ns: NsPrefix::NoNamespace },
                        next: i + 2,
                    }
                } else {
                    Step::Invalid
                },
            }
        } else {
            Step::Absent
        },
    }
}

/// The `<wq-name>` of an attribute selector at `i` of `v`, as (namespace, name, next).
/// "Default namespaces do not apply to attributes" (§6.4), so no prefix is `|`'s meaning.
pub open spec fn attribute_name(v: Seq<ComponentValue>, i: int) -> Option<(NsPrefix, Seq<u32>, int)> {
    let hi = v.len() as int;
    match ident_at(v, i, hi) {
        Some(name) => if is_delim_at(v, i + 1, hi, 0x7C) && ident_at(v, i + 2, hi) is Some {
            // A named <ns-prefix>: undeclared, so invalid (§6.4: "an invalid selector").
            None
        } else {
            Some((NsPrefix::Absent, name, i + 1))
        },
        None => if is_delim_at(v, i, hi, 0x2A) && is_delim_at(v, i + 1, hi, 0x7C) {
            match ident_at(v, i + 2, hi) {
                Some(name) => Some((NsPrefix::Any, name, i + 3)),
                None => None,
            }
        } else if is_delim_at(v, i, hi, 0x7C) {
            match ident_at(v, i + 1, hi) {
                Some(name) => Some((NsPrefix::NoNamespace, name, i + 2)),
                None => None,
            }
        } else {
            None
        },
    }
}

/// §18 `<attr-matcher> = [ '~' | '|' | '^' | '$' | '*' ]? '='` at `i`, as (matcher, next).
/// "White space is forbidden … between the components of an <attr-matcher>."
pub open spec fn attr_matcher(v: Seq<ComponentValue>, i: int) -> Option<(AttrMatcher, int)> {
    let hi = v.len() as int;
    if is_delim_at(v, i, hi, 0x3D) {
        Some((AttrMatcher::Equals, i + 1))
    } else if is_delim_at(v, i + 1, hi, 0x3D) {
        if is_delim_at(v, i, hi, 0x7E) {
            Some((AttrMatcher::Includes, i + 2))
        } else if is_delim_at(v, i, hi, 0x7C) {
            Some((AttrMatcher::DashMatch, i + 2))
        } else if is_delim_at(v, i, hi, 0x5E) {
            Some((AttrMatcher::Prefix, i + 2))
        } else if is_delim_at(v, i, hi, 0x24) {
            Some((AttrMatcher::Suffix, i + 2))
        } else if is_delim_at(v, i, hi, 0x2A) {
            Some((AttrMatcher::Substring, i + 2))
        } else {
            None
        }
    } else {
        None
    }
}

/// §18 `<attribute-selector> = '[' <wq-name> ']' | '[' <wq-name> <attr-matcher> [
/// <string-token> | <ident-token> ] <attr-modifier>? ']'`, on the value of the `[]` block.
/// White space may stand between the components, and at either end.
pub open spec fn attribute_selector(v: Seq<ComponentValue>) -> Option<Simple> {
    let hi = v.len() as int;
    match attribute_name(v, skip_whitespace(v, 0, hi)) {
        None => None,
        Some((ns, name, after_name)) => {
            let at_matcher = skip_whitespace(v, after_name, hi);
            if at_matcher >= hi {
                // '[' <wq-name> ']'
                Some(Simple::Attribute { ns, name, test: None })
            } else {
                match attr_matcher(v, at_matcher) {
                    None => None,
                    Some((matcher, after_matcher)) => {
                        let at_value = skip_whitespace(v, after_matcher, hi);
                        // [ <string-token> | <ident-token> ]
                        let value = match token_at(v, at_value, hi) {
                            Some(Token::String { value }) => Some(value),
                            Some(Token::Ident { value }) => Some(value),
                            _ => None,
                        };
                        match value {
                            None => None,
                            Some(value) => {
                                let at_modifier = skip_whitespace(v, at_value + 1, hi);
                                if at_modifier >= hi {
                                    Some(
                                        Simple::Attribute {
                                            ns,
                                            name,
                                            test: Some(AttrTest { matcher, value, flag: None }),
                                        },
                                    )
                                } else {
                                    // <attr-modifier> = i | s, ASCII case-insensitively.
                                    let flag = match ident_at(v, at_modifier, hi) {
                                        Some(m) => if ascii_case_insensitive_match(
                                            m,
                                            seq![0x69u32],
                                        ) {
                                            Some(CaseFlag::I)
                                        } else if ascii_case_insensitive_match(m, seq![0x73u32]) {
                                            Some(CaseFlag::S)
                                        } else {
                                            None
                                        },
                                        None => None,
                                    };
                                    if flag is Some && skip_whitespace(v, at_modifier + 1, hi)
                                        >= hi {
                                        Some(
                                            Simple::Attribute {
                                                ns,
                                                name,
                                                test: Some(AttrTest { matcher, value, flag }),
                                            },
                                        )
                                    } else {
                                        None
                                    }
                                }
                            },
                        }
                    },
                }
            }
        },
    }
}

/// §18 `<pseudo-element-selector> = : <pseudo-class-selector> |
/// <legacy-pseudo-element-selector>` at `i`, for the four the subset has.
pub open spec fn pseudo_element(items: Seq<ComponentValue>, i: int, hi: int) -> Step<PseudoElement> {
    if is_token_at(items, i, hi, Token::Colon) {
        if is_token_at(items, i + 1, hi, Token::Colon) {
            // ':' ':' <ident-token>; a functional pseudo-element is not in the subset.
            match ident_at(items, i + 2, hi) {
                Some(name) => match pseudo_element_named(name) {
                    Some(element) => Step::Found { value: element, next: i + 3 },
                    None => Step::Invalid,
                },
                None => Step::Invalid,
            }
        } else {
            // <legacy-pseudo-element-selector> = ':' [before | after | first-line |
            // first-letter]
            match ident_at(items, i + 1, hi) {
                Some(name) => match pseudo_element_named(name) {
                    Some(element) => Step::Found { value: element, next: i + 2 },
                    None => Step::Absent,
                },
                None => Step::Absent,
            }
        }
    } else {
        Step::Absent
    }
}

/// A user action pseudo-class after a pseudo-element, at `i`.
pub open spec fn user_action(items: Seq<ComponentValue>, i: int, hi: int) -> Step<PseudoClass> {
    if is_token_at(items, i, hi, Token::Colon) {
        match ident_at(items, i + 1, hi) {
            Some(name) => match pseudo_class_named(name) {
                Some(class) => if is_user_action(class) {
                    Step::Found { value: class, next: i + 2 }
                } else {
                    Step::Invalid
                },
                None => Step::Invalid,
            },
            None => Step::Invalid,
        }
    } else {
        Step::Absent
    }
}

/// `<pseudo-class-selector>*` after a pseudo-element: user action pseudo-classes only, each
/// adjacent to the last ("white space is forbidden … between the <pseudo-element-selector>
/// and <pseudo-class-selector>").
pub open spec fn user_actions(items: Seq<ComponentValue>, i: int, hi: int, acc: Seq<Simple>) -> Option<
    (Seq<Simple>, int),
>
    decreases hi - i,
{
    match user_action(items, i, hi) {
        Step::Absent => Some((acc, i)),
        Step::Invalid => None,
        Step::Found { value, next } => if next > i && next <= hi {
            user_actions(items, next, hi, acc.push(Simple::PseudoClass { class: value }))
        } else {
            None
        },
    }
}

/// §18 `<pseudo-compound-selector> = <pseudo-element-selector> <pseudo-class-selector>*`,
/// optionally, after a compound selector's simple selectors `acc` (modelling choices). A
/// `<complex-no_pseudo-selector>` has none.
pub open spec fn pseudo_compound(
    items: Seq<ComponentValue>,
    i: int,
    hi: int,
    acc: Seq<Simple>,
    no_pseudo: bool,
) -> Option<(Seq<Simple>, int)> {
    match pseudo_element(items, i, hi) {
        Step::Absent => Some((acc, i)),
        Step::Invalid => None,
        Step::Found { value, next } => if no_pseudo {
            // §4.2, §4.3: "Pseudo-elements … are not valid within :is()", nor ":not()".
            None
        } else {
            user_actions(items, next, hi, acc.push(Simple::PseudoElement { element: value }))
        },
    }
}

/// True if one of the first `k` simple selectors of a compound selector is a pseudo-element.
pub open spec fn pseudo_element_within(compound: Seq<Simple>, k: int) -> bool
    decreases k,
{
    if k <= 0 || k > compound.len() {
        false
    } else {
        compound[k - 1] is PseudoElement || pseudo_element_within(compound, k - 1)
    }
}

/// True if a compound selector holds a pseudo-element.
pub open spec fn has_pseudo_element(compound: Seq<Simple>) -> bool {
    pseudo_element_within(compound, compound.len() as int)
}

// ------------------------------------------------------------------------------------
// §18 Grammar: the productions with selectors inside
// ------------------------------------------------------------------------------------

/// The functional pseudo-classes of the subset: `name(` `value` `)`.
pub open spec fn functional_pseudo_class(name: Seq<u32>, value: Seq<ComponentValue>) -> Option<Simple>
    decreases value, value.len() + 1, 0int,
{
    if ascii_case_insensitive_match(name, str_is()) {
        // §4.2: ":is() … taking a <forgiving-selector-list> as its sole argument."
        Some(Simple::Is { arg: parse_as_a_forgiving_selector_list(value) })
    } else if ascii_case_insensitive_match(name, str_where()) {
        // §4.4: "the same syntax and functionality as :is()".
        Some(Simple::Where { arg: parse_as_a_forgiving_selector_list(value) })
    } else if ascii_case_insensitive_match(name, str_not()) {
        // §4.3: ":not() … taking a <complex-no_pseudo-selector-list> as an argument."
        match complex_list(value, 0, value.len() as int, true) {
            Some(arg) => Some(Simple::Not { arg }),
            None => None,
        }
    } else {
        match nth_named(name) {
            // §15.3.1 ":nth-child(An+B [of S]? )": the subset has no "of S", so the argument
            // is <an+b> alone.
            Some(kind) => match a_n_plus_b(value) {
                Some((a, b)) => Some(Simple::Nth { kind, a: clamp(a), b: clamp(b) }),
                None => None,
            },
            None => None,
        }
    }
}

/// §18 `<subclass-selector> = <id-selector> | <class-selector> | <attribute-selector> |
/// <pseudo-class-selector>` at `i`. A ':' that starts a pseudo-element is not one: "the
/// <pseudo-class-selector> production excludes the <legacy-pseudo-element-selector>
/// production".
pub open spec fn subclass_selector(items: Seq<ComponentValue>, i: int, hi: int) -> Step<Simple>
    decreases items, hi - i, 0int,
{
    if i < 0 || i >= hi || hi > items.len() {
        Step::Absent
    } else {
        match items[i] {
            // <id-selector> = <hash-token>: "the <hash-token>'s value must be an identifier",
            // that is, its type flag is "id".
            ComponentValue::Token { token: Token::Hash { value, is_id } } => if is_id {
                Step::Found { value: Simple::Id { name: value }, next: i + 1 }
            } else {
                Step::Invalid
            },
            // <class-selector> = '.' <ident-token>
            ComponentValue::Token { token: Token::Delim { value: 0x2E } } => match ident_at(
                items,
                i + 1,
                hi,
            ) {
                Some(name) => Step::Found { value: Simple::Class { name }, next: i + 2 },
                None => Step::Invalid,
            },
            // <attribute-selector>: '[' … ']' is a simple block.
            ComponentValue::SimpleBlock { associated_token: Token::OpenSquare, value } => match
            attribute_selector(value) {
                Some(simple) => Step::Found { value: simple, next: i + 1 },
                None => Step::Invalid,
            },
            // <pseudo-class-selector> = ':' <ident-token> | ':' <function-token> <any-value> ')'
            ComponentValue::Token { token: Token::Colon } => if is_token_at(
                items,
                i + 1,
                hi,
                Token::Colon,
            ) {
                Step::Absent
            } else if i + 1 < hi {
                match items[i + 1] {
                    ComponentValue::Token { token: Token::Ident { value: name } } => if pseudo_element_named(name) is Some {
                        Step::Absent
                    } else {
                        match pseudo_class_named(name) {
                            Some(class) => Step::Found {
                                value: Simple::PseudoClass { class },
                                next: i + 2,
                            },
                            None => Step::Invalid,
                        }
                    },
                    ComponentValue::Function { name, value } => match functional_pseudo_class(
                        name,
                        value,
                    ) {
                        Some(simple) => Step::Found { value: simple, next: i + 2 },
                        None => Step::Invalid,
                    },
                    _ => Step::Invalid,
                }
            } else {
                Step::Invalid
            },
            _ => Step::Absent,
        }
    }
}

/// `<subclass-selector>*`, then the optional pseudo-compound selector, after the simple
/// selectors `acc`. "White space is forbidden between any of the top-level components of a
/// <compound-selector>", so each starts where the last ended.
pub open spec fn subclass_selectors(
    items: Seq<ComponentValue>,
    i: int,
    hi: int,
    acc: Seq<Simple>,
    no_pseudo: bool,
) -> Option<(Seq<Simple>, int)>
    decreases items, hi - i, 1int,
{
    match subclass_selector(items, i, hi) {
        Step::Invalid => None,
        Step::Found { value, next } => if i < next && next <= hi {
            subclass_selectors(items, next, hi, acc.push(value), no_pseudo)
        } else {
            None
        },
        Step::Absent => pseudo_compound(items, i, hi, acc, no_pseudo),
    }
}

/// §18 `<compound-selector> = [ <type-selector>? <subclass-selector>* ]!` at `i`, with the
/// pseudo-compound selector of `<complex-selector-unit>` folded in (modelling choices).
/// Empty is not an error here; the caller sees that nothing was read.
pub open spec fn compound_selector(items: Seq<ComponentValue>, i: int, hi: int, no_pseudo: bool) -> Option<
    (Seq<Simple>, int),
>
    decreases items, hi - i, 2int,
{
    match type_selector(items, i, hi) {
        Step::Invalid => None,
        Step::Absent => subclass_selectors(items, i, hi, Seq::empty(), no_pseudo),
        Step::Found { value, next } => if i < next && next <= hi {
            subclass_selectors(items, next, hi, seq![value], no_pseudo)
        } else {
            None
        },
    }
}

/// The `<combinator>` at `i`: `'>' | '+' | '~'`.
pub open spec fn combinator_at(items: Seq<ComponentValue>, i: int, hi: int) -> Option<Combinator> {
    if is_delim_at(items, i, hi, 0x3E) {
        Some(Combinator::Child)
    } else if is_delim_at(items, i, hi, 0x2B) {
        Some(Combinator::NextSibling)
    } else if is_delim_at(items, i, hi, 0x7E) {
        Some(Combinator::SubsequentSibling)
    } else {
        None
    }
}

/// §18 `<complex-selector> = <complex-selector-unit> [ <combinator>? <complex-selector-unit>
/// ]*` from the unit at `i` on, after the compounds and combinators read so far. "Whitespace
/// is required between two <complex-selector-unit>s if the <combinator> between them is
/// omitted. (This indicates the descendant combinator is being used.)"
pub open spec fn complex_selector_loop(
    items: Seq<ComponentValue>,
    i: int,
    hi: int,
    compounds: Seq<Seq<Simple>>,
    combinators: Seq<Combinator>,
    no_pseudo: bool,
) -> Option<Complex>
    decreases items, hi - i, 3int
{
    match compound_selector(items, i, hi, no_pseudo) {
        None => None,
        Some((compound, next)) => if next <= i || next > hi {
            // "[ … ]!": a unit must not be empty.
            None
        } else {
            let compounds = compounds.push(compound);
            let after = skip_whitespace(items, next, hi);
            if after >= hi {
                Some(Complex { compounds, combinators })
            } else if has_pseudo_element(compound) {
                // Nothing may follow a pseudo-element (modelling choices).
                None
            } else {
                match combinator_at(items, after, hi) {
                    Some(combinator) => {
                        let start = skip_whitespace(items, after + 1, hi);
                        if start >= hi {
                            None
                        } else {
                            complex_selector_loop(
                                items,
                                start,
                                hi,
                                compounds,
                                combinators.push(combinator),
                                no_pseudo,
                            )
                        }
                    },
                    None => if after > next {
                        complex_selector_loop(
                            items,
                            after,
                            hi,
                            compounds,
                            combinators.push(Combinator::Descendant),
                            no_pseudo,
                        )
                    } else {
                        None
                    },
                }
            }
        },
    }
}

/// `<complex-selector>` (or, if `no_pseudo`, `<complex-no_pseudo-selector>`) on the items from `lo` up
/// to `hi`, with white space allowed at either end. §3.10: "an empty selector, i.e. one that
/// contains no compound selector, is invalid."
pub open spec fn complex_selector(items: Seq<ComponentValue>, lo: int, hi: int, no_pseudo: bool) -> Option<
    Complex,
>
    decreases items, hi - lo, 4int,
{
    let start = skip_whitespace(items, lo, hi);
    if start >= hi || start < lo {
        None
    } else {
        complex_selector_loop(items, start, hi, Seq::empty(), Seq::empty(), no_pseudo)
    }
}

/// `<complex-selector>#` (or `<complex-no_pseudo-selector>#`) from `i` up to `hi`, after the
/// selectors read so far. "A selector list containing an invalid selector is invalid."
pub open spec fn complex_list_loop(
    items: Seq<ComponentValue>,
    i: int,
    hi: int,
    acc: Seq<Complex>,
    no_pseudo: bool,
) -> Option<Seq<Complex>>
    decreases items, hi - i, 5int,
{
    let comma = next_comma(items, i, hi);
    if i < 0 || comma < i || comma > hi {
        None
    } else {
        match complex_selector(items, i, comma, no_pseudo) {
            None => None,
            Some(selector) => if comma >= hi {
                Some(acc.push(selector))
            } else {
                complex_list_loop(items, comma + 1, hi, acc.push(selector), no_pseudo)
            },
        }
    }
}

/// `<complex-selector-list>` (or `<complex-no_pseudo-selector-list>`) on the items from `lo` up to
/// `hi`.
pub open spec fn complex_list(items: Seq<ComponentValue>, lo: int, hi: int, no_pseudo: bool) -> Option<
    Seq<Complex>,
>
    decreases items, hi - lo, 6int,
{
    complex_list_loop(items, lo, hi, Seq::empty(), no_pseudo)
}

/// §18.1 "parse as a forgiving selector list", from `i` up to `hi`, after the selectors kept
/// so far: CSS Syntax §5.4.2 "parse a list" step 3's loop, "while input is not empty", with
/// each item parsed as a `<complex-no_pseudo-selector>`, and "remove all failure items".
pub open spec fn forgiving_list_loop(
    items: Seq<ComponentValue>,
    i: int,
    hi: int,
    acc: Seq<Complex>,
) -> Seq<Complex>
    decreases items, hi - i, 5int,
{
    let comma = next_comma(items, i, hi);
    if i < 0 || i >= hi || comma < i || comma > hi {
        acc
    } else {
        let kept = match complex_selector(items, i, comma, true) {
            Some(selector) => acc.push(selector),
            None => acc,
        };
        if comma >= hi {
            kept
        } else {
            forgiving_list_loop(items, comma + 1, hi, kept)
        }
    }
}

/// §18.1 "parse as a forgiving selector list" on the value of `:is()` or `:where()`.
pub open spec fn parse_as_a_forgiving_selector_list(value: Seq<ComponentValue>) -> Seq<Complex>
    decreases value, value.len() as int, 7int,
{
    // 1. "Parse a list of <complex-no_pseudo-selector>s from input": CSS Syntax §5.4.2 step 2,
    // "If input contains only <whitespace-token>s, return an empty list."
    if only_whitespace(value, 0, value.len() as int) {
        Seq::empty()
    } else {
        // 3. "Remove all failure items from selector list, …, then return a <selector-list>
        // representing the remaining items."
        forgiving_list_loop(value, 0, value.len() as int, Seq::empty())
    }
}

/// `<selector-list> = <complex-selector-list>`, as a grammar for CSS Syntax.
pub open spec fn selector_list(value: Seq<ComponentValue>) -> Option<Seq<Complex>> {
    complex_list(value, 0, value.len() as int, false)
}

/// §21.1 "parse a selector" from the string `source`.
pub open spec fn parse_a_selector(source: Seq<u32>) -> Option<Seq<Complex>> {
    // 1. "Let selector be the result of parsing source as a <selector-list>. If this returns
    // failure, it's an invalid selector; return failure."
    // 2. "If selector is an invalid selector for any other reason (such as, for example,
    // containing an undeclared namespace prefix), return failure." Folded into the grammar
    // (modelling choices).
    // 3. "Otherwise, return selector."
    parse_something_according_to_a_css_grammar(
        Input::String { string: source },
        |value: Seq<ComponentValue>| selector_list(value),
    )
}

// ------------------------------------------------------------------------------------
// Elements, as the matching reads them
// ------------------------------------------------------------------------------------

/// True if `x` is an element of the arena.
pub open spec fn is_element(doc: Document, x: NodeId) -> bool {
    x < doc.nodes.len() && doc.nodes[x as int].kind is Element
}

/// The parent of `x`, if `x` is a node of the arena.
pub open spec fn parent_of(doc: Document, x: NodeId) -> Option<NodeId> {
    if x < doc.nodes.len() {
        doc.nodes[x as int].parent
    } else {
        None
    }
}

/// The children of `x`, if `x` is a node of the arena.
pub open spec fn children_of(doc: Document, x: NodeId) -> Seq<NodeId> {
    if x < doc.nodes.len() {
        doc.nodes[x as int].children
    } else {
        Seq::empty()
    }
}

/// An element's namespace.
pub open spec fn namespace_of(doc: Document, x: NodeId) -> Option<Namespace> {
    match doc.nodes[x as int].kind {
        NodeKind::Element { namespace, .. } => namespace,
        _ => None,
    }
}

/// An element's local name.
pub open spec fn local_name_of(doc: Document, x: NodeId) -> Seq<u32> {
    match doc.nodes[x as int].kind {
        NodeKind::Element { local_name, .. } => local_name,
        _ => Seq::empty(),
    }
}

/// An element's attribute list.
pub open spec fn attributes_of(doc: Document, x: NodeId) -> Seq<Attr> {
    match doc.nodes[x as int].kind {
        NodeKind::Element { attributes, .. } => attributes,
        _ => Seq::empty(),
    }
}

/// HTML: "an HTML element", an element in the HTML namespace; every document is an HTML
/// document (modelling choices).
pub open spec fn is_html_element(doc: Document, x: NodeId) -> bool {
    is_element(doc, x) && namespace_of(doc, x) == Some(Namespace::Html)
}

/// DOM §4.5 the document's mode is "quirks" (the arena's node 0 is its document).
pub open spec fn in_quirks_mode(doc: Document) -> bool {
    doc.nodes.len() > 0 && match doc.nodes[0].kind {
        NodeKind::Document { mode, .. } => mode == DocumentMode::Quirks,
        _ => false,
    }
}

/// The ASCII lowercase of a string.
pub open spec fn to_ascii_lowercase(s: Seq<u32>) -> Seq<u32> {
    Seq::new(s.len(), |i: int| ascii_lowercase(s[i]))
}

/// Infra "ASCII case-insensitive": equal after ASCII lowercasing.
pub open spec fn eq_ignoring_ascii_case(a: Seq<u32>, b: Seq<u32>) -> bool {
    to_ascii_lowercase(a) == to_ascii_lowercase(b)
}

/// §3.7 "White space in Selectors consists of the code points SPACE (U+0020), TAB (U+0009),
/// LINE FEED (U+000A), CARRIAGE RETURN (U+000D), and FORM FEED (U+000C)." These are also
/// HTML's ASCII whitespace and, here, the document white space characters (modelling
/// choices).
pub open spec fn is_selector_whitespace(c: u32) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x0C
}

// ------------------------------------------------------------------------------------
// §6 Attribute selectors
// ------------------------------------------------------------------------------------

/// True if `s` from `i` on has no white space.
pub open spec fn no_whitespace_from(s: Seq<u32>, i: int) -> bool
    decreases s.len() - i,
{
    i < 0 || i >= s.len() || (!is_selector_whitespace(s[i]) && no_whitespace_from(s, i + 1))
}

/// True if `v` has `s` at `i`.
pub open spec fn occurs_at(v: Seq<u32>, s: Seq<u32>, i: int) -> bool {
    0 <= i && i + s.len() <= v.len() && v.subrange(i, i + s.len() as int) == s
}

/// True if `s` occurs in `v` at some position from `i` down to 0.
pub open spec fn occurs_up_to(v: Seq<u32>, s: Seq<u32>, i: int) -> bool
    decreases i + 1,
{
    if i < 0 {
        false
    } else {
        occurs_at(v, s, i) || occurs_up_to(v, s, i - 1)
    }
}

/// True if `s`, which has no white space, is one of the words of `v` from `i` down to 0:
/// it occurs there with white space or an end on each side.
pub open spec fn word_up_to(v: Seq<u32>, s: Seq<u32>, i: int) -> bool
    decreases i + 1,
{
    if i < 0 {
        false
    } else {
        (occurs_at(v, s, i) && (i == 0 || is_selector_whitespace(v[i - 1])) && (i + s.len()
            == v.len() || is_selector_whitespace(v[i + s.len()]))) || word_up_to(v, s, i - 1)
    }
}

/// "a whitespace-separated list of words, one of which is exactly" `s`.
pub open spec fn is_one_of_the_words(v: Seq<u32>, s: Seq<u32>) -> bool {
    s.len() > 0 && no_whitespace_from(s, 0) && word_up_to(v, s, v.len() - s.len())
}

/// §6.1 and §6.2: what each matcher tests of the value `v` against `s`.
pub open spec fn value_matches(matcher: AttrMatcher, v: Seq<u32>, s: Seq<u32>) -> bool {
    match matcher {
        // "whose value is exactly "val"".
        AttrMatcher::Equals => v == s,
        // "a whitespace-separated list of words, one of which is exactly "val". If "val"
        // contains whitespace, it will never represent anything … Also if "val" is the empty
        // string, it will never represent anything."
        AttrMatcher::Includes => is_one_of_the_words(v, s),
        // "its value either being exactly "val" or beginning with "val" immediately followed
        // by "-" (U+002D)".
        AttrMatcher::DashMatch => v == s || (occurs_at(v, s, 0) && s.len() < v.len() && v[s.len()
            as int] == 0x2D),
        // "whose value begins with the prefix "val". If "val" is the empty string then the
        // selector does not represent anything."
        AttrMatcher::Prefix => s.len() > 0 && occurs_at(v, s, 0),
        // "whose value ends with the suffix "val"", likewise.
        AttrMatcher::Suffix => s.len() > 0 && s.len() <= v.len() && occurs_at(
            v,
            s,
            v.len() - s.len(),
        ),
        // "whose value contains at least one instance of the substring "val"", likewise.
        AttrMatcher::Substring => s.len() > 0 && occurs_up_to(v, s, v.len() - s.len()),
    }
}

/// HTML §4.16.2: the attributes whose values "Attribute selectors on an HTML element in an
/// HTML document must treat … as ASCII case-insensitive".
pub open spec fn is_case_insensitive_attribute(name: Seq<u32>) -> bool {
    // "accept"
    name == seq![0x61u32, 0x63, 0x63, 0x65, 0x70, 0x74]
    // "accept-charset"
    || name == seq![0x61u32, 0x63, 0x63, 0x65, 0x70, 0x74, 0x2D, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74]
    // "align"
    || name == seq![0x61u32, 0x6C, 0x69, 0x67, 0x6E]
    // "alink"
    || name == seq![0x61u32, 0x6C, 0x69, 0x6E, 0x6B]
    // "axis"
    || name == seq![0x61u32, 0x78, 0x69, 0x73]
    // "bgcolor"
    || name == seq![0x62u32, 0x67, 0x63, 0x6F, 0x6C, 0x6F, 0x72]
    // "charset"
    || name == seq![0x63u32, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74]
    // "checked"
    || name == seq![0x63u32, 0x68, 0x65, 0x63, 0x6B, 0x65, 0x64]
    // "clear"
    || name == seq![0x63u32, 0x6C, 0x65, 0x61, 0x72]
    // "codetype"
    || name == seq![0x63u32, 0x6F, 0x64, 0x65, 0x74, 0x79, 0x70, 0x65]
    // "color"
    || name == seq![0x63u32, 0x6F, 0x6C, 0x6F, 0x72]
    // "compact"
    || name == seq![0x63u32, 0x6F, 0x6D, 0x70, 0x61, 0x63, 0x74]
    // "declare"
    || name == seq![0x64u32, 0x65, 0x63, 0x6C, 0x61, 0x72, 0x65]
    // "defer"
    || name == seq![0x64u32, 0x65, 0x66, 0x65, 0x72]
    // "dir"
    || name == seq![0x64u32, 0x69, 0x72]
    // "direction"
    || name == seq![0x64u32, 0x69, 0x72, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E]
    // "disabled"
    || name == seq![0x64u32, 0x69, 0x73, 0x61, 0x62, 0x6C, 0x65, 0x64]
    // "enctype"
    || name == seq![0x65u32, 0x6E, 0x63, 0x74, 0x79, 0x70, 0x65]
    // "face"
    || name == seq![0x66u32, 0x61, 0x63, 0x65]
    // "frame"
    || name == seq![0x66u32, 0x72, 0x61, 0x6D, 0x65]
    // "hreflang"
    || name == seq![0x68u32, 0x72, 0x65, 0x66, 0x6C, 0x61, 0x6E, 0x67]
    // "http-equiv"
    || name == seq![0x68u32, 0x74, 0x74, 0x70, 0x2D, 0x65, 0x71, 0x75, 0x69, 0x76]
    // "lang"
    || name == seq![0x6Cu32, 0x61, 0x6E, 0x67]
    // "language"
    || name == seq![0x6Cu32, 0x61, 0x6E, 0x67, 0x75, 0x61, 0x67, 0x65]
    // "link"
    || name == seq![0x6Cu32, 0x69, 0x6E, 0x6B]
    // "media"
    || name == seq![0x6Du32, 0x65, 0x64, 0x69, 0x61]
    // "method"
    || name == seq![0x6Du32, 0x65, 0x74, 0x68, 0x6F, 0x64]
    // "multiple"
    || name == seq![0x6Du32, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x6C, 0x65]
    // "nohref"
    || name == seq![0x6Eu32, 0x6F, 0x68, 0x72, 0x65, 0x66]
    // "noresize"
    || name == seq![0x6Eu32, 0x6F, 0x72, 0x65, 0x73, 0x69, 0x7A, 0x65]
    // "noshade"
    || name == seq![0x6Eu32, 0x6F, 0x73, 0x68, 0x61, 0x64, 0x65]
    // "nowrap"
    || name == seq![0x6Eu32, 0x6F, 0x77, 0x72, 0x61, 0x70]
    // "readonly"
    || name == seq![0x72u32, 0x65, 0x61, 0x64, 0x6F, 0x6E, 0x6C, 0x79]
    // "rel"
    || name == seq![0x72u32, 0x65, 0x6C]
    // "rev"
    || name == seq![0x72u32, 0x65, 0x76]
    // "rules"
    || name == seq![0x72u32, 0x75, 0x6C, 0x65, 0x73]
    // "scope"
    || name == seq![0x73u32, 0x63, 0x6F, 0x70, 0x65]
    // "scrolling"
    || name == seq![0x73u32, 0x63, 0x72, 0x6F, 0x6C, 0x6C, 0x69, 0x6E, 0x67]
    // "selected"
    || name == seq![0x73u32, 0x65, 0x6C, 0x65, 0x63, 0x74, 0x65, 0x64]
    // "shape"
    || name == seq![0x73u32, 0x68, 0x61, 0x70, 0x65]
    // "target"
    || name == seq![0x74u32, 0x61, 0x72, 0x67, 0x65, 0x74]
    // "text"
    || name == seq![0x74u32, 0x65, 0x78, 0x74]
    // "type"
    || name == seq![0x74u32, 0x79, 0x70, 0x65]
    // "valign"
    || name == seq![0x76u32, 0x61, 0x6C, 0x69, 0x67, 0x6E]
    // "valuetype"
    || name == seq![0x76u32, 0x61, 0x6C, 0x75, 0x65, 0x74, 0x79, 0x70, 0x65]
    // "vlink"
    || name == seq![0x76u32, 0x6C, 0x69, 0x6E, 0x6B]
}

/// HTML §4.16.2: true if the selector's attribute name `name`, with namespace component
/// `ns`, names the attribute `attr` of the element `x`. "When comparing the name part of a
/// CSS attribute selector to the names of attributes on HTML elements in HTML documents, the
/// name part of the CSS attribute selector must first be converted to ASCII lowercase. The
/// same selector when compared to other attributes must be compared according to its
/// original case." Among those other attributes are "the names of attributes that
/// themselves have namespaces".
pub open spec fn names_attribute(doc: Document, x: NodeId, ns: NsPrefix, name: Seq<u32>, attr: Attr) -> bool {
    // §6.4: "attribute selectors without a namespace component apply only to attributes that
    // have no namespace (equivalent to '|attr')"; "*|" matches "without regard to the
    // attribute's namespace".
    let ns_ok = match ns {
        NsPrefix::Any => true,
        _ => attr.namespace is None,
    };
    let name_ok = if is_html_element(doc, x) && attr.namespace is None {
        to_ascii_lowercase(name) == attr.local_name
    } else {
        name == attr.local_name
    };
    ns_ok && name_ok
}

/// True if the attribute `attr` of `x` passes `test` (§6.1 to §6.3).
pub open spec fn attribute_passes(doc: Document, x: NodeId, attr: Attr, test: Option<AttrTest>) -> bool {
    match test {
        // "[att]": "whatever the value of the attribute".
        None => true,
        Some(test) => {
            let insensitive = match test.flag {
                // §6.3: "When this flag is present, UAs must match the attribute's value
                // ASCII case-insensitively."
                Some(CaseFlag::I) => true,
                // "in this case the UA must match the value case-sensitively … regardless of
                // document language rules".
                Some(CaseFlag::S) => false,
                // HTML §4.16.2's list, for "an HTML element in an HTML document", and only
                // for attributes without a namespace, whose names are those names.
                None => is_html_element(doc, x) && attr.namespace is None
                    && is_case_insensitive_attribute(attr.local_name),
            };
            if insensitive {
                value_matches(
                    test.matcher,
                    to_ascii_lowercase(attr.value),
                    to_ascii_lowercase(test.value),
                )
            } else {
                value_matches(test.matcher, attr.value, test.value)
            }
        },
    }
}

/// True if one of the first `k` attributes of `x` is named by (`ns`, `name`) and passes
/// `test`.
pub open spec fn some_attribute(
    doc: Document,
    x: NodeId,
    ns: NsPrefix,
    name: Seq<u32>,
    test: Option<AttrTest>,
    k: int,
) -> bool
    decreases k,
{
    if k <= 0 || k > attributes_of(doc, x).len() {
        false
    } else {
        let attr = attributes_of(doc, x)[k - 1];
        (names_attribute(doc, x, ns, name, attr) && attribute_passes(doc, x, attr, test))
            || some_attribute(doc, x, ns, name, test, k - 1)
    }
}

/// The value of the attribute of `x` with no namespace and the local name `name`, among its
/// first `k` attributes: DOM "get an attribute by namespace and local name", which returns
/// the first.
pub open spec fn plain_attribute_value(doc: Document, x: NodeId, name: Seq<u32>, k: int) -> Option<
    Seq<u32>,
>
    decreases k,
{
    if k <= 0 || k > attributes_of(doc, x).len() {
        None
    } else {
        match plain_attribute_value(doc, x, name, k - 1) {
            Some(value) => Some(value),
            None => {
                let attr = attributes_of(doc, x)[k - 1];
                if attr.namespace is None && attr.local_name == name {
                    Some(attr.value)
                } else {
                    None
                }
            },
        }
    }
}

/// The value of `x`'s attribute `name`, with no namespace.
pub open spec fn get_attribute(doc: Document, x: NodeId, name: Seq<u32>) -> Option<Seq<u32>> {
    plain_attribute_value(doc, x, name, attributes_of(doc, x).len() as int)
}

/// "id"
pub open spec fn str_id() -> Seq<u32> {
    seq![0x69u32, 0x64]
}

/// "class"
pub open spec fn str_class() -> Seq<u32> {
    seq![0x63u32, 0x6C, 0x61, 0x73, 0x73]
}

/// "href"
pub open spec fn str_href() -> Seq<u32> {
    seq![0x68u32, 0x72, 0x65, 0x66]
}

/// §6.6 class selector: "equivalent to the ~= notation applied to the local class attribute
/// (i.e. [class~=identifier])". "When matching against a document which is in quirks mode,
/// class names must be matched ASCII case-insensitively; class selectors are otherwise
/// case-sensitive."
pub open spec fn has_class(doc: Document, x: NodeId, name: Seq<u32>) -> bool {
    match get_attribute(doc, x, str_class()) {
        None => false,
        Some(value) => if in_quirks_mode(doc) {
            is_one_of_the_words(to_ascii_lowercase(value), to_ascii_lowercase(name))
        } else {
            is_one_of_the_words(value, name)
        },
    }
}

/// §7 ID selector: "represents an element instance that has an identifier that matches the
/// identifier in the ID selector". "In HTML all ID attributes are named id." In quirks mode
/// the match is ASCII case-insensitive (§7, HTML §4.16.2).
pub open spec fn has_id(doc: Document, x: NodeId, name: Seq<u32>) -> bool {
    match get_attribute(doc, x, str_id()) {
        None => false,
        Some(value) => if in_quirks_mode(doc) {
            eq_ignoring_ascii_case(value, name)
        } else {
            value == name
        },
    }
}

// ------------------------------------------------------------------------------------
// §15 Tree-structural pseudo-classes
// ------------------------------------------------------------------------------------

/// "Inclusive siblings" of `x`: its parent's children, or `x` alone if it has none
/// (modelling choices).
pub open spec fn inclusive_siblings(doc: Document, x: NodeId) -> Seq<NodeId> {
    match parent_of(doc, x) {
        Some(p) => children_of(doc, p),
        None => seq![x],
    }
}

/// `x`'s position among its inclusive siblings.
pub open spec fn sibling_index(doc: Document, x: NodeId) -> int {
    clazel_dom::spec::index_of(inclusive_siblings(doc, x), x)
}

/// §15.4: "the same type": the same namespace and local name ("a type selector and
/// namespace prefix matching the element in question").
pub open spec fn same_type(doc: Document, x: NodeId, y: NodeId) -> bool {
    namespace_of(doc, x) == namespace_of(doc, y) && local_name_of(doc, x) == local_name_of(doc, y)
}

/// True if `y` counts among `x`'s siblings: an element ("non-element nodes are not
/// counted"), and of `x`'s type if `of_type`.
pub open spec fn counts(doc: Document, x: NodeId, y: NodeId, of_type: bool) -> bool {
    is_element(doc, y) && (!of_type || same_type(doc, x, y))
}

/// How many of `sibs` before index `j` count.
pub open spec fn count_before(doc: Document, x: NodeId, sibs: Seq<NodeId>, j: int, of_type: bool) -> nat
    decreases j,
{
    if j <= 0 || j > sibs.len() {
        0
    } else {
        count_before(doc, x, sibs, j - 1, of_type) + if counts(doc, x, sibs[j - 1], of_type) {
            1nat
        } else {
            0nat
        }
    }
}

/// How many of `sibs` from index `j` on count.
pub open spec fn count_from(doc: Document, x: NodeId, sibs: Seq<NodeId>, j: int, of_type: bool) -> nat
    decreases sibs.len() - j,
{
    if j < 0 || j >= sibs.len() {
        0
    } else {
        count_from(doc, x, sibs, j + 1, of_type) + if counts(doc, x, sibs[j], of_type) {
            1nat
        } else {
            0nat
        }
    }
}

/// The 1-based index of `x` among the inclusive siblings that count, from the start, or
/// from the end if `from_end`.
pub open spec fn child_index(doc: Document, x: NodeId, of_type: bool, from_end: bool) -> int {
    let sibs = inclusive_siblings(doc, x);
    let j = sibling_index(doc, x);
    if from_end {
        count_from(doc, x, sibs, j + 1, of_type) as int + 1
    } else {
        count_before(doc, x, sibs, j, of_type) as int + 1
    }
}

/// §15.3.1 "represents any index i = An + B for any non-negative integer n", evaluated
/// (modelling choices).
pub open spec fn nth_index_matches(a: int, b: int, i: int) -> bool {
    if a == 0 {
        i == b
    } else if a > 0 {
        i >= b && (i - b) % a == 0
    } else {
        i <= b && (b - i) % (-a) == 0
    }
}

/// §15.2 `:empty`: "an element that has no children except, optionally, document white
/// space characters. In terms of the document tree, only element nodes and content nodes
/// (such as DOM text nodes, and entity references) whose data has a non-zero length must be
/// considered as affecting emptiness; comments, processing instructions, and other nodes must
/// not affect whether an element is considered empty or not." Checks the first `k` children.
pub open spec fn empty_up_to(doc: Document, kids: Seq<NodeId>, k: int) -> bool
    decreases k,
{
    if k <= 0 || k > kids.len() {
        true
    } else {
        let child = kids[k - 1];
        let affects = if child >= doc.nodes.len() {
            false
        } else {
            match doc.nodes[child as int].kind {
                NodeKind::Element { .. } => true,
                NodeKind::Text { data } => !all_whitespace(data, 0),
                _ => false,
            }
        };
        !affects && empty_up_to(doc, kids, k - 1)
    }
}

/// True if `data` from `i` on is all document white space characters.
pub open spec fn all_whitespace(data: Seq<u32>, i: int) -> bool
    decreases data.len() - i,
{
    i < 0 || i >= data.len() || (is_selector_whitespace(data[i]) && all_whitespace(data, i + 1))
}

/// HTML §4.16.3: "All a elements that have an href attribute, and all area elements that
/// have an href attribute, must match one of :link and :visited."
pub open spec fn is_hyperlink(doc: Document, x: NodeId) -> bool {
    is_html_element(doc, x) && (local_name_of(doc, x) == seq![0x61u32] || local_name_of(doc, x)
        == seq![0x61u32, 0x72, 0x65, 0x61]) && get_attribute(doc, x, str_href()) is Some
}

/// §9.2 `:visited`: never, as no history reaches a renderer (modelling choices).
pub open spec fn is_visited(doc: Document, x: NodeId) -> bool {
    false
}

/// True if the pseudo-class `class` matches the element `x`.
pub open spec fn pseudo_class_matches(doc: Document, class: PseudoClass, x: NodeId) -> bool {
    match class {
        // A hyperlink that is not visited matches :link.
        PseudoClass::Link => is_hyperlink(doc, x) && !is_visited(doc, x),
        PseudoClass::Visited => is_hyperlink(doc, x) && is_visited(doc, x),
        // §9.1: "It matches an element if the element would match either :link or :visited".
        PseudoClass::AnyLink => (is_hyperlink(doc, x) && !is_visited(doc, x)) || (is_hyperlink(
            doc,
            x,
        ) && is_visited(doc, x)),
        // §15.1: "the root of the document … in a DOM document, the :root pseudo-class
        // matches the document element", the element child of the document.
        PseudoClass::Root => match parent_of(doc, x) {
            Some(p) => p < doc.nodes.len() && doc.nodes[p as int].kind is Document,
            None => false,
        },
        PseudoClass::Empty => empty_up_to(doc, children_of(doc, x), children_of(doc, x).len() as int),
        // §15.3.3: "Same as :nth-child(1)".
        PseudoClass::FirstChild => child_index(doc, x, false, false) == 1,
        // §15.3.4: "Same as :nth-last-child(1)".
        PseudoClass::LastChild => child_index(doc, x, false, true) == 1,
        // §15.3.5: "Same as :first-child:last-child".
        PseudoClass::OnlyChild => child_index(doc, x, false, false) == 1 && child_index(
            doc,
            x,
            false,
            true,
        ) == 1,
        // §15.4.3 to §15.4.5, likewise with :nth-of-type(1) and :nth-last-of-type(1).
        PseudoClass::FirstOfType => child_index(doc, x, true, false) == 1,
        PseudoClass::LastOfType => child_index(doc, x, true, true) == 1,
        PseudoClass::OnlyOfType => child_index(doc, x, true, false) == 1 && child_index(
            doc,
            x,
            true,
            true,
        ) == 1,
        // The user action pseudo-classes never match (modelling choices).
        PseudoClass::Hover => false,
        PseudoClass::Active => false,
        PseudoClass::Focus => false,
        PseudoClass::FocusVisible => false,
        PseudoClass::FocusWithin => false,
    }
}

/// True if the namespace component `ns` of a type or universal selector allows `x`. §5.3:
/// "*|E": "in any namespace, including those without a namespace"; "|E": "without a
/// namespace"; "E": "if no default namespace has been declared for selectors, this is
/// equivalent to *|E".
pub open spec fn namespace_allows(doc: Document, ns: NsPrefix, x: NodeId) -> bool {
    match ns {
        NsPrefix::Absent => true,
        NsPrefix::Any => true,
        NsPrefix::NoNamespace => namespace_of(doc, x) is None,
    }
}

/// HTML §4.16.2: "When comparing a CSS element type selector to the names of HTML elements
/// in HTML documents, the CSS element type selector must first be converted to ASCII
/// lowercase. The same selector when compared to other elements must be compared according
/// to its original case. In both cases, to match, the values must be identical."
pub open spec fn type_name_matches(doc: Document, name: Seq<u32>, x: NodeId) -> bool {
    if is_html_element(doc, x) {
        to_ascii_lowercase(name) == local_name_of(doc, x)
    } else {
        name == local_name_of(doc, x)
    }
}

// ------------------------------------------------------------------------------------
// §21.3 Match a selector against an element
// ------------------------------------------------------------------------------------

/// True if the simple selector `s` matches the element `x`.
pub open spec fn simple_matches(doc: Document, s: Simple, x: NodeId) -> bool
    decreases s, 0int, 0int,
{
    is_element(doc, x) && match s {
        // §5.1 "represents an element … with the given name", in the namespace allowed.
        Simple::Type { ns, name } => namespace_allows(doc, ns, x) && type_name_matches(doc, name, x),
        // §5.2 "represents an element of any element type", likewise.
        Simple::Universal { ns } => namespace_allows(doc, ns, x),
        Simple::Id { name } => has_id(doc, x, name),
        Simple::Class { name } => has_class(doc, x, name),
        Simple::Attribute { ns, name, test } => some_attribute(
            doc,
            x,
            ns,
            name,
            test,
            attributes_of(doc, x).len() as int,
        ),
        Simple::PseudoClass { class } => pseudo_class_matches(doc, class, x),
        // §15.3.1 "elements that are among An+Bth elements from the list composed of their
        // inclusive siblings", §15.3.2 "counting backwards from the end", §15.4 "among
        // elements of the same type".
        Simple::Nth { kind, a, b } => nth_index_matches(
            a,
            b,
            match kind {
                NthKind::Child => child_index(doc, x, false, false),
                NthKind::LastChild => child_index(doc, x, false, true),
                NthKind::OfType => child_index(doc, x, true, false),
                NthKind::LastOfType => child_index(doc, x, true, true),
            },
        ),
        // §4.2: "If the argument, after parsing, is an empty list, the pseudo-class is valid
        // but matches nothing. Otherwise, the pseudo-class matches any element that matches
        // any of the selectors in the list."
        Simple::Is { arg } => match_list(doc, arg, arg.len() as int, x),
        // §4.4: "the same syntax and functionality as :is()".
        Simple::Where { arg } => match_list(doc, arg, arg.len() as int, x),
        // §4.3: "It represents an element that is not represented by its argument."
        Simple::Not { arg } => !match_list(doc, arg, arg.len() as int, x),
        // A pseudo-element is not an element (modelling choices).
        Simple::PseudoElement { .. } => false,
    }
}

/// True if each of the first `k` simple selectors of `compound` matches `x`.
pub open spec fn compound_matches(doc: Document, compound: Seq<Simple>, k: int, x: NodeId) -> bool
    decreases compound, k, 0int,
{
    if k <= 0 || k > compound.len() {
        true
    } else {
        compound_matches(doc, compound, k - 1, x) && simple_matches(doc, compound[k - 1], x)
    }
}

/// True if the complex selector made of the first `n` compound selectors of `c` (and the
/// combinators between them) matches the element `x`: §21.3 "match a complex selector
/// against an element".
pub open spec fn match_complex(doc: Document, c: Complex, n: int, x: NodeId) -> bool
    decreases c, n, 0int,
{
    if n <= 0 || n > c.compounds.len() || n - 2 >= c.combinators.len() {
        false
    } else {
        let compound = c.compounds[n - 1];
        // "If any simple selectors in the rightmost compound selector does not match the
        // element, return failure."
        if !compound_matches(doc, compound, compound.len() as int, x) {
            false
        // "Otherwise, if there is only one compound selector in the complex selector, return
        // success."
        } else if n == 1 {
            true
        } else {
            // "Otherwise, consider all possible elements that could be related to this
            // element by the rightmost combinator. If the operation of matching the selector
            // consisting of this selector with the rightmost compound selector and rightmost
            // combinator removed against any one of these elements returns success, then
            // return success. Otherwise, return failure."
            match c.combinators[n - 2] {
                // §16.1 "an arbitrary descendant of some ancestor element A".
                Combinator::Descendant => some_ancestor_matches(
                    doc,
                    c,
                    n - 1,
                    parent_of(doc, x),
                    doc.nodes.len(),
                ),
                // §16.2 "a childhood relationship between two elements".
                Combinator::Child => match parent_of(doc, x) {
                    Some(p) => is_element(doc, p) && match_complex(doc, c, n - 1, p),
                    None => false,
                },
                // §16.3 "the second element immediately follows the first … ignoring
                // non-element nodes".
                Combinator::NextSibling => previous_element_matches(
                    doc,
                    c,
                    n - 1,
                    inclusive_siblings(doc, x),
                    sibling_index(doc, x) - 1,
                ),
                // §16.4 "share the same parent … the first … precedes (not necessarily
                // immediately) the … second one".
                Combinator::SubsequentSibling => some_earlier_sibling_matches(
                    doc,
                    c,
                    n - 1,
                    inclusive_siblings(doc, x),
                    sibling_index(doc, x) - 1,
                ),
            }
        }
    }
}

/// True if `x` or one of its ancestors, within `fuel` steps, is an element that the first
/// `n` compound selectors of `c` match.
pub open spec fn some_ancestor_matches(
    doc: Document,
    c: Complex,
    n: int,
    x: Option<NodeId>,
    fuel: nat,
) -> bool
    decreases c, n, fuel + 1,
{
    match x {
        None => false,
        Some(a) => if fuel == 0 {
            false
        } else {
            (is_element(doc, a) && match_complex(doc, c, n, a)) || some_ancestor_matches(
                doc,
                c,
                n,
                parent_of(doc, a),
                (fuel - 1) as nat,
            )
        },
    }
}

/// True if the element nearest before index `j + 1` of `sibs`, looking at indexes `j`, `j -
/// 1`, …, is one that the first `n` compound selectors of `c` match.
pub open spec fn previous_element_matches(
    doc: Document,
    c: Complex,
    n: int,
    sibs: Seq<NodeId>,
    j: int,
) -> bool
    decreases c, n, j + 2,
{
    if j < 0 || j >= sibs.len() {
        false
    } else if is_element(doc, sibs[j]) {
        match_complex(doc, c, n, sibs[j])
    } else {
        previous_element_matches(doc, c, n, sibs, j - 1)
    }
}

/// True if one of the elements at indexes `j`, `j - 1`, …, 0 of `sibs` is one that the
/// first `n` compound selectors of `c` match.
pub open spec fn some_earlier_sibling_matches(
    doc: Document,
    c: Complex,
    n: int,
    sibs: Seq<NodeId>,
    j: int,
) -> bool
    decreases c, n, j + 2,
{
    if j < 0 || j >= sibs.len() {
        false
    } else {
        (is_element(doc, sibs[j]) && match_complex(doc, c, n, sibs[j]))
            || some_earlier_sibling_matches(doc, c, n, sibs, j - 1)
    }
}

/// True if one of the first `k` complex selectors of `list` matches `x`.
pub open spec fn match_list(doc: Document, list: Seq<Complex>, k: int, x: NodeId) -> bool
    decreases list, k, 0int,
{
    if k <= 0 || k > list.len() {
        false
    } else {
        match_list(doc, list, k - 1, x) || match_complex(
            doc,
            list[k - 1],
            list[k - 1].compounds.len() as int,
            x,
        )
    }
}

/// §21.3 "match a selector against an element": "For each complex selector in the given
/// selector (which is taken to be a list of complex selectors), match the complex selector
/// against element … If the matching returns success for any complex selector, then the
/// algorithm return success; otherwise it returns failure."
pub open spec fn match_a_selector_against_an_element(doc: Document, selector: Seq<Complex>, x: NodeId) -> bool {
    match_list(doc, selector, selector.len() as int, x)
}

// ------------------------------------------------------------------------------------
// §17 Calculating a selector's specificity
// ------------------------------------------------------------------------------------

/// A specificity: "(A, B, C)".
pub ghost struct Specificity {
    /// "the number of ID selectors".
    pub a: nat,
    /// "the number of class selectors, attributes selectors, and pseudo-classes".
    pub b: nat,
    /// "the number of type selectors and pseudo-elements".
    pub c: nat,
}

/// (0, 0, 0).
pub open spec fn zero() -> Specificity {
    Specificity { a: 0, b: 0, c: 0 }
}

/// The limit of each component (modelling choices).
pub open spec fn specificity_limit() -> nat {
    0xFFFF_FFFF
}

/// `n`, "clamped to that limit".
pub open spec fn saturate(n: nat) -> nat {
    if n > specificity_limit() {
        specificity_limit()
    } else {
        n
    }
}

/// Counts added component-wise, each clamped.
pub open spec fn add(x: Specificity, y: Specificity) -> Specificity {
    Specificity { a: saturate(x.a + y.a), b: saturate(x.b + y.b), c: saturate(x.c + y.c) }
}

/// §17: "Specificities are compared by comparing the three components in order: the
/// specificity with a larger A value is more specific; if the two A values are tied, then the
/// specificity with a larger B value is more specific; if the two B values are also tied,
/// then the specificity with a larger C value is more specific; if all the values are tied,
/// the two specificities are equal." True if `x` is at most as specific as `y`.
pub open spec fn not_more_specific(x: Specificity, y: Specificity) -> bool {
    x.a < y.a || (x.a == y.a && (x.b < y.b || (x.b == y.b && x.c <= y.c)))
}

/// The more specific of two.
pub open spec fn most_specific(x: Specificity, y: Specificity) -> Specificity {
    if not_more_specific(x, y) {
        y
    } else {
        x
    }
}

/// The specificity of the simple selector `s`.
pub open spec fn simple_specificity(s: Simple) -> Specificity
    decreases s, 0int, 0int,
{
    match s {
        // "count the number of ID selectors in the selector (= A)".
        Simple::Id { .. } => Specificity { a: 1, b: 0, c: 0 },
        // "count the number of class selectors, attributes selectors, and pseudo-classes in
        // the selector (= B)".
        Simple::Class { .. } => Specificity { a: 0, b: 1, c: 0 },
        Simple::Attribute { .. } => Specificity { a: 0, b: 1, c: 0 },
        Simple::PseudoClass { .. } => Specificity { a: 0, b: 1, c: 0 },
        // ":nth-child() … is the specificity of the pseudo-class itself (counting as one
        // pseudo-class selector) plus the specificity of the most specific complex selector
        // in its selector list argument (if any)": the subset has no argument.
        Simple::Nth { .. } => Specificity { a: 0, b: 1, c: 0 },
        // "count the number of type selectors and pseudo-elements in the selector (= C)".
        Simple::Type { .. } => Specificity { a: 0, b: 0, c: 1 },
        Simple::PseudoElement { .. } => Specificity { a: 0, b: 0, c: 1 },
        // "ignore the universal selector".
        Simple::Universal { .. } => zero(),
        // "The specificity of an :is(), :not(), or :has() pseudo-class is replaced by the
        // specificity of the most specific complex selector in its selector list argument."
        Simple::Is { arg } => list_specificity(arg, arg.len() as int),
        Simple::Not { arg } => list_specificity(arg, arg.len() as int),
        // "The specificity of a :where() pseudo-class is replaced by zero."
        Simple::Where { .. } => zero(),
    }
}

/// The specificity of the first `k` simple selectors of a compound selector: the counts of
/// each, added.
pub open spec fn compound_specificity(compound: Seq<Simple>, k: int) -> Specificity
    decreases compound, k, 0int,
{
    if k <= 0 || k > compound.len() {
        zero()
    } else {
        add(compound_specificity(compound, k - 1), simple_specificity(compound[k - 1]))
    }
}

/// The specificity of the first `n` compound selectors of a complex selector.
pub open spec fn complex_specificity(c: Complex, n: int) -> Specificity
    decreases c, n, 0int,
{
    if n <= 0 || n > c.compounds.len() {
        zero()
    } else {
        add(
            complex_specificity(c, n - 1),
            compound_specificity(c.compounds[n - 1], c.compounds[n - 1].len() as int),
        )
    }
}

/// The specificity of a complex selector.
pub open spec fn specificity(c: Complex) -> Specificity {
    complex_specificity(c, c.compounds.len() as int)
}

/// The most specific of the first `k` complex selectors of `list`, or zero if `k` is 0.
pub open spec fn list_specificity(list: Seq<Complex>, k: int) -> Specificity
    decreases list, k, 0int,
{
    if k <= 0 || k > list.len() {
        zero()
    } else {
        most_specific(
            list_specificity(list, k - 1),
            complex_specificity(list[k - 1], list[k - 1].compounds.len() as int),
        )
    }
}

/// §17: "If the selector is a selector list, this number is calculated for each selector in
/// the list. For a given matching process against the list, the specificity in effect is that
/// of the most specific selector in the list that matches." Over the first `k`.
pub open spec fn specificity_in_effect(doc: Document, list: Seq<Complex>, k: int, x: NodeId) -> Specificity
    decreases k,
{
    if k <= 0 || k > list.len() {
        zero()
    } else if match_complex(doc, list[k - 1], list[k - 1].compounds.len() as int, x) {
        most_specific(specificity_in_effect(doc, list, k - 1, x), specificity(list[k - 1]))
    } else {
        specificity_in_effect(doc, list, k - 1, x)
    }
}

// ------------------------------------------------------------------------------------
// CSSOM §2.1 Common Serializing Idioms
// ------------------------------------------------------------------------------------

/// The lowercase hexadecimal digit of `d`, below 16.
pub open spec fn hex_digit(d: nat) -> u32 {
    if d < 10 {
        (0x30 + d) as u32
    } else {
        (0x61 + d - 10) as u32
    }
}

/// The hexadecimal digits of `n`, before `digits`.
pub open spec fn hex_digits(n: nat, digits: Seq<u32>) -> Seq<u32>
    decreases n,
{
    if n < 16 {
        seq![hex_digit(n)] + digits
    } else {
        hex_digits(n / 16, seq![hex_digit(n % 16)] + digits)
    }
}

/// "escape a character as code point": "\" (U+005C), "followed by the Unicode code point as
/// the smallest possible number of hexadecimal digits in the range 0-9 a-f … followed by a
/// single SPACE (U+0020)".
pub open spec fn escape_as_code_point(c: u32) -> Seq<u32> {
    seq![0x5Cu32] + hex_digits(c as nat, Seq::empty()) + seq![0x20u32]
}

/// "escape a character": "\" (U+005C), "followed by the character".
pub open spec fn escape(c: u32) -> Seq<u32> {
    seq![0x5Cu32, c]
}

/// "non-ASCII ident code point" (CSS Syntax §4.2).
pub open spec fn is_non_ascii_ident(c: u32) -> bool {
    clazel_css::tokenizer::spec::is_non_ascii_ident_code_point(c)
}

/// "serialize an identifier": the serialization of the character at `i` of `s`.
pub open spec fn identifier_char(s: Seq<u32>, i: int) -> Seq<u32> {
    let c = s[i];
    // "If the character is NULL (U+0000), then the REPLACEMENT CHARACTER (U+FFFD)."
    if c == 0 {
        seq![0xFFFDu32]
    // "If the character is in the range [\1-\1f] (U+0001 to U+001F) or is U+007F, then the
    // character escaped as code point."
    } else if (0x01 <= c <= 0x1F) || c == 0x7F {
        escape_as_code_point(c)
    // "If the character is the first character and is in the range [0-9] (U+0030 to U+0039),
    // then the character escaped as code point."
    } else if i == 0 && 0x30 <= c <= 0x39 {
        escape_as_code_point(c)
    // "If the character is the second character and is in the range [0-9] (U+0030 to U+0039)
    // and the first character is a "-" (U+002D), then the character escaped as code point."
    } else if i == 1 && 0x30 <= c <= 0x39 && s[0] == 0x2D {
        escape_as_code_point(c)
    // "If the character is the first character and is a "-" (U+002D), and there is no
    // second character, then the escaped character."
    } else if i == 0 && c == 0x2D && s.len() == 1 {
        escape(c)
    // "If the character is not handled by one of the above rules and is a non-ASCII ident
    // code point, is "-" (U+002D) or "_" (U+005F), or is in one of the ranges [0-9] (U+0030 to
    // U+0039), [A-Z] (U+0041 to U+005A), or [a-z] (U+0061 to U+007A), then the character
    // itself."
    } else if is_non_ascii_ident(c) || c == 0x2D || c == 0x5F || (0x30 <= c <= 0x39) || (0x41
        <= c <= 0x5A) || (0x61 <= c <= 0x7A) {
        seq![c]
    // "Otherwise, the escaped character."
    } else {
        escape(c)
    }
}

/// "serialize an identifier", of the first `k` characters of `s`.
pub open spec fn identifier_prefix(s: Seq<u32>, k: int) -> Seq<u32>
    decreases k,
{
    if k <= 0 || k > s.len() {
        Seq::empty()
    } else {
        identifier_prefix(s, k - 1) + identifier_char(s, k - 1)
    }
}

/// CSSOM §2.1 "serialize an identifier".
pub open spec fn serialize_an_identifier(s: Seq<u32>) -> Seq<u32> {
    identifier_prefix(s, s.len() as int)
}

/// "serialize a string": the serialization of the character `c`.
pub open spec fn string_char(c: u32) -> Seq<u32> {
    // "If the character is NULL (U+0000), then the REPLACEMENT CHARACTER (U+FFFD)."
    if c == 0 {
        seq![0xFFFDu32]
    // "If the character is in the range [\1-\1f] (U+0001 to U+001F) or is U+007F, the
    // character escaped as code point."
    } else if (0x01 <= c <= 0x1F) || c == 0x7F {
        escape_as_code_point(c)
    // "If the character is '"' (U+0022) or "\" (U+005C), the escaped character."
    } else if c == 0x22 || c == 0x5C {
        escape(c)
    // "Otherwise, the character itself."
    } else {
        seq![c]
    }
}

/// "serialize a string", of the first `k` characters of `s`, without the quotes.
pub open spec fn string_prefix(s: Seq<u32>, k: int) -> Seq<u32>
    decreases k,
{
    if k <= 0 || k > s.len() {
        Seq::empty()
    } else {
        string_prefix(s, k - 1) + string_char(s[k - 1])
    }
}

/// CSSOM §2.1 "serialize a string": '"', the characters, '"'.
pub open spec fn serialize_a_string(s: Seq<u32>) -> Seq<u32> {
    seq![0x22u32] + string_prefix(s, s.len() as int) + seq![0x22u32]
}

// ------------------------------------------------------------------------------------
// CSSOM §6.7.2 Serializing Selectors
// ------------------------------------------------------------------------------------

/// The matcher's text.
pub open spec fn matcher_text(matcher: AttrMatcher) -> Seq<u32> {
    match matcher {
        AttrMatcher::Equals => seq![0x3Du32],
        AttrMatcher::Includes => seq![0x7Eu32, 0x3D],
        AttrMatcher::DashMatch => seq![0x7Cu32, 0x3D],
        AttrMatcher::Prefix => seq![0x5Eu32, 0x3D],
        AttrMatcher::Suffix => seq![0x24u32, 0x3D],
        AttrMatcher::Substring => seq![0x2Au32, 0x3D],
    }
}

/// The namespace component of a type or universal selector: "If the namespace prefix maps
/// to a namespace that is the null namespace (not in a namespace) append "|"". `*|` is left
/// out (modelling choices).
pub open spec fn element_prefix(ns: NsPrefix) -> Seq<u32> {
    match ns {
        NsPrefix::NoNamespace => seq![0x7Cu32],
        _ => Seq::empty(),
    }
}

/// CSSOM "serialize a simple selector".
pub open spec fn serialize_a_simple_selector(s: Simple) -> Seq<u32>
    decreases s, 0int, 0int,
{
    match s {
        // "type selector": 2. the prefix, 3. "the serialization of the element name as an
        // identifier".
        Simple::Type { ns, name } => element_prefix(ns) + serialize_an_identifier(name),
        // "universal selector": 2. the prefix, 4. "append "*" (U+002A)".
        Simple::Universal { ns } => element_prefix(ns) + seq![0x2Au32],
        // "attribute selector": 1. "[", 2. a namespace that is not the null namespace (here
        // only "*|"), 3. the name, 4. the matcher and "the serialization of the attribute
        // value as a string", 5. the flag, 6. "]".
        Simple::Attribute { ns, name, test } => {
            let prefix = match ns {
                NsPrefix::Any => seq![0x2Au32, 0x7C],
                _ => Seq::empty(),
            };
            let value = match test {
                None => Seq::empty(),
                Some(test) => matcher_text(test.matcher) + serialize_a_string(test.value)
                    + match test.flag {
                    None => Seq::empty(),
                    Some(CaseFlag::I) => seq![0x20u32, 0x69],
                    Some(CaseFlag::S) => seq![0x20u32, 0x73],
                },
            };
            seq![0x5Bu32] + prefix + serialize_an_identifier(name) + value + seq![0x5Du32]
        },
        // "class selector": "." and "the serialization of the class name as an identifier".
        Simple::Class { name } => seq![0x2Eu32] + serialize_an_identifier(name),
        // "ID selector": "#" and "the serialization of the ID as an identifier".
        Simple::Id { name } => seq![0x23u32] + serialize_an_identifier(name),
        // "pseudo-class": "If the pseudo-class does not accept arguments append ":"
        // (U+003A), followed by the name of the pseudo-class".
        Simple::PseudoClass { class } => seq![0x3Au32] + pseudo_class_name(class),
        // ":nth-child() … The result of serializing the value using the rules to serialize an
        // <a-n-plus-b> value."
        Simple::Nth { kind, a, b } => seq![0x3Au32] + nth_name(kind) + seq![0x28u32]
            + serialize_a_n_plus_b(a, b) + seq![0x29u32],
        // ":not() … The result of serializing the value using the rules for serializing a
        // group of selectors"; :is() and :where() alike (modelling choices).
        Simple::Is { arg } => seq![0x3Au32] + str_is() + seq![0x28u32] + serialize_list(
            arg,
            arg.len() as int,
        ) + seq![0x29u32],
        Simple::Where { arg } => seq![0x3Au32] + str_where() + seq![0x28u32] + serialize_list(
            arg,
            arg.len() as int,
        ) + seq![0x29u32],
        Simple::Not { arg } => seq![0x3Au32] + str_not() + seq![0x28u32] + serialize_list(
            arg,
            arg.len() as int,
        ) + seq![0x29u32],
        // "If this is the last part of the chain of the selector and there is a
        // pseudo-element, append "::" followed by the name of the pseudo-element".
        Simple::PseudoElement { element } => seq![0x3Au32, 0x3A] + pseudo_element_name(element),
    }
}

/// True for a universal selector that serializing a compound leaves out when it is not
/// alone: its prefix is not the null namespace (modelling choices).
pub open spec fn is_omitted_universal(s: Simple) -> bool {
    match s {
        Simple::Universal { ns } => ns != NsPrefix::NoNamespace,
        _ => false,
    }
}

/// Steps 1 and 2 of "serialize a selector" for one compound, over its first `k` simple
/// selectors: "Otherwise, for each simple selector in the compound selectors that is not a
/// universal selector of which the namespace prefix maps to a namespace that is not the
/// default namespace serialize the simple selector and append the result".
pub open spec fn compound_text(compound: Seq<Simple>, k: int) -> Seq<u32>
    decreases compound, k, 0int,
{
    if k <= 0 || k > compound.len() {
        Seq::empty()
    } else if is_omitted_universal(compound[k - 1]) {
        compound_text(compound, k - 1)
    } else {
        compound_text(compound, k - 1) + serialize_a_simple_selector(compound[k - 1])
    }
}

/// Steps 1 and 2 of "serialize a selector" for one compound selector.
pub open spec fn serialize_compound(compound: Seq<Simple>) -> Seq<u32>
    decreases compound, compound.len() + 1, 0int,
{
    // 1. "If there is only one simple selector in the compound selectors which is a universal
    // selector, append the result of serializing the universal selector."
    if compound.len() == 1 && compound[0] is Universal {
        serialize_a_simple_selector(compound[0])
    } else {
        compound_text(compound, compound.len() as int)
    }
}

/// Step 3: "a single SPACE (U+0020), followed by the combinator ">", "+", "~", … as
/// appropriate, followed by another single SPACE (U+0020) if the combinator was not
/// whitespace".
pub open spec fn combinator_text(combinator: Combinator) -> Seq<u32> {
    match combinator {
        Combinator::Descendant => seq![0x20u32],
        Combinator::Child => seq![0x20u32, 0x3E, 0x20],
        Combinator::NextSibling => seq![0x20u32, 0x2B, 0x20],
        Combinator::SubsequentSibling => seq![0x20u32, 0x7E, 0x20],
    }
}

/// CSSOM "serialize a selector", over the first `n` parts of the chain.
pub open spec fn serialize_chain(c: Complex, n: int) -> Seq<u32>
    decreases c, n, 0int,
{
    if n <= 0 || n > c.compounds.len() {
        Seq::empty()
    } else if n == 1 {
        serialize_compound(c.compounds[0])
    } else {
        let before = serialize_chain(c, n - 1);
        let joint = if n - 2 < c.combinators.len() {
            combinator_text(c.combinators[n - 2])
        } else {
            Seq::empty()
        };
        before + joint + serialize_compound(c.compounds[n - 1])
    }
}

/// CSSOM "serialize a selector".
pub open spec fn serialize_a_selector(c: Complex) -> Seq<u32> {
    serialize_chain(c, c.compounds.len() as int)
}

/// CSSOM "serialize a group of selectors", over the first `k`: "serialize each selector …
/// and then serialize a comma-separated list of these serializations", which joins them
/// with ", ".
pub open spec fn serialize_list(list: Seq<Complex>, k: int) -> Seq<u32>
    decreases list, k, 0int,
{
    if k <= 0 || k > list.len() {
        Seq::empty()
    } else if k == 1 {
        serialize_chain(list[0], list[0].compounds.len() as int)
    } else {
        serialize_list(list, k - 1) + seq![0x2Cu32, 0x20] + serialize_chain(
            list[k - 1],
            list[k - 1].compounds.len() as int,
        )
    }
}

/// CSSOM "serialize a group of selectors".
pub open spec fn serialize_a_group_of_selectors(list: Seq<Complex>) -> Seq<u32> {
    serialize_list(list, list.len() as int)
}

/// `skip_whitespace` stops at `hi`.
pub proof fn lemma_skip_whitespace_bounded(items: Seq<ComponentValue>, i: int, hi: int)
    requires
        i <= hi,
    ensures
        i <= skip_whitespace(items, i, hi) <= hi,
    decreases hi - i,
{
    if !(i < 0 || i >= hi || hi > items.len() || !is_whitespace_token(items[i])) {
        lemma_skip_whitespace_bounded(items, i + 1, hi);
    }
}

} // verus!
