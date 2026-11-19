//! Parsing, serialization, specificity and matching against Servo's `selectors` crate
//! (phase-5.md item 5.5): the engine Firefox and Servo match with, on every selector of
//! WPT's `css/selectors/parsing` (the vendored table, `tests/generated/`) and on generated
//! selectors, and, for the generated ones, on generated documents.
//!
//! Servo's engine is given what this crate leaves to its caller: a [`selectors::Element`]
//! over a `clazel-dom` arena ([`El`]), read through the arena's public readers; the
//! pseudo-classes and pseudo-elements of this crate's subset (`:link`, `:visited`,
//! `:any-link`, the user action pseudo-classes, the four pseudo-elements) as its
//! non-tree-structural ones; and no `@namespace` declarations, so no default namespace and no
//! declared prefix, as `src/spec.rs` models. Everything else, the grammar, `:nth-*`, `:is()`,
//! `:where()`, `:not()`, the combinators, specificity and serialization, is Servo's own.
//! What [`El`] decides is only what the Selectors text leaves to the host (what is an
//! element, whitespace in `:empty`, which arena node is the root, a hyperlink): it states each
//! in the code of its method.
//!
//! Each difference is listed in [`KNOWN`] with the reason it is not a bug in either engine,
//! and is excused only for the inputs that match its predicate; an unlisted difference fails
//! the test. Half of the generated selectors are "clean" (no pseudo-element, no mutation, so
//! no invalid item in a forgiving list) and for them nothing is excused. The matching of
//! every generated selector that both engines accept is compared on every element of
//! generated documents, with nothing excused.
//!
//! Skipped under Miri (`#[cfg_attr(miri, ignore)]`, as `clazel-cookie`'s differential test
//! is): Servo's `servo_arc` 0.4.3 (`Arc::from_header_and_iter_alloc`, lib.rs:809) writes
//! through a pointer whose tag comes from a zero-size retag, which Stacked Borrows reports as
//! undefined behaviour. The fault is in the reference engine, a test-only dependency, not in
//! this crate, which the other tests run under Miri.

use std::collections::BTreeMap;
use std::fmt;

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_selectors::exec_match::matches;
use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_serialize::serialize;
use clazel_selectors::exec_specificity::list_specificity_of;
use cssparser::{
    CowRcStr, Parser as CssParser, ParserInput, SourceLocation, ToCss, serialize_identifier,
};
use precomputed_hash::PrecomputedHash;
use selectors::attr::{AttrSelectorOperation, CaseSensitivity, NamespaceConstraint};
use selectors::bloom::BloomFilter;
use selectors::context::{
    MatchingContext, MatchingForInvalidation, MatchingMode, NeedsSelectorFlags, QuirksMode,
    SelectorCaches,
};
use selectors::matching::{ElementSelectorFlags, matches_selector_list};
use selectors::parser::{self, ParseRelative, SelectorImpl, SelectorList, SelectorParseErrorKind};
use selectors::{Element, OpaqueElement, Parser};

/// One check of a WPT page; the table is the one `tests/conformance_selectors.rs` runs.
struct Case {
    file: &'static str,
    line: usize,
    helper: &'static str,
    selector: &'static [u16],
    valid: bool,
    serialized: &'static [&'static [u16]],
}

include!("generated/wpt_css_selectors.rs");

// ------------------------------------------------------------------------------------
// Servo's side: the selector implementation of this crate's subset
// ------------------------------------------------------------------------------------

#[derive(Clone, Debug, Eq, PartialEq)]
enum PseudoClass {
    Link,
    Visited,
    AnyLink,
    Hover,
    Active,
    Focus,
    FocusVisible,
    FocusWithin,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum PseudoElement {
    Before,
    After,
    FirstLine,
    FirstLetter,
}

impl parser::PseudoElement for PseudoElement {
    type Impl = Impl;

    /// CSS Pseudo 4: the user action pseudo-classes may follow a pseudo-element, as this
    /// crate's grammar has it (src/spec.rs).
    fn accepts_state_pseudo_classes(&self) -> bool {
        true
    }

    fn is_before_or_after(&self) -> bool {
        matches!(self, PseudoElement::Before | PseudoElement::After)
    }
}

impl parser::NonTSPseudoClass for PseudoClass {
    type Impl = Impl;

    fn is_active_or_hover(&self) -> bool {
        matches!(self, PseudoClass::Active | PseudoClass::Hover)
    }

    fn is_user_action_state(&self) -> bool {
        !matches!(
            self,
            PseudoClass::Link | PseudoClass::Visited | PseudoClass::AnyLink
        )
    }
}

impl ToCss for PseudoClass {
    fn to_css<W: fmt::Write>(&self, dest: &mut W) -> fmt::Result {
        dest.write_str(match self {
            PseudoClass::Link => ":link",
            PseudoClass::Visited => ":visited",
            PseudoClass::AnyLink => ":any-link",
            PseudoClass::Hover => ":hover",
            PseudoClass::Active => ":active",
            PseudoClass::Focus => ":focus",
            PseudoClass::FocusVisible => ":focus-visible",
            PseudoClass::FocusWithin => ":focus-within",
        })
    }
}

impl ToCss for PseudoElement {
    fn to_css<W: fmt::Write>(&self, dest: &mut W) -> fmt::Result {
        dest.write_str(match self {
            PseudoElement::Before => "::before",
            PseudoElement::After => "::after",
            PseudoElement::FirstLine => "::first-line",
            PseudoElement::FirstLetter => "::first-letter",
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
struct Impl;

impl SelectorImpl for Impl {
    type ExtraMatchingData<'a> = std::marker::PhantomData<&'a ()>;
    type AttrValue = Value;
    type Identifier = Atom;
    type LocalName = Atom;
    type NamespaceUrl = Atom;
    type NamespacePrefix = Atom;
    type BorrowedLocalName = Atom;
    type BorrowedNamespaceUrl = Atom;
    type NonTSPseudoClass = PseudoClass;
    type PseudoElement = PseudoElement;
}

/// A string for every name and value; serialized as an identifier, or, as an attribute value,
/// as a string.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct Atom(String);

impl ToCss for Atom {
    fn to_css<W: fmt::Write>(&self, dest: &mut W) -> fmt::Result {
        serialize_identifier(&self.0, dest)
    }
}

impl From<String> for Atom {
    fn from(s: String) -> Self {
        Atom(s)
    }
}

impl<'a> From<&'a str> for Atom {
    fn from(s: &'a str) -> Self {
        Atom(s.into())
    }
}

impl PrecomputedHash for Atom {
    fn precomputed_hash(&self) -> u32 {
        self.0
            .bytes()
            .fold(17u32, |h, b| h.wrapping_mul(31).wrapping_add(u32::from(b)))
    }
}

/// Attribute values are serialized as strings, as CSSOM does.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct Value(String);

impl ToCss for Value {
    fn to_css<W: fmt::Write>(&self, dest: &mut W) -> fmt::Result {
        dest.write_char('"')?;
        {
            use std::fmt::Write;
            write!(cssparser::CssStringWriter::new(dest), "{}", self.0)?;
        }
        dest.write_char('"')
    }
}

impl AsRef<str> for Value {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl<'a> From<&'a str> for Value {
    fn from(s: &'a str) -> Self {
        Value(s.into())
    }
}

struct Ours;

impl<'i> Parser<'i> for Ours {
    type Impl = Impl;
    type Error = SelectorParseErrorKind<'i>;

    fn parse_is_and_where(&self) -> bool {
        true
    }

    fn parse_non_ts_pseudo_class(
        &self,
        location: SourceLocation,
        name: CowRcStr<'i>,
    ) -> Result<PseudoClass, cssparser::ParseError<'i, Self::Error>> {
        let class = match name.to_ascii_lowercase().as_str() {
            "link" => PseudoClass::Link,
            "visited" => PseudoClass::Visited,
            "any-link" => PseudoClass::AnyLink,
            "hover" => PseudoClass::Hover,
            "active" => PseudoClass::Active,
            "focus" => PseudoClass::Focus,
            "focus-visible" => PseudoClass::FocusVisible,
            "focus-within" => PseudoClass::FocusWithin,
            _ => {
                return Err(location.new_custom_error(
                    SelectorParseErrorKind::UnsupportedPseudoClassOrElement(name),
                ));
            }
        };
        Ok(class)
    }

    fn parse_pseudo_element(
        &self,
        location: SourceLocation,
        name: CowRcStr<'i>,
    ) -> Result<PseudoElement, cssparser::ParseError<'i, Self::Error>> {
        let element = match name.to_ascii_lowercase().as_str() {
            "before" => PseudoElement::Before,
            "after" => PseudoElement::After,
            "first-line" => PseudoElement::FirstLine,
            "first-letter" => PseudoElement::FirstLetter,
            _ => {
                return Err(location.new_custom_error(
                    SelectorParseErrorKind::UnsupportedPseudoClassOrElement(name),
                ));
            }
        };
        Ok(element)
    }
}

/// Servo's parse of `input`, as a list.
fn servo_parse(input: &str) -> Option<SelectorList<Impl>> {
    let mut parser_input = ParserInput::new(input);
    SelectorList::parse(
        &Ours,
        &mut CssParser::new(&mut parser_input),
        ParseRelative::No,
    )
    .ok()
}

// ------------------------------------------------------------------------------------
// Servo's side: an element of a `clazel-dom` arena
// ------------------------------------------------------------------------------------

/// An arena, and one reference per node for [`OpaqueElement`] to point at.
struct Doc {
    arena: Arena,
    ids: Vec<usize>,
}

#[derive(Clone)]
struct El<'a> {
    doc: &'a Doc,
    id: usize,
}

impl fmt::Debug for El<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "El({})", self.id)
    }
}

fn s(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn cps(x: &str) -> Vec<u32> {
    x.chars().map(u32::from).collect()
}

fn namespace_url(ns: &Option<Namespace>) -> &'static str {
    match ns {
        None => "",
        Some(Namespace::Html) => "http://www.w3.org/1999/xhtml",
        Some(Namespace::MathMl) => "http://www.w3.org/1998/Math/MathML",
        Some(Namespace::Svg) => "http://www.w3.org/2000/svg",
        Some(Namespace::XLink) => "http://www.w3.org/1999/xlink",
        Some(Namespace::Xml) => "http://www.w3.org/XML/1998/namespace",
        Some(Namespace::Xmlns) => "http://www.w3.org/2000/xmlns/",
    }
}

impl<'a> El<'a> {
    fn node(&self, id: usize) -> El<'a> {
        El { doc: self.doc, id }
    }

    fn is_element(&self, id: usize) -> bool {
        matches!(self.doc.arena.kind(id), ExecKind::Element { .. })
    }

    /// The name, namespace and attributes of this element.
    fn parts(&self) -> (&'a Vec<u32>, &'a Option<Namespace>, &'a Vec<ExecAttr>) {
        match self.doc.arena.kind(self.id) {
            ExecKind::Element {
                local_name,
                namespace,
                attributes,
                ..
            } => (local_name, namespace, attributes),
            _ => unreachable!("an element"),
        }
    }

    fn siblings(&self) -> &'a [usize] {
        match self.doc.arena.parent(self.id) {
            Some(p) => self.doc.arena.children(p),
            None => &[],
        }
    }

    fn first_attr(&self, name: &str) -> Option<String> {
        self.parts()
            .2
            .iter()
            .find(|a| a.namespace.is_none() && s(&a.local_name) == name)
            .map(|a| s(&a.value))
    }
}

impl Element for El<'_> {
    type Impl = Impl;

    fn opaque(&self) -> OpaqueElement {
        OpaqueElement::new(self.doc.ids.get(self.id).unwrap_or(&0))
    }

    fn parent_element(&self) -> Option<Self> {
        self.doc
            .arena
            .parent(self.id)
            .filter(|&p| self.is_element(p))
            .map(|p| self.node(p))
    }

    fn parent_node_is_shadow_root(&self) -> bool {
        false
    }

    fn containing_shadow_host(&self) -> Option<Self> {
        None
    }

    fn is_pseudo_element(&self) -> bool {
        false
    }

    fn prev_sibling_element(&self) -> Option<Self> {
        let sibs = self.siblings();
        let at = sibs.iter().position(|&x| x == self.id)?;
        sibs.iter()
            .take(at)
            .rev()
            .find(|&&x| self.is_element(x))
            .map(|&x| self.node(x))
    }

    fn next_sibling_element(&self) -> Option<Self> {
        let sibs = self.siblings();
        let at = sibs.iter().position(|&x| x == self.id)?;
        sibs.iter()
            .skip(at.saturating_add(1))
            .find(|&&x| self.is_element(x))
            .map(|&x| self.node(x))
    }

    fn first_element_child(&self) -> Option<Self> {
        self.doc
            .arena
            .children(self.id)
            .iter()
            .find(|&&x| self.is_element(x))
            .map(|&x| self.node(x))
    }

    fn is_html_element_in_html_document(&self) -> bool {
        // Every document is an HTML document (src/spec.rs), so this is the HTML namespace.
        matches!(self.parts().1, Some(Namespace::Html))
    }

    fn has_local_name(&self, local_name: &Atom) -> bool {
        s(self.parts().0) == local_name.0
    }

    fn has_namespace(&self, ns: &Atom) -> bool {
        namespace_url(self.parts().1) == ns.0
    }

    fn is_same_type(&self, other: &Self) -> bool {
        self.parts().0 == other.parts().0
            && namespace_url(self.parts().1) == namespace_url(other.parts().1)
    }

    fn attr_matches(
        &self,
        ns: &NamespaceConstraint<&Atom>,
        local_name: &Atom,
        operation: &AttrSelectorOperation<&Value>,
    ) -> bool {
        self.parts().2.iter().any(|a| {
            let ns_ok = match ns {
                NamespaceConstraint::Any => true,
                NamespaceConstraint::Specific(url) => namespace_url(&a.namespace) == url.0,
            };
            ns_ok && s(&a.local_name) == local_name.0 && operation.eval_str(&s(&a.value))
        })
    }

    fn match_non_ts_pseudo_class(
        &self,
        pc: &PseudoClass,
        _context: &mut MatchingContext<Impl>,
    ) -> bool {
        match pc {
            // HTML §4.16.3: a and area elements with an href attribute are links; no
            // history reaches a renderer, so none is visited (src/spec.rs).
            PseudoClass::Link | PseudoClass::AnyLink => self.is_link(),
            PseudoClass::Visited => false,
            // No pointer or focus in this phase.
            _ => false,
        }
    }

    fn match_pseudo_element(
        &self,
        _pe: &PseudoElement,
        _context: &mut MatchingContext<Impl>,
    ) -> bool {
        // A pseudo-element is not an element (src/spec.rs).
        false
    }

    fn apply_selector_flags(&self, _flags: ElementSelectorFlags) {}

    fn is_link(&self) -> bool {
        let (name, ns, _) = self.parts();
        matches!(ns, Some(Namespace::Html))
            && (s(name) == "a" || s(name) == "area")
            && self.first_attr("href").is_some()
    }

    fn is_html_slot_element(&self) -> bool {
        false
    }

    fn has_id(&self, id: &Atom, case_sensitivity: CaseSensitivity) -> bool {
        // The first attribute named `id` in no namespace (DOM "get an attribute by name").
        self.first_attr("id")
            .is_some_and(|v| case_sensitivity.eq(v.as_bytes(), id.0.as_bytes()))
    }

    fn has_class(&self, name: &Atom, case_sensitivity: CaseSensitivity) -> bool {
        self.first_attr("class").is_some_and(|v| {
            v.split([' ', '\t', '\n', '\x0C', '\r'])
                .any(|w| !w.is_empty() && case_sensitivity.eq(w.as_bytes(), name.0.as_bytes()))
        })
    }

    fn has_custom_state(&self, _name: &Atom) -> bool {
        false
    }

    fn imported_part(&self, _name: &Atom) -> Option<Atom> {
        None
    }

    fn is_part(&self, _name: &Atom) -> bool {
        false
    }

    fn is_empty(&self) -> bool {
        // Selectors 4 §15.1: no element children, and no text but white space.
        self.doc
            .arena
            .children(self.id)
            .iter()
            .all(|&c| match self.doc.arena.kind(c) {
                ExecKind::Element { .. } => false,
                ExecKind::Text { data } => data
                    .iter()
                    .all(|&u| matches!(u, 0x20 | 0x09 | 0x0A | 0x0D | 0x0C)),
                _ => true,
            })
    }

    fn is_root(&self) -> bool {
        // The element child of the document.
        self.doc
            .arena
            .parent(self.id)
            .is_some_and(|p| matches!(self.doc.arena.kind(p), ExecKind::Document { .. }))
    }

    fn add_element_unique_hashes(&self, _filter: &mut BloomFilter) -> bool {
        false
    }
}

/// Servo's answer for `list` against `el`.
fn servo_matches(list: &SelectorList<Impl>, el: &El, quirks: bool) -> bool {
    let mut caches = SelectorCaches::default();
    let mut context = MatchingContext::new(
        MatchingMode::Normal,
        None,
        &mut caches,
        if quirks {
            QuirksMode::Quirks
        } else {
            QuirksMode::NoQuirks
        },
        NeedsSelectorFlags::No,
        MatchingForInvalidation::No,
    );
    matches_selector_list(list, el, &mut context)
}

/// The greatest specificity of the list's selectors, as (A, B, C).
fn servo_specificity(list: &SelectorList<Impl>) -> (u32, u32, u32) {
    list.slice()
        .iter()
        .map(|sel| {
            let x = sel.specificity();
            ((x >> 20) & 0x3FF, (x >> 10) & 0x3FF, x & 0x3FF)
        })
        .max()
        .unwrap_or((0, 0, 0))
}

// ------------------------------------------------------------------------------------
// Differences
// ------------------------------------------------------------------------------------

/// What differs between the two engines on one selector.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Diff {
    /// We accept what Servo rejects.
    WeAccept,
    /// We reject what Servo accepts.
    WeReject,
    /// Both accept; the serializations differ.
    Serialization,
    /// Both accept; the specificities differ.
    Specificity,
    /// Both accept; the elements matched differ.
    Matching,
}

/// The differences known: a name, the kind, a predicate on the selector, and why it is not a
/// bug in either engine. Each applies only to the inputs its predicate selects; every one
/// was found by this test's first runs and checked by hand against the cited text.
type Known = (&'static str, Diff, fn(&str) -> bool, &'static str);

const USER_ACTION: &[&str] = &["hover", "active", "focus", "focus-visible", "focus-within"];

/// True if `selector` has `:is(` or `:where(`, the forgiving selector lists.
fn has_forgiving_list(selector: &str) -> bool {
    let lower = selector.to_ascii_lowercase();
    lower.contains(":is(") || lower.contains(":where(")
}

/// True if a pseudo-element is followed, in its compound selector, by a pseudo-class that
/// is not a user action pseudo-class.
fn pseudo_class_after_pseudo_element(selector: &str) -> bool {
    let lower = selector.to_ascii_lowercase();
    let mut from = 0;
    while let Some(at) = lower.get(from..).and_then(|rest| rest.find(':')) {
        let start = from.saturating_add(at);
        let rest = lower.get(start..).unwrap_or("");
        let body = rest.trim_start_matches(':');
        let name_end = body
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '-'))
            .unwrap_or(body.len());
        let name = &body[..name_end];
        if matches!(name, "before" | "after" | "first-line" | "first-letter") {
            // The rest of this compound selector.
            let compound = &body[name_end..];
            let compound = compound
                .split(|c: char| c.is_whitespace() || matches!(c, ',' | '>' | '+' | '~' | ')'))
                .next()
                .unwrap_or("");
            for part in compound.split(':').skip(1) {
                let n_end = part
                    .find(|c: char| !(c.is_ascii_alphanumeric() || c == '-'))
                    .unwrap_or(part.len());
                if !USER_ACTION.contains(&&part[..n_end]) {
                    return true;
                }
            }
        }
        from = start.saturating_add(1);
    }
    false
}

const KNOWN: &[Known] = &[
    (
        "forgiving-list-keeps-item-text",
        Diff::Serialization,
        has_forgiving_list,
        "§18.1's forgiving selector list drops an invalid or unsupported item, and src/spec.rs \
         serializes what was kept; Servo keeps the item's text as a never-matching one, which \
         CSSOM does not specify. The same selectors match the same elements (the match \
         comparison covers every generated one), and the specificities agree.",
    ),
    (
        "pseudo-class-after-pseudo-element",
        Diff::WeReject,
        pseudo_class_after_pseudo_element,
        "§18's note allows only the user action pseudo-classes after a pseudo-element, and \
         src/spec.rs rejects `::before:is(...)` and the like; Servo accepts any pseudo-class \
         there.",
    ),
    (
        "shadow-host",
        Diff::WeReject,
        |selector| selector.to_ascii_lowercase().contains(":host"),
        ":host() (shadow DOM) is not in the subset; Servo parses it as a pseudo-class.",
    ),
    (
        "unbalanced-bracket-in-forgiving-list",
        Diff::WeAccept,
        |selector| {
            has_forgiving_list(selector)
                && selector.matches('[').count() != selector.matches(']').count()
        },
        "A stray ] or an unclosed [ in the argument of :is()/:where(): CSS Syntax closes the \
         block at EOF or the end of the item and §18.1 drops the item, so src/spec.rs accepts \
         the selector (WPT's one case of this, `:is(# C4...`, is `Class::BadTokenInIs` of \
         tests/conformance_selectors.rs); Servo rejects the whole selector.",
    ),
];

fn excused(selector: &str, diff: &Diff) -> Option<&'static str> {
    KNOWN
        .iter()
        .find(|(_, d, applies, _)| d == diff && applies(selector))
        .map(|(name, ..)| *name)
}

/// Compare parsing, serialization and specificity of one selector.
fn compare_parse(selector: &str) -> Vec<Diff> {
    let ours = parse_selector(&cps(selector));
    let theirs = servo_parse(selector);
    match (ours, theirs) {
        (None, None) => Vec::new(),
        (Some(_), None) => {
            if std::env::var_os("CLAZEL_DIFF_VERBOSE").is_some() {
                println!("ACC {selector:?}");
            }
            vec![Diff::WeAccept]
        }
        (None, Some(_)) => {
            if std::env::var_os("CLAZEL_DIFF_VERBOSE").is_some() {
                println!("REJ {selector:?}");
            }
            vec![Diff::WeReject]
        }
        (Some(o), Some(t)) => {
            let mut diffs = Vec::new();
            if s(&serialize(&o)) != t.to_css_string() {
                diffs.push(Diff::Serialization);
                if std::env::var_os("CLAZEL_DIFF_VERBOSE").is_some() {
                    println!(
                        "SER {selector:?}\n  ours   {:?}\n  servo  {:?}",
                        s(&serialize(&o)),
                        t.to_css_string()
                    );
                }
            }
            let sp = list_specificity_of(&o, o.lists.len().saturating_sub(1));
            if (sp.a, sp.b, sp.c) != servo_specificity(&t) {
                diffs.push(Diff::Specificity);
            }
            diffs
        }
    }
}

/// A tally of one corpus.
#[derive(Default)]
struct Tally {
    total: usize,
    agree: usize,
    both_accept: usize,
    both_reject: usize,
    excused: BTreeMap<&'static str, usize>,
    unexplained: Vec<String>,
}

impl Tally {
    fn record(&mut self, selector: &str, diffs: Vec<Diff>, accepted: bool) {
        self.total = self.total.saturating_add(1);
        if diffs.is_empty() {
            self.agree = self.agree.saturating_add(1);
            if accepted {
                self.both_accept = self.both_accept.saturating_add(1);
            } else {
                self.both_reject = self.both_reject.saturating_add(1);
            }
            return;
        }
        let mut all_excused = true;
        for d in &diffs {
            match excused(selector, d) {
                Some(name) => {
                    let n = self.excused.entry(name).or_insert(0);
                    *n = n.saturating_add(1);
                }
                None => {
                    all_excused = false;
                    self.unexplained.push(format!("{selector:?}: {d:?}"));
                }
            }
        }
        let _ = all_excused;
    }
}

fn utf16(units: &[u16]) -> String {
    String::from_utf16_lossy(units)
}

#[test]
#[cfg_attr(miri, ignore = "servo_arc fails Stacked Borrows")]
fn wpt_parsing_against_servo() {
    let stride = if cfg!(miri) { 23 } else { 1 };
    let mut tally = Tally::default();
    for (k, case) in WPT.iter().enumerate() {
        if k % stride != 0 {
            continue;
        }
        let selector = utf16(case.selector);
        let diffs = compare_parse(&selector);
        let accepted = parse_selector(&cps(&selector)).is_some();
        // WPT's own verdict is the other tests' business (`conformance_selectors.rs`); here it
        // only labels a failure.
        let label = format!(
            "{}:{} ({}, WPT says {}, {} serializations)",
            case.file,
            case.line,
            case.helper,
            if case.valid { "valid" } else { "invalid" },
            case.serialized.len()
        );
        let before = tally.unexplained.len();
        tally.record(&selector, diffs, accepted);
        if let Some(last) = tally.unexplained.get_mut(before) {
            last.push_str(&format!(" at {label}"));
        }
    }
    // The one check the converter could not read is a direct test() through the DOM's matches().
    assert_eq!(NOT_RUN.len(), 1);
    println!(
        "clazel-conformance: suite=\"selectors differential, WPT inputs\" pass={} xfail={} fail={} total={}",
        tally.agree,
        tally.excused.values().sum::<usize>(),
        tally.unexplained.len(),
        tally.total
    );
    for (name, n) in &tally.excused {
        println!("  excused {name}: {n}");
    }
    assert!(
        tally.unexplained.is_empty(),
        "{}",
        tally.unexplained.join("\n")
    );
}

// ------------------------------------------------------------------------------------
// Generated selectors and documents
// ------------------------------------------------------------------------------------

/// xorshift64*, and whether to leave out what the engines serialize differently.
struct Rng(u64, bool);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        ((self.next() >> 33) as usize).checked_rem(n).unwrap_or(0)
    }

    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        items.get(self.below(items.len())).copied().unwrap_or("")
    }
}

const TYPES: &[&str] = &[
    "div", "p", "a", "span", "li", "ul", "area", "DIV", "A", "svg", "rect", "*", "html",
];
const NAMES: &[&str] = &["a", "b", "x", "main", "A", "B", "item", "red"];
const ATTRS: &[&str] = &[
    "id", "class", "href", "lang", "type", "data-x", "TYPE", "ID",
];
const VALUES: &[&str] = &[
    "a", "b", "x", "a b", "A", "", "/", "en", "en-US", "text", "TEXT", "item red",
];
const MATCHERS: &[&str] = &["=", "~=", "|=", "^=", "$=", "*="];
const NTH: &[&str] = &[
    "1", "2", "3", "odd", "even", "n", "2n", "2n+1", "-n+2", "n+2", "3n-1", "0", "-1", "+3",
    "0n+1", "-2n+5",
];
const SIMPLE_PSEUDO: &[&str] = &[
    ":first-child",
    ":last-child",
    ":only-child",
    ":first-of-type",
    ":last-of-type",
    ":only-of-type",
    ":empty",
    ":root",
    ":link",
    ":any-link",
    ":visited",
    ":hover",
    ":focus",
];
const NTH_FUNCTIONS: &[&str] = &[
    ":nth-child",
    ":nth-last-child",
    ":nth-of-type",
    ":nth-last-of-type",
];
const COMBINATORS: &[&str] = &[" ", " > ", " + ", " ~ ", ">", "+", "~"];

fn gen_simple(rng: &mut Rng, depth: usize) -> String {
    match rng.below(12) {
        0 | 1 => format!(".{}", rng.pick(NAMES)),
        2 => format!("#{}", rng.pick(NAMES)),
        3 => format!("[{}]", rng.pick(ATTRS)),
        4 | 5 => {
            let flag = rng.pick(&["", "", " i", " s", " I"]);
            let quote = rng.pick(&["\"", "'", ""]);
            let value = rng.pick(VALUES);
            // An unquoted value must be an identifier; an empty or odd one is the point, except
            // in the clean selectors, where it is quoted instead.
            let quote =
                if rng.1 && quote.is_empty() && (value.is_empty() || value.contains([' ', '/'])) {
                    "\""
                } else {
                    quote
                };
            format!(
                "[{}{}{q}{}{q}{}]",
                rng.pick(ATTRS),
                rng.pick(MATCHERS),
                value,
                flag,
                q = quote
            )
        }
        6 => rng.pick(SIMPLE_PSEUDO).to_string(),
        7 => format!("{}({})", rng.pick(NTH_FUNCTIONS), rng.pick(NTH)),
        8 | 9 if depth < 3 => {
            let f = rng.pick(&[":is", ":where", ":not", ":IS", ":Not"]);
            format!("{f}({})", gen_list(rng, depth.saturating_add(1)))
        }
        10 if !rng.1 => rng
            .pick(&[
                "::before",
                "::after",
                ":before",
                ":first-line",
                "::first-letter",
            ])
            .to_string(),
        _ => format!(".{}", rng.pick(NAMES)),
    }
}

fn gen_compound(rng: &mut Rng, depth: usize) -> String {
    let mut out = String::new();
    if rng.below(3) != 0 {
        out.push_str(rng.pick(TYPES));
    }
    let n = if out.is_empty() {
        1usize.saturating_add(rng.below(3))
    } else {
        rng.below(3)
    };
    for _ in 0..n {
        out.push_str(&gen_simple(rng, depth));
    }
    out
}

fn gen_complex(rng: &mut Rng, depth: usize) -> String {
    let mut out = gen_compound(rng, depth);
    for _ in 0..rng.below(3) {
        out.push_str(rng.pick(COMBINATORS));
        out.push_str(&gen_compound(rng, depth));
    }
    out
}

fn gen_list(rng: &mut Rng, depth: usize) -> String {
    let n = 1usize.saturating_add(rng.below(3));
    (0..n)
        .map(|_| gen_complex(rng, depth))
        .collect::<Vec<_>>()
        .join(rng.pick(&[", ", ",", " , "]))
}

/// Edit a selector in one place: the inputs a grammar-driven generator would not make.
fn mutate(rng: &mut Rng, selector: &str) -> String {
    let mut chars: Vec<char> = selector.chars().collect();
    if chars.is_empty() {
        return String::new();
    }
    let at = rng.below(chars.len());
    const EDITS: &[char] = &[
        '(', ')', '[', ']', ',', ' ', '>', '+', '~', '*', '|', '.', '#', ':', '"', '\\', '-', 'n',
        '1', '\u{e9}',
    ];
    match rng.below(3) {
        0 => {
            chars.remove(at);
        }
        1 => chars.insert(
            at,
            EDITS.get(rng.below(EDITS.len())).copied().unwrap_or('('),
        ),
        _ => {
            if let Some(slot) = chars.get_mut(at) {
                *slot = EDITS.get(rng.below(EDITS.len())).copied().unwrap_or(')');
            }
        }
    }
    chars.into_iter().collect()
}

fn element(arena: &mut Arena, ns: Namespace, name: &str, attrs: &[(String, String)]) -> usize {
    let id = arena
        .create(ExecKind::Element {
            namespace: Some(ns),
            prefix: None,
            local_name: cps(name),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        })
        .unwrap_or(0);
    for (n, v) in attrs {
        arena.append_attribute(
            id,
            ExecAttr {
                namespace: None,
                prefix: None,
                local_name: cps(n),
                value: cps(v),
            },
        );
    }
    id
}

/// A random document: `html` under the document node, and `count` more elements, text and
/// comments, attached at random places below it.
fn gen_doc(rng: &mut Rng, count: usize) -> (Doc, bool) {
    let mut arena = Arena::new(Vec::new());
    let quirks = rng.below(2) == 0;
    arena.set_mode(if quirks {
        DocumentMode::Quirks
    } else {
        DocumentMode::NoQuirks
    });
    let root = element(&mut arena, Namespace::Html, "html", &[]);
    arena.append(0, root);
    let mut nodes = vec![root];
    let mut parents = vec![root];
    for _ in 0..count {
        let parent = parents
            .get(rng.below(parents.len()))
            .copied()
            .unwrap_or(root);
        match rng.below(8) {
            0 => {
                let data = rng.pick(&["", " ", "  \n", "text", "\u{a0}"]);
                let t = arena
                    .create(ExecKind::Text { data: cps(data) })
                    .unwrap_or(0);
                arena.append(parent, t);
            }
            1 => {
                let c = arena
                    .create(ExecKind::Comment { data: cps("c") })
                    .unwrap_or(0);
                arena.append(parent, c);
            }
            _ => {
                let name = rng.pick(&[
                    "div", "p", "a", "span", "li", "ul", "area", "DIV", "svg", "rect",
                ]);
                let ns = if rng.below(6) == 0 {
                    Namespace::Svg
                } else {
                    Namespace::Html
                };
                let mut attrs: Vec<(String, String)> = Vec::new();
                for _ in 0..rng.below(4) {
                    attrs.push((
                        rng.pick(ATTRS).to_ascii_lowercase(),
                        rng.pick(VALUES).to_string(),
                    ));
                }
                if rng.below(4) == 0 {
                    attrs.push((rng.pick(ATTRS).to_string(), rng.pick(VALUES).to_string()));
                }
                let e = element(&mut arena, ns, name, &attrs);
                arena.append(parent, e);
                nodes.push(e);
                if rng.below(2) == 0 {
                    parents.push(e);
                }
            }
        }
    }
    let ids = (0..arena.len()).collect();
    (Doc { arena, ids }, quirks)
}

#[test]
#[cfg_attr(miri, ignore = "servo_arc fails Stacked Borrows")]
fn generated_selectors_against_servo() {
    let (n_selectors, n_docs) = if cfg!(miri) { (60, 2) } else { (6000, 8) };
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15, false);
    let docs: Vec<(Doc, bool)> = (0..n_docs).map(|_| gen_doc(&mut rng, 40)).collect();
    let mut parse = Tally::default();
    let mut matching = Tally::default();
    let mut compared_elements = 0usize;
    let mut matched_elements = 0usize;
    // Of the selectors, every other one is "clean": no pseudo-element, no mutation, so no
    // invalid item in a forgiving list. For these no difference is excused at all.
    let mut clean_total = 0usize;
    let mut clean_diffs: Vec<String> = Vec::new();
    for k in 0..n_selectors {
        let clean = k % 2 == 0;
        rng.1 = clean;
        let mut selector = gen_list(&mut rng, 0);
        if !clean && k % 4 == 3 {
            selector = mutate(&mut rng, &selector);
        }
        if clean {
            clean_total += 1;
            for d in compare_parse(&selector) {
                clean_diffs.push(format!("{selector:?}: {d:?}"));
            }
        }
        let ours = parse_selector(&cps(&selector));
        let theirs = servo_parse(&selector);
        let diffs = compare_parse(&selector);
        parse.record(&selector, diffs, ours.is_some());
        let (Some(o), Some(t)) = (ours, theirs) else {
            continue;
        };
        for (doc, quirks) in &docs {
            for id in 0..doc.arena.len() {
                if !matches!(doc.arena.kind(id), ExecKind::Element { .. }) {
                    continue;
                }
                let a = matches(&doc.arena, &o, id);
                let b = servo_matches(&t, &El { doc, id }, *quirks);
                compared_elements += 1;
                matched_elements += usize::from(a);
                let diffs = if a == b {
                    Vec::new()
                } else {
                    vec![Diff::Matching]
                };
                matching.record(&format!("{selector} on node {id}"), diffs, a);
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"selectors differential, generated selectors (parse, serialize, specificity)\" pass={} xfail={} fail={} total={}",
        parse.agree,
        parse.excused.values().sum::<usize>(),
        parse.unexplained.len(),
        parse.total
    );
    println!(
        "clazel-conformance: suite=\"selectors differential, generated documents (match)\" pass={} xfail={} fail={} total={}",
        matching.agree,
        matching.excused.values().sum::<usize>(),
        matching.unexplained.len(),
        matching.total
    );
    println!(
        "clazel-selectors: parsed by both {}, rejected by both {}; {} element checks, {} of them matches",
        parse.both_accept, parse.both_reject, compared_elements, matched_elements
    );
    println!(
        "clazel-selectors: of the generated selectors, {clean_total} had no pseudo-element and no \
         mutation, and none of them differs in parsing, serialization or specificity (nothing is \
         excused for them)"
    );
    for (name, n) in parse.excused.iter().chain(matching.excused.iter()) {
        println!("  excused {name}: {n}");
    }
    assert!(clean_diffs.is_empty(), "{}", clean_diffs.join("\n"));
    let mut unexplained = parse.unexplained;
    unexplained.extend(matching.unexplained);
    unexplained.truncate(60);
    assert!(unexplained.is_empty(), "{}", unexplained.join("\n"));
}
